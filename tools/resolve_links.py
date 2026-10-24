#!/usr/bin/env python3
"""Resolve direct Apple Music and YT Music links for every track in index.html.

Rewrites DATA entries as [artist, song, pos, apple_track_id, ytm_video_id]
(null where nothing trustworthy was found; the page falls back to DDG then)
and prints matches worth a manual look. Tracks listed in FIXES get the
corrected names appended, [..., search_song, search_artist?], which the page
uses for its search links while still showing the official spelling.

    pip install ytmusicapi
    python3 tools/resolve_links.py

Lookups are cached in the system temp dir, so reruns are cheap.
"""
import json
import os
import re
import sys
import tempfile
import threading
import time
import unicodedata
import urllib.parse
import urllib.request
from difflib import SequenceMatcher

from ytmusicapi import YTMusic

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
INDEX = os.path.join(ROOT, 'index.html')
CACHE_DIR = os.path.join(tempfile.gettempdir(), 'odsluchownia-links')
DATA_RE = re.compile(r'^const DATA = (.*);$', re.M)

# Words that mark an alternate take; penalised unless the listed title has them too.
ALT = {'live', 'demo', 'acoustic', 'remix', 'cover', 'tribute', 'rehearsal',
       'orchestral', 'symphonic', 'unplugged', 'reimagined'}
# Not worth linking at all.
REJECT = {'instrumental', 'karaoke'}
MIN_SIM = 0.85

# Typos and misnamings in the official list: (artist, song) -> (search artist, search song).
FIXES = {
    ('Armored Saint', 'Reign Of Fear'): ('Armored Saint', 'Reign of Fire'),
    ('Azarath', 'Beyond The Gates Of Burning Ghasts'): ('Azarath', 'Beyond the Gates of Burning Ghast'),
    ('Blindead', 'So, It Feels Like A Misunderstanding When…'): ('Blindead', 'So, It Feels Like Misunderstanding When'),
    ('Candlemass', "At The Gallow's End"): ('Candlemass', 'At the Gallows End'),
    ('Carcass', 'Corporeal Jigsore Quandary'): ('Carcass', 'Corporal Jigsore Quandary'),
    ('Celtic Frost', 'A Dying God Into The Human Flesh'): ('Celtic Frost', 'A Dying God Coming into Human Flesh'),
    ('Celtic Frost', 'Procreation Of The Wicked'): ('Celtic Frost', 'Procreation (Of the Wicked)'),
    ('Darkthrone', 'Nastassja In Eternal Sleep'): ('Darkthrone', 'Natassja in Eternal Sleep'),
    ('Girlschool & Motorhead', "Please Don't Touch"): ('Girlschool', "Please Don't Touch"),
    ('Grave', 'Souless'): ('Grave', 'Soulless'),
    ('Hypocrisy', 'Fractured Millenium'): ('Hypocrisy', 'Fractured Millennium'),
    ('Judas Priest', 'Turbo'): ('Judas Priest', 'Turbo Lover'),
    ('KAT', 'Diabelski dom (cz.2)'): ('KAT', 'Diabelski dom cz. II'),
    ('KAT', 'Purpupowe gody'): ('KAT', 'Purpurowe gody'),
    ('Kreator', 'When The Sun Turns Red'): ('Kreator', 'When the Sun Burns Red'),
    ('Marduk', 'Sulhpur Souls'): ('Marduk', 'Sulphur Souls'),
    ('Megadeth', "Peace Sells But Who's Buying"): ('Megadeth', 'Peace Sells'),
    ('Mercyful Fate', 'Curse Of The Pharohs'): ('Mercyful Fate', 'Curse of the Pharaohs'),
    ('Meshuggah', 'New Millenium Cyanide Christ'): ('Meshuggah', 'New Millennium Cyanide Christ'),
    ('Metal Church', 'Watch The Children Prey'): ('Metal Church', 'Watch the Children Pray'),
    ('Morowe', 'Tylko piekło, labrirynty i diabły'): ('Morowe', 'Tylko piekło, labirynty i diabły'),
    ('Motörhead', 'God Was Never On My Side'): ('Motörhead', 'God Was Never on Your Side'),
    ('Municipal Waste', "Headbanger's Face Rip"): ('Municipal Waste', 'Headbanger Face Rip'),
    ('Nevermore', 'Heart Collerctor'): ('Nevermore', 'The Heart Collector'),
    ('Pantera', 'Cemetary Gates'): ('Pantera', 'Cemetery Gates'),
    ('Sabaton', 'Forty To One (40:1)'): ('Sabaton', '40:1'),
    ('Shining (Nor)', 'The Madness And The Damage Done'): ('Shining', 'The Madness and the Damage Done'),
    ('Suicidal Tendencies', "Can't Bring Me Down"): ('Suicidal Tendencies', "You Can't Bring Me Down"),
    ('Testament', 'True Beliver'): ('Testament', 'True Believer'),
    ('Truchło Strzygi', 'Busola donikąd'): ('Truchło Strzygi', 'Busola do nikąd'),
    ('Type O Negative', 'Love Me To Death'): ('Type O Negative', 'Love You to Death'),
    ('Type O Negative', 'Wolfmoon'): ('Type O Negative', 'Wolf Moon'),
    ('Vader', 'The Crucifed Ones'): ('Vader', 'The Crucified Ones'),
    ('Van Halen', "Running' With The Devil"): ('Van Halen', "Runnin' with the Devil"),
    ('Venom', 'Lay Down Your Souls'): ('Venom', 'Lay Down Your Soul'),
    ('W.A.S.P.', 'Sleeping In The Fire'): ('W.A.S.P.', 'Sleeping (In the Fire)'),
    ('Wintersun', 'Beyond The Black Sun'): ('Wintersun', 'Beyond the Dark Sun'),
}
NUM_WORDS = {w: str(i) for i, w in enumerate(
    'zero one two three four five six seven eight nine ten eleven twelve'.split())}
NUM_WORDS.update(twenty='20', thirty='30', forty='40', fifty='50', hundred='100')
ROMAN = {'i': '1', 'ii': '2', 'iii': '3', 'iv': '4', 'v': '5', 'vi': '6', 'vii': '7', 'viii': '8'}
PART = {'cz', 'part', 'pt', 'vol', 'chapter'}


def norm(s):
    s = unicodedata.normalize('NFKD', s.replace('ł', 'l').replace('Ł', 'L'))
    s = ''.join(c for c in s if not unicodedata.combining(c)).lower().replace('&', ' and ')
    return ' '.join(re.sub(r'[^a-z0-9]+', ' ', s).split())


def tokens(s):
    """Normalised words with numbers unified: Five/5, cz. I/cz. 1, Futility V/Futility 5."""
    w = norm(s).split()
    out = []
    for i, t in enumerate(w):
        if t in NUM_WORDS:
            t = NUM_WORDS[t]
        elif t in ROMAN and (len(t) > 1 or i == len(w) - 1 or (i and w[i - 1] in PART)):
            t = ROMAN[t]
        elif t.isdigit():
            t = t.lstrip('0') or '0'
        out.append(t)
    return out


def core(s):
    """Comparable title: no bracketed or dash-suffixed extras, no leading article."""
    t = tokens(re.sub(r'\s*[(\[][^)\]]*[)\]]|\s+-\s+.*$', '', s)) or tokens(s)
    if len(t) > 1 and t[0] in ('the', 'a', 'an'):
        t = t[1:]
    return ' '.join(t)


def nums(s):
    return {t for t in tokens(s) if t.isdigit()}


def sim(a, b):
    return SequenceMatcher(None, a, b).ratio()


def artist_ok(want, names):
    w = norm(want)
    return any(w == n or w in n.split(' and ') or sim(w, n) >= 0.9 for n in map(norm, names))


def pick(artist, song, cands):
    """cands: (id, title, [artist names], album). Returns (score, id, flags, description) or None."""
    want = core(song)
    want_words = set(norm(song).split())
    want_nums = nums(song)
    best = None
    for i, (cid, title, artists, album) in enumerate(cands):
        if not cid or not artist_ok(artist, artists):
            continue
        s = sim(core(title), want)
        if s < MIN_SIM:
            continue
        # Part numbers must agree: Diabelski dom (cz.2) is not Diabelski Dom I.
        got_nums = nums(title)
        if want_nums and got_nums and not want_nums <= got_nums:
            continue
        words = set(norm(title + ' ' + (album or '')).split()) - want_words
        if words & REJECT:
            continue
        alt = words & ALT
        # Near misses are usually typos in the list; let the API's ranking pick among
        # them rather than whichever variant happens to be closest to the typo.
        score = (1.0 if s == 1 else 0.9) - 0.2 * len(alt) - 0.001 * i
        if best is None or score > best[0]:
            flags = ([f'title~{s:.2f}'] if s < 1 else []) + sorted(alt)
            best = (score, cid, flags, f'{"/".join(artists)} - {title} [{album}]')
    return best


def best_of(artist, song, searches):
    """Run searches lazily until one gives a clean match; keep the best seen."""
    best = None
    for tag, run in searches:
        hit = pick(artist, song, run())
        if hit and tag:
            hit = hit[:2] + (hit[2] + [tag],) + hit[3:]
        if hit and (best is None or hit[0] > best[0]):
            best = hit
        if best and not best[2]:
            break
    return best


class Cache:
    def __init__(self, name):
        os.makedirs(CACHE_DIR, exist_ok=True)
        self.path = os.path.join(CACHE_DIR, name + '.json')
        self.data = json.load(open(self.path)) if os.path.exists(self.path) else {}

    def get(self, key, fetch):
        if key not in self.data:
            self.data[key] = fetch()
            with open(self.path, 'w') as f:
                json.dump(self.data, f)
        return self.data[key]


def itunes(params, _last=[0.0]):
    # Apple throttles at roughly 20 requests/minute.
    time.sleep(max(0.0, _last[0] + 3.2 - time.time()))
    url = 'https://itunes.apple.com/search?' + urllib.parse.urlencode(
        {'country': 'pl', 'media': 'music', 'entity': 'song', **params})
    for attempt in range(5):
        _last[0] = time.time()
        try:
            with urllib.request.urlopen(url, timeout=30) as r:
                return [(x.get('trackId'), x.get('trackName', ''), [x.get('artistName', '')],
                         x.get('collectionName', '')) for x in json.load(r)['results']]
        except Exception as e:
            print(f'itunes retry {attempt + 1}: {e}', file=sys.stderr)
            time.sleep(30 * (attempt + 1))
    raise RuntimeError('iTunes search keeps failing')


def resolve_apple(rows, out):
    cache = Cache('apple')
    queries = [
        lambda a, s: {'term': f'{a} {s}', 'limit': 50},
        lambda a, s: {'term': s, 'attribute': 'songTerm', 'limit': 200},
        lambda a, s: {'term': a, 'attribute': 'artistTerm', 'limit': 200},
    ]
    def search(params):
        return lambda: cache.get(json.dumps(params, sort_keys=True), lambda: itunes(params))

    for n, (a, s) in enumerate(rows):
        hit = best_of(a, s, [(None, search(q(a, s))) for q in queries])
        if hit:
            out[(a, s)] = hit
        if n % 50 == 0:
            print(f'apple {n}/{len(rows)}', file=sys.stderr)


def resolve_ytm(rows, out):
    cache = Cache('ytm')
    yt = YTMusic(location='PL')

    def search(q, kind):
        time.sleep(0.5)
        res = yt.search(q, filter=kind, limit=20)
        return [(r.get('videoId'), r.get('title', ''), [x['name'] for x in r.get('artists') or []],
                 (r.get('album') or {}).get('name', '')) for r in res]

    for n, (a, s) in enumerate(rows):
        hit = best_of(a, s, [
            (None, lambda: cache.get(f'songs:{a} {s}', lambda: search(f'{a} {s}', 'songs'))),
            # Videos are often fan uploads or clips; always worth a look.
            ('video', lambda: cache.get(f'videos:{a} {s}', lambda: search(f'{a} {s}', 'videos'))),
        ])
        if hit:
            out[(a, s)] = hit
        if n % 100 == 0:
            print(f'ytm {n}/{len(rows)}', file=sys.stderr)


def main():
    html = open(INDEX, encoding='utf-8').read()
    data = json.loads(DATA_RE.search(html).group(1))
    listed = {(d[0], d[1]) for d in data}
    stale = [k for k in FIXES if k not in listed]
    if stale:
        sys.exit(f'FIXES entries not in DATA: {stale}')
    rows = [FIXES.get((d[0], d[1]), (d[0], d[1])) for d in data]

    apple, ytm = {}, {}
    workers = [threading.Thread(target=resolve_apple, args=(rows, apple)),
               threading.Thread(target=resolve_ytm, args=(rows, ytm))]
    for w in workers:
        w.start()
    for w in workers:
        w.join()

    for name, found in (('Apple', apple), ('YTM', ytm)):
        print(f'\n## {name}: {len(found)}/{len(rows)} resolved')
        for a, s in rows:
            if (a, s) not in found:
                print(f'  MISSING  {a} - {s}')
            elif found[(a, s)][2]:
                _, _, flags, got = found[(a, s)]
                print(f'  {",".join(flags):<22} {a} - {s}  =>  {got}')

    new = []
    for d, (a, s) in zip(data, rows):
        row = d[:3] + [apple.get((a, s), (0, None))[1], ytm.get((a, s), (0, None))[1]]
        if (a, s) != (d[0], d[1]):
            row += [s] + ([a] if a != d[0] else [])
        new.append(row)
    html = DATA_RE.sub(lambda _: 'const DATA = ' + json.dumps(new, ensure_ascii=False) + ';', html, 1)
    open(INDEX, 'w', encoding='utf-8').write(html)


if __name__ == '__main__':
    main()
