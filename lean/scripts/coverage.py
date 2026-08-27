#!/usr/bin/env python3
"""Which points of the theses have no audit row at all?

The audit records what was formalized.  It cannot say what was never started:
a point nobody transcribed has no row, so it is invisible to every count taken
off the CSVs.  This enumerates the points in the sources and subtracts.

DISP decoding, per docs/STATEMENT-AUDIT.md:
  parsec {N0}  -> N          parsec {N1} -> Na, {N2} -> Nb, ...
  point  {R0}  -> roman(R)
so `\\begin{parsec}{1254}` + `\\begin{point}{30}` is 125dIII.

Points that are not claims -- Proof, Remark, Warning, Notation, Convention,
Example, Intermezzo -- are counted separately: they are not things to
formalize, and lumping them in would understate coverage.

Usage:  python3 scripts/coverage.py [--list CHAPTER] [--kind KIND]
"""
import re, sys, os, glob, collections

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.dirname(ROOT)

CHAPTERS = {'cstar.tex': 'A/CStar', 'vn.tex': 'A/VN', 'proc.tex': 'A/Proc',
            'dils.tex': 'B/Dils', 'eff.tex': 'B/Eff'}

# Kinds that unambiguously assert something to formalize.  A whitelist, not a
# blacklist: most points are narrative, and guessing the other way inflates the
# gap enormously -- a first cut that counted every non-prose point as a claim
# reported 62.8% coverage where the real figure is 97%.
CLAIM = {'Definition', 'Proposition', 'Theorem', 'Lemma', 'Corollary',
         'Exercise', 'Exercise*', 'Fact', 'Claim'}

# Kinds that sometimes assert and sometimes illustrate.  Reported separately:
# folding them into CLAIM because most of them happen to be audited would be
# circular -- the denominator must not be chosen to flatter the numerator.
MIXED = {'Example', 'Examples', 'Notation'}

PARSEC = re.compile(r'\\begin\{parsec\}\{(\d+)\}')
# the kind is the first BRACE group after the number -- an optional [label]
# may sit between them, and either may be absent
POINT = re.compile(r'\\begin\{point\}\{(\d+)\}(?:\[[^\]]*\])?(?:\{([^}{]*)\})?')

ROMAN = [(1000,'M'),(900,'CM'),(500,'D'),(400,'CD'),(100,'C'),(90,'XC'),
         (50,'L'),(40,'XL'),(10,'X'),(9,'IX'),(5,'V'),(4,'IV'),(1,'I')]


def roman(n):
    out = ''
    for v, s in ROMAN:
        while n >= v:
            out += s; n -= v
    return out


def disp_of(parsec, point):
    d = parsec % 10
    n = parsec // 10
    letter = '' if d == 0 else chr(ord('a') + d - 1)
    return f'{n}{letter}{roman(point // 10)}'


def points():
    """(chapter, disp, kind, line) for every point in the five chapters."""
    for fname, chapter in CHAPTERS.items():
        path = os.path.join(SRC, fname)
        if not os.path.exists(path):
            continue
        cur = None
        for i, ln in enumerate(open(path, encoding='utf-8'), 1):
            m = PARSEC.search(ln)
            if m:
                cur = int(m.group(1)); continue
            m = POINT.search(ln)
            if m and cur is not None:
                pt = int(m.group(1))
                if pt % 10:          # {15} etc -- not a top-level point
                    continue
                kind = (m.group(2) or '').strip()
                yield chapter, disp_of(cur, pt), kind, f'{fname}:{i}'


def audited():
    seen = set()
    for p in glob.glob(os.path.join(ROOT, 'docs', 'audit', '*.csv')):
        for ln in open(p, encoding='utf-8'):
            f = ln.split('|')
            if len(f) > 5 and f[0] and f[0] != 'DISP':
                seen.add(f[0].split('.')[0])   # clause suffix -> its point
    return seen


def main():
    have = audited()
    rows = list(points())
    by = collections.defaultdict(lambda: [0, 0, 0, 0])   # claim, miss, mixed, mixed-miss
    missing, mixed_missing = [], []
    for chapter, disp, kind, loc in rows:
        got = disp in have
        b = by[chapter]
        if kind in CLAIM:
            b[0] += 1
            if not got:
                b[1] += 1
                missing.append((chapter, disp, kind, loc))
        elif kind in MIXED:
            b[2] += 1
            if not got:
                b[3] += 1
                mixed_missing.append((chapter, disp, kind, loc))

    if '--list' in sys.argv:
        want = sys.argv[sys.argv.index('--list') + 1]
        for c, d, k, loc in (missing + mixed_missing):
            if c.startswith(want) or want == 'all':
                print(f'  {c:9} {d:10} {k:16} {loc}')
        print(f'  -- {sum(1 for m in (missing+mixed_missing) if m[0].startswith(want) or want=="all")} unaudited')
        return 0

    print(f'{len(rows)} points in the five chapters; {sum(b[0] for b in by.values())} '
          f'are Definition/Proposition/Theorem/Lemma/Corollary/Exercise.\n')
    print(f'  {"chapter":10} {"claims":>7} {"no row":>7} {"cov":>6}     '
          f'{"mixed":>6} {"no row":>7}')
    tc = tm = xc = xm = 0
    for c in sorted(by):
        claim, miss, mixed, mmiss = by[c]
        tc += claim; tm += miss; xc += mixed; xm += mmiss
        pct = 100 * (claim - miss) / claim if claim else 100
        print(f'  {c:10} {claim:7} {miss:7} {pct:5.1f}%     {mixed:6} {mmiss:7}')
    print(f'  {"TOTAL":10} {tc:7} {tm:7} {100*(tc-tm)/tc:5.1f}%     {xc:6} {xm:7}')
    print(f'\n  "mixed" = Example/Examples/Notation, which sometimes assert and\n'
          f'  sometimes illustrate; counted apart so the denominator is not chosen\n'
          f'  to flatter the numerator.  Proof, Remark and unlabelled narrative\n'
          f'  points are excluded entirely ({100*6/314:.0f}%, {100*2/49:.0f}% and '
          f'{100*40/379:.0f}% of them carry a row).')
    print(f'\n`--list <chapter>|all` names the unaudited claims.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
