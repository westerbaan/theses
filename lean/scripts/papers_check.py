#!/usr/bin/env python3
"""Check the follow-up papers' audit CSVs (docs/audit/papers-*.csv).

* every row has 6 or 7 fields (a literal `|` inside a field splits it);
* the stmt column is ok/weaker/stronger/differs and the proof column is
  faithful/route/mild/mathlib/none/sorry/tree;
* a 7th (status) field opens with a verdict word;
* every lean_name that looks like a single identifier is declared somewhere
  under Papers/ or Theses/ (PHANTOM otherwise);
* every DISP names a point of ../papers/<TAG>-points.csv.
Exit status 1 on any finding.
"""
import glob, os, re, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STMT = {'ok', 'weaker', 'stronger', 'differs'}
PROOF = {'faithful', 'route', 'mild', 'mathlib', 'none', 'sorry', 'tree'}
VERDICT = re.compile(r'^(row added|repaired|left-[a-z-]+|open)\b', re.I)
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|scoped\s+|local\s+)*(?:theorem|lemma|def|abbrev|instance(?:\s*\(priority\s*:=\s*\d+\))?|structure|class|inductive)\s+([A-Za-z_][\w'.₀-₉]*)")
names = set()
for d in ('Papers', 'Theses'):
    for p in glob.glob(os.path.join(ROOT, d, '**', '*.lean'), recursive=True):
        for l in open(p, encoding='utf-8'):
            m = DECL.match(l)
            if m:
                names.add(m.group(1)); names.add(m.group(1).split('.')[-1])
points = {}
for f in glob.glob(os.path.join(ROOT, '..', 'papers', '*-points.csv')):
    for l in list(open(f, encoding='utf-8'))[1:]:
        q = l.split('|')
        points.setdefault(q[0], set()).add(q[1])
bad = 0
for f in sorted(glob.glob(os.path.join(ROOT, 'docs', 'audit', 'papers-*.csv'))):
    rel = os.path.relpath(f, ROOT)
    for i, l in enumerate(open(f, encoding='utf-8').read().split('\n')[1:], 2):
        if not l.strip():
            continue
        q = l.split('|')
        def rep(kind, msg):
            global bad
            bad += 1
            print(f"{kind:9} {rel}:{i}  {msg}")
        if len(q) not in (6, 7):
            rep('SCHEMA', f'{len(q)} fields'); continue
        if q[3] not in STMT: rep('STMT', repr(q[3]))
        if q[4] not in PROOF: rep('PROOF', repr(q[4]))
        if len(q) == 7 and q[6].strip() and not VERDICT.match(q[6].strip()):
            rep('VERDICT', q[6].strip()[:50])
        tag, _, num = q[0].partition(' ')
        base = re.match(r'[0-9.]+', num)
        if tag in points and base and base.group(0).rstrip('.') not in points[tag]:
            rep('DISP', q[0])
        for n in [x.strip() for x in q[1].split(',')]:
            if re.fullmatch(r"[A-Za-z_][\w'.₀-₉]*", n) and n not in names and n.split('.')[-1] not in names:
                rep('PHANTOM', n)
print(f"papers audit: {bad} findings")
sys.exit(1 if bad else 0)
