#!/usr/bin/env python3
"""Exact cross-checks between the audit CSVs and the tree.

Two checks, both set comparisons -- no reading of prose.  The general check
(testing a recorded *reason* against the tree) was tried twice and abandoned:
"rests on" means both `depends on` and `is blocked by`, and nothing in the
text distinguishes them.  These two do not need to read anything.

1. SORRY CLASS

An audit row classed `sorry` asserts that its declaration is not carried by a
proof.  That goes stale silently: when a declaration gets proved, the row
keeps saying `sorry` until someone notices.  In August 2026 seven of eighteen
such rows were stale at once -- every Kornell statement had been proved and
none of the rows updated -- and stale rows are what reasons elsewhere then
cite ("blocked on 125IV") long after the block is gone.

  ORPHANED   row says `sorry`, the declaration is proved  -> the row is stale
  UNRECORDED declaration is `sorry`, no row says so       -> the audit is blind

2. PHANTOM ROWS

A row naming a declaration that no longer exists.  Proof repairs delete the
machinery they replace, and the rows survive them -- inflating every count
taken off the audit.  Thirteen were found this way on 2026-08-26, seven left
by one repair and two by a deletion committed minutes earlier in the same
session.  A phantom row is only safe to delete once its thesis point still has
live coverage, so the check prints the point's surviving rows and leaves the
judgement to a person.

Namespaces matter here: a declaration inside `namespace Foo` is `Foo.bar` in
the audit.  Ignoring that reports 26 phantoms where there are 6.

Run `Theses/AxiomCheck.lean` for the authoritative sorry list; this reads the
source, which agrees with it and is far cheaper.

Usage:  python3 scripts/audit_check.py
Exits 1 on any discrepancy.
"""
import re, sys, glob, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|'
    r'unsafe\s+|scoped\s+)*'
    r'(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+'
    r'([^\s(){}\[\]:,]+)')

# `sorry` as code: not inside backticks, not after a comment marker.
SORRY = re.compile(r'(^|[\s(\[:=>,])sorry(\s|$|[)\],;])')


NS_OPEN = re.compile(r'^\s*namespace\s+(\S+)')
NS_END = re.compile(r'^\s*end\s+(\S+)\s*$')


def tree_declarations():
    """Every declaration name under Theses/, qualified by every enclosing
    namespace suffix -- the audit may name it at any depth."""
    names = set()
    for path in glob.glob(os.path.join(ROOT, 'Theses', '**', '*.lean'),
                          recursive=True):
        stack = []
        for ln in open(path, encoding='utf-8'):
            m = NS_OPEN.match(ln)
            if m:
                stack.extend(m.group(1).split('.'))
                continue
            m = NS_END.match(ln)
            if m:
                parts = m.group(1).split('.')
                if stack[-len(parts):] == parts:
                    del stack[-len(parts):]
                continue
            m = DECL.match(ln)
            if m:
                n = m.group(1)
                names.add(n)
                for i in range(len(stack)):
                    names.add('.'.join(stack[i:] + [n]))
    return names


def tree_sorries():
    out = {}
    for path in glob.glob(os.path.join(ROOT, 'Theses', '**', '*.lean'),
                          recursive=True):
        rel = os.path.relpath(path, ROOT)
        cur = None
        for ln in open(path, encoding='utf-8'):
            m = DECL.match(ln)
            if m:
                cur = m.group(1)
                continue
            if cur and '`' not in ln:
                code = ln.split('--')[0]
                if SORRY.search(code):
                    out[cur] = rel
    return out


def audit_rows():
    for path in sorted(glob.glob(os.path.join(ROOT, 'docs', 'audit', '*.csv'))):
        for i, line in enumerate(open(path, encoding='utf-8'), 1):
            f = line.rstrip('\n').split('|')
            if len(f) > 5 and f[1] and f[1] != 'lean_name':
                yield os.path.basename(path), i, f


def main():
    tree = tree_sorries()
    rows = list(audit_rows())
    recorded = {f[1]: (fn, i, f[0]) for fn, i, f in rows if f[4] == 'sorry'}

    orphaned = {k: v for k, v in recorded.items() if k not in tree}
    unrecorded = {k: v for k, v in tree.items() if k not in recorded}

    for name, (fname, lineno, disp) in sorted(orphaned.items()):
        print(f'ORPHANED   {fname}:{lineno}  {disp}  {name}')
        print(f'           row says `sorry`; the tree has a proof')
    for name, rel in sorted(unrecorded.items()):
        print(f'UNRECORDED {rel}  {name}')
        print(f'           declaration is `sorry`; no audit row records it')

    # Phantom rows.
    names = tree_declarations()
    by_point = {}
    for _, _, f in rows:
        by_point.setdefault(f[0], []).append(f)
    phantom = [(fn, i, f) for fn, i, f in rows
               if ' ' not in f[1] and f[1] not in names]
    for fn, i, f in phantom:
        print(f'PHANTOM    {fn}:{i}  {f[0]}  {f[1]}  (proof={f[4]})')
        live = [g for g in by_point[f[0]]
                if g[1] != f[1] and ' ' not in g[1] and g[1] in names]
        if live:
            print(f'           {f[0]} still covered by: '
                  + ', '.join(f'{g[1]} ({g[4]})' for g in live))
        else:
            print(f'           {f[0]} HAS NO OTHER LIVE ROW -- coverage lost')

    print(f'\n{len(tree)} sorries in the tree, {len(recorded)} rows classed '
          f'`sorry`; {len(orphaned)} orphaned, {len(unrecorded)} unrecorded, '
          f'{len(phantom)} phantom')
    return 1 if (orphaned or unrecorded or phantom) else 0


if __name__ == '__main__':
    sys.exit(main())
