#!/usr/bin/env python3
"""Cross-check the audit's `sorry` proof-class against the tree's real sorries.

An audit row classed `sorry` asserts that its declaration is not carried by a
proof.  That assertion goes stale silently: when a declaration gets proved,
the row keeps saying `sorry` until someone notices.  In August 2026 seven of
eighteen such rows were stale at once -- every Kornell statement had been
proved and none of the rows had been updated -- and stale rows are what
reasons elsewhere then cite ("blocked on 125IV") long after the block is gone.

This is an exact set comparison, not a reading of prose:

  ORPHANED   row says `sorry`, the declaration is proved  -> the row is stale
  UNRECORDED declaration is `sorry`, no row says so       -> the audit is blind

Run `Theses/AxiomCheck.lean` for the authoritative sorry list; this reads the
source, which agrees with it and is far cheaper.

Usage:  python3 scripts/sorry_class_check.py
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


def main():
    tree = tree_sorries()
    recorded = {}
    for path in sorted(glob.glob(os.path.join(ROOT, 'docs', 'audit', '*.csv'))):
        for i, line in enumerate(open(path, encoding='utf-8'), 1):
            f = line.rstrip('\n').split('|')
            if len(f) > 4 and f[4] == 'sorry':
                recorded[f[1]] = (os.path.basename(path), i, f[0])

    orphaned = {k: v for k, v in recorded.items() if k not in tree}
    unrecorded = {k: v for k, v in tree.items() if k not in recorded}

    for name, (fname, lineno, disp) in sorted(orphaned.items()):
        print(f'ORPHANED   {fname}:{lineno}  {disp}  {name}')
        print(f'           row says `sorry`; the tree has a proof')
    for name, rel in sorted(unrecorded.items()):
        print(f'UNRECORDED {rel}  {name}')
        print(f'           declaration is `sorry`; no audit row records it')

    print(f'\n{len(tree)} sorries in the tree, {len(recorded)} rows classed '
          f'`sorry`; {len(orphaned)} orphaned, {len(unrecorded)} unrecorded')
    return 1 if (orphaned or unrecorded) else 0


if __name__ == '__main__':
    sys.exit(main())
