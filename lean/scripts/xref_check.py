#!/usr/bin/env python3
"""Check that every `docs/FILE.md §N` reference names a section that exists.

The tree and the documents cite each other by section number — "see
`docs/DEAD-LIMBS.md` §10e", "§13.6's prefix-indexing fix" — and the documents
get renumbered.  Nothing has ever checked those references, and two of them in
`A/Proc/QuantumLambda.lean` point at `docs/DEAD-LIMBS.md` §5d, which does not
exist and did not when the pointer was written; the numbering it belongs to is
gone.

Only **qualified** references are read — `` `docs/DEAD-LIMBS.md` §10e `` — because
they say which document they mean.  A bare `§13.5` inside a document usually
means that document and sometimes does not: `COMMUTATION-THEOREM.md` cites
`DEAD-LIMBS.md`'s §12b, §13.5 and §10c bare, in prose that names the other file
a few words earlier.  Resolving those needs to read the sentence, which is the
same wall the bare .tex references hit (`cite_check.py --bare`), so they are
counted and not checked.

A section exists when some heading of the file opens with its number: `## 5.`,
`### 5.1`, `### 10a.`, `### 13.4`.  Sub-numbering is not invented — `§5` does
not stand in for `§5.1` — because a reader following `§5` lands on the section
and a reader following `§5d` lands nowhere.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
LEAN = ROOT / "Theses"

HEADING = re.compile(r'^#{1,4}\s+(\d+(?:\.\d+)?[a-z]?)\.?\s')
QUALIFIED = re.compile(r'`?docs/([A-Za-z-]+\.md)`?\s*§\s*(\d+(?:\.\d+)?[a-z]?)')
BARE = re.compile(r'§\s*(\d+(?:\.\d+)?[a-z]?)')


def anchors():
    out = {}
    for md in sorted(DOCS.glob("*.md")):
        out[md.name] = {m.group(1) for m in
                        (HEADING.match(l) for l in md.read_text().splitlines()) if m}
    return out


def main():
    have = anchors()
    bad, checked = [], 0

    def look(where, lineno, fname, sec):
        nonlocal checked
        if fname not in have:
            bad.append((where, lineno, fname, sec, "no such document"))
            return
        checked += 1
        if sec not in have[fname]:
            near = sorted(s for s in have[fname] if s.startswith(sec.rstrip("abcdefgh")))[:4]
            bad.append((where, lineno, fname, sec,
                        "nearest: " + ", ".join("§" + n for n in near) if near else "no near match"))

    for src in sorted(LEAN.rglob("*.lean")):
        if ".lake" in src.parts:
            continue
        rel = src.relative_to(ROOT)
        for i, line in enumerate(src.read_text(errors="replace").splitlines(), 1):
            for m in QUALIFIED.finditer(line):
                look(rel, i, m.group(1), m.group(2))

    unqualified = 0
    for md in sorted(DOCS.glob("*.md")):
        for i, line in enumerate(md.read_text().splitlines(), 1):
            spans = []
            for m in QUALIFIED.finditer(line):
                spans.append(m.span())
                look(md.relative_to(ROOT.parent), i, m.group(1), m.group(2))
            for m in BARE.finditer(line):
                if not any(a <= m.start() < b for a, b in spans):
                    unqualified += 1

    for where, lineno, fname, sec, why in bad:
        print(f"DANGLING {where}:{lineno}  {fname} §{sec} — {why}")
    print(f"\n{checked} qualified section cross-references resolved, {len(bad)} name "
          f"a section that is not there; {unqualified} bare §N references inside the "
          f"documents are counted and not checked")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
