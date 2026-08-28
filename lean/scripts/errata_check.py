#!/usr/bin/env python3
"""Check `ERRATA.md` against the tree, the sources, and its own stated rules.

`ERRATA.md` opens with three rules about itself:

* "**Everything here is open** -- not yet acted on by an author."
* "Items are **removed** once they are accounted for ... Do not add a `DONE`
  row -- delete the row instead."
* "Locate by **point number**, never by line."

Nothing checked any of them, and nothing checked that a row's point number
exists or that the citations pointing *at* the file hit a row that is there.
This does all four:

The first three are exact.  **PHANTOM is a shortlist**, for the reason the bare
`.tex` references hit in `cite_check.py`: a citation of a *removed* row is not a
defect -- `A/CStar/TowardsVN.lean:1866` says so in as many words, "the ERRATA.md
row was removed with the fix" -- and a DISP near the file name is sometimes the
*point a row is about* rather than the row's key, as at `152XII`, whose defect
is about `42I`.  Read the hits; do not expect zero.

1. **STATUS**  -- a row whose status is not `OPEN`, against the file's own rule.
2. **PHANTOM** -- a DISP cited as an `ERRATA.md` row from the Lean tree or from
   an audit CSV, with no such row in the file.
3. **NOPOINT** -- a row whose DISP does not decode to a point the sources have.
4. **DUP**     -- two rows with the same DISP *and* the same defect, which the
   file's ordering rule would not produce.

The DISP decoding is `cite_check.py`'s, so a tag of any shape it knows -- the
sub-parsec letter, the sub-point letter, a `.k` clause -- is read the same way
here.  Parsec ranges are disjoint across the five source files, so the tag alone
fixes the file.
"""

import pathlib
import re
import sys
import types

HERE = pathlib.Path(__file__).resolve()
ROOT = HERE.parents[2]
LEAN = HERE.parents[1]

_src = (HERE.parent / "cite_check.py").read_text().replace("sys.exit(main())", "pass")
cc = types.ModuleType("cc")
cc.__file__ = str(HERE.parent / "cite_check.py")
exec(compile(_src, "cite_check", "exec"), cc.__dict__)

# The clause may sit inside the bold or outside it -- `**101VII.1**` and
# `**14VIII**.3` are both in use, and a reader of one form would not guess the
# other.  Reading only the second missed 101VII entirely and reported the audit
# rows that cite it as phantoms.
ROW = re.compile(r'^\|\s*\*\*(\d{1,3}[a-z]?[IVXL]+[a-z]?)(\.[0-9a-z]+)?'
                 r'(?:\s*[-–—]+\s*(\d{1,3}[a-z]?[IVXL]+[a-z]?))?\*\*(\.[0-9a-z]+)?')
# A citation of the file, from anywhere: "ERRATA.md as 101VII.1", "ERRATA.md row
# 148IV", "ERRATA.md:117 (228III-228VI)".  Every DISP in the window counts, not
# just the first: "the proof of 49II is unaffected ... filed as the second 49III
# row in ERRATA.md" names 49III, and reading only the nearest token reported the
# row as missing because it read 49II.
CITE = re.compile(r'ERRATA\.md')
NEARBY = re.compile(r'\b(\d{1,3}[a-z]?[IVXL]+[a-z]?)(\.[0-9a-z]+)?\b')
SPLIT = re.compile(r'^(\d{1,3})([a-z]?)([IVXL]+)([a-z]?)$')


def rows():
    """(disp, clause, status, line number) for every table row of ERRATA.md."""
    out = []
    for i, line in enumerate((LEAN / "ERRATA.md").read_text().splitlines(), 1):
        m = ROW.match(line)
        if not m:
            continue
        cells = [c.strip() for c in line.split("|")]
        status = cells[-2] if len(cells) >= 3 else ""
        clause = (m.group(2) or m.group(4) or "").lstrip(".")
        out.append((m.group(1), clause, status, i, line))
        if m.group(3):                    # `**228III--228VI**` covers both ends
            out.append((m.group(3), "", status, i, line))
    return out


def main():
    table = rows()
    have = {d for d, _c, _s, _l, _t in table}
    bad_status, nopoint, phantom, dup = [], [], [], []

    points = {tex.name: cc.points(tex.read_text(errors="replace"))
              for tex in sorted(ROOT.glob("*.tex"))}

    for disp, clause, status, ln, text in table:
        # `OPEN (nit)`, `OPEN (informational)`, `OPEN (ruling pending, A12)` are
        # all open; the file's rule is about a row that has been ACTED on.
        if not status.upper().startswith("OPEN"):
            bad_status.append((ln, disp, status))
        m = SPLIT.match(disp)
        if not m:
            nopoint.append((ln, disp, "does not parse as a DISP"))
            continue
        key = cc.decode(m.group(1), m.group(2), m.group(3), m.group(4))
        if not any(key[:2] in tbl for tbl in points.values()):
            nopoint.append((ln, disp, f"decodes to parsec {{{key[0]}}} point {{{key[1]}}}, "
                                      f"which no source file has"))

    seen = {}
    for disp, clause, _s, ln, text in table:
        body = text.split("|")[2][:80] if len(text.split("|")) > 2 else ""
        k = (disp, clause, body)
        if k in seen:
            dup.append((ln, disp, seen[k]))
        seen[k] = ln

    targets = list(LEAN.rglob("Theses/**/*.lean")) + list((LEAN / "docs" / "audit").glob("*.csv"))
    for path in sorted(targets):
        if ".lake" in path.parts:
            continue
        rel = path.relative_to(ROOT)
        for i, line in enumerate(path.read_text(errors="replace").splitlines(), 1):
            for m in CITE.finditer(line):
                window = line[max(0, m.start() - 45):m.end() + 45]
                named = [x.group(1) for x in NEARBY.finditer(window)]
                if not named or any(n in have for n in named):
                    continue
                key = (rel, i, ", ".join(dict.fromkeys(named))[:60])
                if key not in phantom:
                    phantom.append(key)

    for ln, disp, status in bad_status:
        print(f"STATUS   ERRATA.md:{ln}  {disp} is `{status}`, not OPEN -- the file's own "
              f"rule is to delete a row rather than mark it done")
    for ln, disp, why in nopoint:
        print(f"NOPOINT  ERRATA.md:{ln}  {disp} {why}")
    for rel, i, disp in phantom:
        print(f"PHANTOM  {rel}:{i}  cites ERRATA.md {disp}; the file has no such row")
    for ln, disp, first in dup:
        print(f"DUP      ERRATA.md:{ln}  {disp} repeats the row at :{first}")

    print(f"\n{len(table)} errata rows (range rows counted at both ends): {len(bad_status)} not OPEN, {len(nopoint)} whose point "
          f"the sources do not have, {len(dup)} duplicated; {len(phantom)} citations name a row "
          f"that is not there")
    return 1 if (bad_status or nopoint or phantom or dup) else 0


if __name__ == "__main__":
    sys.exit(main())
