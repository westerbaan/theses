#!/usr/bin/env python3
"""Repair the .tex line numbers in the tree's citations, by history, not by guess.

`scripts/cite_check.py` reports a citation as drifted when the cited line has
fallen outside the extent of the label it names.  Snapping every such citation
to the label's opening line would be wrong: 133 citations in the tree point
deliberately at an interior line -- a displayed equation, a numbered clause --
and their offset inside the point is the information they carry.

So the offset is recovered rather than discarded.  For each drifted citation the
.tex file's history is walked newest-first until a revision is found in which the
cited line *did* sit inside that label's extent.  The offset from that revision's
opening line is the offset the citation meant; the repaired line is today's
opening line plus that same offset.  A citation whose line was never inside the
extent, at any revision, is reported and left alone -- it is a different kind of
error and not one a shift can fix.

Run with --write to apply; without it, prints the repairs it would make.
"""

import re
import subprocess
import sys
import types
from pathlib import Path

HERE = Path(__file__).resolve()
ROOT = HERE.parents[2]

_mod_src = (HERE.parent / "cite_check.py").read_text().replace("sys.exit(main())", "pass")
cc = types.ModuleType("cc")
cc.__file__ = str(HERE.parent / "cite_check.py")
exec(compile(_mod_src, "cite_check", "exec"), cc.__dict__)


def revisions(tex):
    r = subprocess.run(["git", "log", "--format=%H", "--", tex],
                       cwd=ROOT, capture_output=True, text=True)
    return r.stdout.split()


_cache = {}


def extents_at(tex, rev):
    key = (tex, rev)
    if key not in _cache:
        r = subprocess.run(["git", "show", f"{rev}:{tex}"],
                           cwd=ROOT, capture_output=True, text=True)
        _cache[key] = cc.extents_from_text(r.stdout) if r.returncode == 0 else {}
    return _cache[key]


def disp_repair(write):
    """Repair the self-citation of a DISP-tagged doc comment, by history.

    Same rule as the labelled case, with the tag in place of the label: the
    tag decodes to a parsec and a point, and the question is whether the cited
    line is inside that point.  Where it is not, the .tex history says where
    the point used to open and how far into it the citation pointed.
    """
    # two readings of each file: the plain points, which anchor the offset, and
    # the same points widened over their proofs, which decide whether a citation
    # needs repairing at all (cite_check.with_proofs)
    plain_now = {tex.name: cc.points(tex.read_text(errors="replace"))
                 for tex in sorted(cc.ROOT.glob("*.tex"))}
    tables_now = {k: cc.with_proofs(v) for k, v in plain_now.items()}
    revs, cache = {}, {}
    fixed, stuck = [], []

    def table_at(tex, rev):
        if (tex, rev) not in cache:
            r = subprocess.run(["git", "show", f"{rev}:{tex}"], cwd=ROOT,
                               capture_output=True, text=True)
            pts = cc.points(r.stdout) if r.returncode == 0 else {}
            cache[(tex, rev)] = (pts, cc.with_proofs(pts))
        return cache[(tex, rev)]

    for src in sorted(cc.LEAN.rglob("*.lean")):
        if ".lake" in src.parts:
            continue
        rel = src.relative_to(ROOT)
        lines = src.read_text(errors="replace").splitlines(keepends=True)
        changed = False
        for i, line in enumerate(lines):
            m = cc.TAG.match(line)
            if not m:
                continue
            head = "".join(lines[i:i + 3])
            ref = cc.SELFREF.search(head)
            if not ref:
                continue
            tex, num = ref.group(1), int(ref.group(2))
            if tex in cc.NO_PARSECS:
                continue
            key = (str(int(m.group(1)) * 10 + (ord(m.group(2)) - 96 if m.group(2) else 0)),
                   str(cc.roman(m.group(3)) * 10))
            tag = f"{m.group(1)}{m.group(2)}{m.group(3)}"
            here = tables_now.get(tex, {}).get(key)
            anchor = plain_now.get(tex, {}).get(key)
            if here is None or here[0] <= num <= here[1]:
                continue
            if tex not in revs:
                revs[tex] = revisions(tex)
            for rev in revs[tex]:
                old_plain, old_wide = table_at(tex, rev)
                old = old_wide.get(key)
                if old and old[0] <= num <= old[1]:
                    offset = num - old_plain[key][0]
                    new = anchor[0] + offset
                    # the reference may be on any of the doc comment's first lines
                    for j in range(i, min(i + 3, len(lines))):
                        if f"{tex}:{num}" in lines[j]:
                            lines[j] = lines[j].replace(f"{tex}:{num}", f"{tex}:{new}", 1)
                            break
                    fixed.append((rel, i + 1, tag, tex, num, new, offset, rev[:7]))
                    changed = True
                    break
            else:
                stuck.append((rel, i + 1, tag, tex, num, here))
        if changed and write:
            src.write_text("".join(lines))

    for rel, ln, tag, tex, old, new, off, rev in fixed:
        print(f"{'FIXED ' if write else 'WOULD '} {rel}:{ln}  **{tag}** {tex}:{old} -> :{new}"
              f"  (offset +{off} inside the point, last correct at {rev})")
    for rel, ln, tag, tex, num, here in stuck:
        print(f"UNFIXED {rel}:{ln}  **{tag}** cites {tex}:{num}; no revision of {tex} "
              f"ever put that line inside the point the tag decodes to "
              f"(now {tex}:{here[0]}-{here[1]})")
    print(f"\n{len(fixed)} DISP self-citations repaired by history, {len(stuck)} left alone")
    return 0


def main():
    write = "--write" in sys.argv
    if "--disp" in sys.argv:
        return disp_repair(write)
    now = cc.extents()
    revs = {}
    repairs, orphans = [], []

    for src in sorted(cc.LEAN.rglob("*.lean")):
        if ".lake" in src.parts:
            continue
        rel = src.relative_to(ROOT)
        lines = src.read_text(errors="replace").splitlines(keepends=True)
        changed = False
        for idx, line in enumerate(lines):
            # a slash-pair citation (`a`/`b`, vn.tex:2362/2684) pairs its labels
            # with its lines in order; CITE would read the last label against the
            # first line, so those spans are held out of the substitution.
            masked = [m.span() for m in cc.PAIRED.finditer(line)]

            def fix(m):
                nonlocal changed
                if any(a <= m.start() < b for a, b in masked):
                    return m.group(0)
                lab, tex, num = m.group(1), m.group(2), int(m.group(3))
                spans = now.get(lab, {}).get(tex)
                if not spans or cc.contains(spans, num):
                    return m.group(0)
                if tex not in revs:
                    revs[tex] = revisions(tex)
                for rev in revs[tex]:
                    old = extents_at(tex, rev).get(lab)
                    if old and any(a <= num <= b for a, b in old):
                        offset = num - min(a for a, b in old)
                        new = min(a for a, b in spans) + offset
                        repairs.append((rel, idx + 1, lab, tex, num, new, offset, rev[:7]))
                        changed = True
                        return m.group(0).replace(f"{tex}:{num}", f"{tex}:{new}")
                orphans.append((rel, idx + 1, lab, tex, num, spans))
                return m.group(0)

            def fix_paren(m):
                # same repair for `label` (file.tex:N); skip the shape when the
                # name is not a label of that file, since it is then a Lean
                # identifier that happens to precede a reference
                if m.group(2) not in now.get(m.group(1), {}):
                    return m.group(0)
                return fix(m)

            lines[idx] = cc.PARENCITE.sub(fix_paren, cc.CITE.sub(fix, line))
        if changed and write:
            src.write_text("".join(lines))

    for rel, ln, lab, tex, old, new, off, rev in repairs:
        print(f"{'FIXED ' if write else 'WOULD '} {rel}:{ln}  `{lab}` {tex}:{old} -> :{new}"
              f"  (offset +{off} inside the point, last correct at {rev})")
    for rel, ln, lab, tex, num, spans in orphans:
        ext = ", ".join(f"{a}-{b}" for a, b in spans)
        print(f"UNFIXED {rel}:{ln}  `{lab}` cited at {tex}:{num}; no revision of {tex} "
              f"ever put that line inside `{lab}` (extent now {ext})")

    print(f"\n{len(repairs)} citations repaired by history, {len(orphans)} left alone "
          f"because no revision supports them")
    return 0


if __name__ == "__main__":
    sys.exit(main())
