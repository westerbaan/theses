#!/usr/bin/env python3
"""Check `name` (`File.lean:N`) references against where the declaration is.

The tree and the audit rows locate their own declarations by line -- "`ncp_ceil`
(`A/VN/Projections.lean:2829`)" -- 761 times, and nothing checks them.  They
drift exactly as the `.tex` line references did, which `cite_check.py` found
41% stale; a reference into our own source has no `\\label` to fall back on, so
the pointer is all there is.

Only the **named** form is checked: a declaration name in backticks immediately
before the reference.  A bare `File.lean:N` says nothing about what it points
at, and guessing would report the careful references as errors -- the same wall
`cite_check.py --bare` hit on the .tex side.  Those are counted, not checked.

A reference is accepted when the declaration is within `SLACK` lines of the
number, because the convention is inconsistent: some point at the `theorem`
line, some at the doc comment that opens above it, and a long doc comment is
twenty lines.  What that cannot absorb is a declaration that has moved a
hundred lines, which is the failure mode worth finding.

`--write` repairs them, and needs no history to do it: the **name** identifies
the target, so today's line is the answer.  That is what separates this from the
bare `.tex` references, where nothing says what the number was pointing at and a
history walk proposed 42 repairs of which the first two read were wrong.  A
reference whose name is declared in two places is left alone and reported.
"""

import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent
ROOT = LEAN.parent

SLACK = 30

# `foo_bar` (`A/Proc/Tensor.lean:1107`)   /  `foo_bar` (Tensor.lean:1107)
NAMED = re.compile(r'`([A-Za-z_][A-Za-z0-9_.\']*)`[^`\n]{0,24}?'
                   r'`?([A-Za-z][A-Za-z0-9_/]*\.lean):(\d+)`?')
ANY = re.compile(r'\b([A-Za-z][A-Za-z0-9_/]*\.lean):(\d+)')
USE_SITE = re.compile(r'\b(?:used|use[sd]?|consumed|called|invoked|applied|cited|'
                      r'appears|occurs)\b[^`\n]{0,20}\bat\b', re.I)
DECL = re.compile(r'^(?:private |protected |noncomputable |partial |@\[[^\]]*\]\s*)*'
                  r'(?:theorem|lemma|def|abbrev|structure|instance|inductive|class) '
                  r'([A-Za-z_][A-Za-z0-9_.\']*)')


def sources():
    """basename -> [(path, {declaration name: line})], for every file in Theses/."""
    out = {}
    for p in sorted(LEAN.rglob("Theses/**/*.lean")):
        if ".lake" in p.parts:
            continue
        where = {}
        for i, line in enumerate(p.read_text(errors="replace").splitlines(), 1):
            m = DECL.match(line)
            if m:
                where.setdefault(m.group(1), i)
                short = m.group(1).rsplit(".", 1)[-1]
                where.setdefault(short, i)
        out.setdefault(p.name, []).append((p, where))
    return out


def main():
    write = "--write" in sys.argv
    src = sources()
    targets = (sorted(LEAN.rglob("Theses/**/*.lean"))
               + sorted((LEAN / "docs" / "audit").glob("*.csv"))
               + sorted((LEAN / "docs").glob("*.md"))
               + [LEAN / "ERRATA.md", LEAN / "QUESTIONS.md", LEAN / "PROVING-LOG.md"])
    drift, gone, ok, unnamed = [], [], 0, 0
    for path in targets:
        if ".lake" in path.parts:
            continue
        rel = path.relative_to(ROOT)
        historical = path.name == "PROVING-LOG.md" or path.name.endswith("-survey.md")
        lines = path.read_text(errors="replace").splitlines(keepends=True)
        changed = False
        for i, line in enumerate([l.rstrip("\n") for l in lines], 1):
            named = {(m.start(), m.group(2), m.group(3)) for m in NAMED.finditer(line)}
            unnamed += max(0, len(ANY.findall(line)) - len(named))
            for m in NAMED.finditer(line):
                # "`dils_stand_filter` IS used, at Pure.lean:2421" points at a
                # CALL SITE, not at the declaration, and reading it as the
                # latter reports a correct row as drifted.
                if USE_SITE.search(line[max(0, m.start() - 70):m.end()]):
                    ok += 1
                    continue
                name, fname, num = m.group(1), m.group(2).split("/")[-1], int(m.group(3))
                if fname not in src:
                    continue                      # Mathlib and other trees
                hits = [w[name] for _p, w in src[fname] if name in w]
                if not hits:
                    continue                      # not a declaration of that file
                if any(abs(h - num) <= SLACK for h in hits):
                    ok += 1
                elif not historical:
                    drift.append((rel, i, name, fname, num, sorted(hits)))
                    if write and len(set(hits)) == 1:
                        old_ref, new_ref = f"{fname}:{num}", f"{fname}:{hits[0]}"
                        if old_ref in lines[i - 1]:
                            lines[i - 1] = lines[i - 1].replace(old_ref, new_ref, 1)
                            changed = True
        if changed:
            path.write_text("".join(lines))
    for rel, i, name, fname, num, hits in drift:
        tag = "FIXED  " if (write and len(set(hits)) == 1) else "MOVED  "
        print(f"{tag} {rel}:{i}  `{name}` cited at {fname}:{num}, declared at "
              + ", ".join(f"{fname}:{h}" for h in hits)
              + ("" if len(set(hits)) == 1 else "  -- two declarations, left alone"))
    print(f"\n{ok} named `File.lean:N` references land within {SLACK} lines of the "
          f"declaration, {len(drift)} do not; {unnamed} further .lean line references "
          f"name no declaration and are not checked")
    return 1 if drift else 0


if __name__ == "__main__":
    sys.exit(main())
