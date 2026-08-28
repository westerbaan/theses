#!/usr/bin/env python3
"""Flag doc comments that claim a von Neumann setting the Lean type does not have.

A doc comment saying "an mi-bilinear map between von Neumann algebras is
completely positive" over a signature whose binders are `CStarAlgebra` is
stating the *thesis's* theorem and proving a stronger one.  That is not a
harmless wording slip: the audit row above it is then graded against a
statement the tree does not make, which is how `113II` and all four renderings
of `113IV` sat at `stmt=ok` while a fifth rendering of the same generalisation,
in `A/CStar`, was graded `stronger`.

The binders cannot be read off the source -- `variable`, `omit ... in`, section
structure and superclass instances all intervene -- so they are taken from
`docs/binders.txt`, which `scripts/BinderDump.lean` writes by walking the
elaborated environment.  Regenerate it after changing any signature:

    lake env lean scripts/BinderDump.lean

A doc comment is flagged when its **first sentence** says "von Neumann" and the
declaration's type carries `CStarAlgebra` without `Theses.VonNeumannAlgebra`.

Two phrases are not claims about the setting and are excluded: a *von Neumann
subalgebra* and a *von Neumann tensor product* are objects named in the
statement, carried by predicates like `IsVNSubalgebra` and by `vnTensor`, and a
declaration about them needs no von Neumann binder on the ambient type.
"""

import pathlib
import re
import sys

LEAN = pathlib.Path(__file__).resolve().parents[1] / "Theses"
BINDERS = pathlib.Path(__file__).resolve().parents[1] / "docs" / "binders.txt"

DECL = re.compile(r'^(?:private |protected |noncomputable |@\[[^\]]*\]\s*)*'
                  r'(?:theorem|lemma) (\S+)')
TAG = re.compile(r'\*\*(\d{1,3}[a-z]?[IVXL]+(?:\.[0-9a-z]+)?)\*\*')
# an object, not a hypothesis about the ambient algebra
OBJECTS = ("von Neumann subalgebra", "von Neumann subalgebras",
           "von Neumann tensor product")


def binder_table():
    out = {}
    if not BINDERS.exists():
        sys.exit(f"{BINDERS} is missing; run `lake env lean scripts/BinderDump.lean`")
    for line in BINDERS.read_text().splitlines():
        parts = line.split("|")
        if len(parts) == 3:
            out[parts[1]] = (parts[0], [c for c in parts[2].split(",") if c])
    return out


def doc_of(lines, i):
    """The doc comment immediately above line `i`, or None."""
    j = i - 1
    while j >= 0 and not lines[j].lstrip().startswith("/--"):
        if lines[j].strip() == "" or lines[j].lstrip().startswith("--"):
            return None
        j -= 1
    return " ".join(lines[j:i]) if j >= 0 else None


def main():
    binders = binder_table()
    hits = []
    for src in sorted(LEAN.rglob("*.lean")):
        lines = src.read_text().splitlines()
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m:
                continue
            doc = doc_of(lines, i)
            if not doc:
                continue
            first = doc.split(". ")[0]
            if "on Neumann" not in first or any(o in first for o in OBJECTS):
                continue
            cand = [k for k in binders if k == m.group(1) or k.endswith("." + m.group(1))]
            if not cand:
                continue
            classes = binders[cand[0]][1]
            has = lambda k: any(k in c for c in classes)
            if has("CStarAlgebra") and not has("VonNeumannAlgebra"):
                tag = TAG.search(doc)
                hits.append((src, i + 1, m.group(1), tag.group(1) if tag else "-",
                             " ".join(first.split())[:140]))

    for src, ln, name, tag, txt in hits:
        print(f"VNCLAIM {src}:{ln}  {name}  [{tag}]\n        {txt}")
    print(f"\n{len(hits)} doc comments claim a von Neumann setting their type does not have")
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main())
