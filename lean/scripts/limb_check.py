#!/usr/bin/env python3
"""Re-check `docs/DEAD-LIMBS.md`'s liveness claims against the tree.

The document is full of sentences of the form "`foo` — zero consumers",
"confirmed dead", "still dead".  Every one of them was true when written and
none of them is rechecked by anything.  A limb that acquires a consumer leaves
a false sentence behind, and the next sweep inherits it: §5.1 and §5.2 were both
overturned that way, and §10c's "no longer an orphan by direct count" survived
until a cone pass contradicted it.

So: pull the names out of the dead-claims, count their *code* uses in
`Theses/` — comments blanked, the defining occurrence not counted — and report
the ones that are alive.  A name the tree no longer has is reported separately:
that is a deletion the document records, not a stale claim.

The count is the same textual one the sweep used, with the same blind spots
(`docs/DEAD-LIMBS.md` §1 lists eight ways a zero-use lies).  It is a check on
the document, not a liveness oracle: a name it reports as alive really does
occur, and a name it reports as dead may still be reached through a dotted
projection.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
LEAN = ROOT / "Theses"
DOC = ROOT / "docs" / "DEAD-LIMBS.md"

CLAIMS = re.compile(
    r'(confirmed dead|still dead|are dead|is dead|zero[- ]use|zero consumers?|'
    r'no consumers?|unconsumed|reached from nothing|has none|dead by both)',
    re.I)
NAME = re.compile(r'`([A-Za-z_][A-Za-z0-9_.\']*)`')
DEFN = re.compile(r'^\s*(?:private |protected |noncomputable |partial )*'
                  r'(?:theorem|lemma|def|abbrev|structure|instance|inductive) '
                  r'([A-Za-z_][A-Za-z0-9_.\']*)')


def code_text():
    """Every Lean source in `Theses/`, with comment spans blanked."""
    out = []
    for p in sorted(LEAN.rglob("*.lean")):
        src = p.read_text(errors="replace")
        buf, i, depth = [], 0, 0
        while i < len(src):
            if src.startswith("/-", i):
                depth += 1
                buf.append("  ")
                i += 2
            elif src.startswith("-/", i) and depth:
                depth -= 1
                buf.append("  ")
                i += 2
            else:
                buf.append(" " if depth else src[i])
                i += 1
        out.append((p, re.sub(r'--[^\n]*', '', "".join(buf))))
    return out


def subjects(line):
    """The names a line is *about*, not every name it mentions.

    Prose is not read at all.  In every case this check tried and got wrong, the
    document was saying the name is alive in the same sentence that carried a
    dead-claim about something else -- "parsec 1490's proofs go through
    `unSeminorm_add_le` directly", "`mem_vnComm_top` is named as dead by both §7
    and §10c, and it is not".  A sentence cannot be read for its subject with a
    regex, so only the two structured positions are used: the names a bullet
    opens with, and the first cell of a table row.  That is where the sweep puts
    the declaration a claim is about.
    """
    t = line.lstrip()
    if t.startswith("|"):
        cells = t.split("|")
        return NAME.findall(cells[1]) if len(cells) > 1 else []
    if t.startswith(("*", "-")):
        head = re.split(r'(?<=[.:;])\s', t.lstrip("*- "), maxsplit=1)[0]
        # the document's convention puts the *file* in parentheses after the
        # declaration -- `ipf_sub_right` (`SelfDualCompletion`) -- and some file
        # names are also declaration names
        head = re.sub(r'\([^()]*\)', " ", head)
        return NAME.findall(head)
    return []


def main():
    sources = code_text()
    defined, uses = {}, {}
    for p, code in sources:
        for line in code.splitlines():
            m = DEFN.match(line)
            if m:
                defined.setdefault(m.group(1), p)

    def count(name):
        if name in uses:
            return uses[name]
        # §13.6's fourth implementation trap: a use token has to be found under
        # *every contiguous run of its dotted components*, not only its suffixes
        # and not only its prefixes.  `le_vnComm_comm.mpr` is a use of
        # `le_vnComm_comm`; `hW.norm_ipVal_self_le` is a use of
        # `norm_ipVal_self_le`; `hΩ.centralProj.conj` is a use of `centralProj`,
        # which is neither the first component nor the last.  Bounding on
        # identifier characters only -- letting a dot sit on either side -- finds
        # all three.  It over-counts a short name against Mathlib's, and that is
        # the safe direction here: over-counting reports a limb as alive and a
        # person checks, under-counting silently confirms a stale dead-claim.
        pat = re.compile(r"(?<![A-Za-z0-9_'])" + re.escape(name) + r"(?![A-Za-z0-9_'])")
        n = sum(len(pat.findall(code)) for _, code in sources)
        uses[name] = max(0, n - (1 if name in defined else 0))
        return uses[name]

    # Most dead-claims are not sentences.  They are bullets and table rows under
    # a heading that says "all zero-use" or "Kept, each with its reason" once,
    # for the whole list.  So a claim is in scope either on its own line or
    # inside such a list, which runs until the next heading.
    LIST_OPENS = re.compile(r'(all zero-use|Kept, each with its reason|'
                            r'confirmed dead|re-confirmed dead|all of them dead)', re.I)
    HEADING = re.compile(r'^(#{1,4} |\*\*\d)')
    # A line that states a nonzero count is not claiming the names on it are
    # dead -- it is doing the opposite, or naming an API rather than a
    # declaration.  Without this the check reports its own document back.
    COUNTED = re.compile(r'(is consumed|are consumed|now has|now have|has \*?\*?\d|'
                         r'have \d|\d+ uses|\d+ consumers|uses each|consumers? and|'
                         r'zero-use but|remainder of the|has two|has three|now consumed|and it is not|used \\w+ times)', re.I)

    alive, gone, checked = [], set(), 0
    in_list = False
    doc_lines = DOC.read_text().splitlines()
    for i, line in enumerate(doc_lines, 1):
        # Markdown wraps, so a claim and its qualifier ("… is consumed inside
        # `tensor_factorisation`'s own proof", "It is now consumed by 110III's
        # own proof") land on later lines.  Both tests read a four-line window;
        # the report keeps the first line's number.
        window = " ".join(doc_lines[i - 1:i + 3])
        if HEADING.match(line):
            in_list = False
        if LIST_OPENS.search(line):
            in_list = True
        scoped = in_list and (line.lstrip().startswith(("*", "-", "|")))
        if not (scoped or CLAIMS.search(window)):
            continue
        if COUNTED.search(window):
            continue
        for name in subjects(line):
            if "." in name and not name[0].islower():
                continue                           # a module path, not a name
            if name not in defined:
                gone.add(name)
                continue
            checked += 1
            n = count(name)
            if n:
                alive.append((i, name, n, " ".join(line.split())[:150]))

    for ln, name, n, sentence in alive:
        print(f"ALIVE  DEAD-LIMBS.md:{ln}  `{name}` has {n} code use"
              f"{'s' if n > 1 else ''}\n       {sentence}")
    print(f"\n{checked} names claimed dead were re-counted, {len(alive)} "
          f"{'has' if len(alive) == 1 else 'have'} a code use; {len(gone)} names in "
          f"dead-claims are no longer in the tree (deleted, as the document records)")
    return 1 if alive else 0


if __name__ == "__main__":
    sys.exit(main())
