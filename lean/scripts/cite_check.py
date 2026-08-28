#!/usr/bin/env python3
"""Check every `label`, file.tex:N citation in the Lean tree against the sources.

A citation in the tree looks like

    **108I** (`bilinear-basic`, proc.tex:2012, Definition)

and it makes two claims at once: that the point is called `bilinear-basic`, and
that the cited line is in it.  The .tex files move under editing and the line
half of the claim goes stale silently, because nothing compiles it.

The test is *containment*, not equality.  A citation is entitled to point at a
displayed equation or a sub-clause part-way through a point, so the question is
whether the cited line still falls inside the extent of the thing the label
names -- not whether it equals the line the label opens on.  Anything else
would report the tree's most careful citations as errors.

Four constructs carry a label:

    \\begin{parsec}{N}[label]        ... \\end{parsec}
    \\begin{point}{N}[label]{Kind}   ... \\end{point}
    \\begin{solution}{label}         ... \\end{solution}
    \\label{label}                   -- extent is the enclosing environment

Citations naming a file and a line but no label cannot be checked; they are
counted, not passed over in silence.
"""

import re
import sys
from pathlib import Path
from collections import defaultdict

ROOT = Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"

OPEN = re.compile(r'\\begin\{(parsec|point|solution)\}(.*)')
CLOSE = re.compile(r'\\end\{(parsec|point|solution)\}')
BRACKET_LABEL = re.compile(r'^\{[^}]*\}\[([^\]]+)\]')   # parsec/point: {N}[label]
BRACE_LABEL = re.compile(r'^\{([^}]+)\}')               # solution: {label}
LABEL_CMD = re.compile(r'\\label\{([^}]+)\}')

CITE = re.compile(r'`([A-Za-z0-9][A-Za-z0-9:_-]*)`,\s*`?([a-z]+\.tex):(\d+)')
BARE = re.compile(r'\b([a-z]+\.tex):(\d+)')

# A doc comment that opens with a DISP tag makes its own locating claim, and the
# tag alone decodes to a parsec and a point (docs/STATEMENT-AUDIT.md).  That is
# a second, label-free way to check a file:line reference -- the one that reaches
# the 331 self-citations carrying no label at all.
TAG = re.compile(r'^/--\s*\**\s*\*\*(\d{1,3})([a-z]?)([IVXL]+)'
                 r'(?:\.[0-9a-z]+)?(?:\([a-z]\))?\*\*(.*)')
SELFREF = re.compile(r'\(\s*`?([a-z]+\.tex):(\d+)`?')
ROMAN = {"I": 1, "V": 5, "X": 10, "L": 50}
# The solution files carry `\begin{solution}{label}` and no parsecs, so a tag
# cited against one is naming the *solution* to that exercise; it is checkable
# by label (the paired form) and not by decoding.
NO_PARSECS = {"asols.tex", "bsols.tex"}
# The word after the line reference is only a kind claim when it is a kind;
# otherwise the doc comment has simply run on into prose.
KINDS = {"Definition", "Definitions", "Proposition", "Theorem", "Lemma",
         "Corollary", "Exercise", "Example", "Examples", "Notation", "Fact",
         "Claim", "Remark", "Convention"}


def roman(s):
    total = 0
    for i, ch in enumerate(s):
        v = ROMAN[ch]
        total += -v if i + 1 < len(s) and ROMAN[s[i + 1]] > v else v
    return total


def points(tex_text):
    """(parsec key, point key) -> (start, end, kind) for one .tex file."""
    out = {}
    parsec = None
    pt = None
    for i, line in enumerate(tex_text.splitlines(), 1):
        m = re.search(r'\\begin\{parsec\}\{(\d+)\}', line)
        if m:
            parsec = m.group(1)
            continue
        m = re.search(r'\\begin\{point\}\{(\d+)\}(?:\[[^\]]*\])?(?:\{([^}]*)\})?', line)
        if m:
            if pt:
                out[pt[0]] = (pt[1], i - 1, pt[2])
            kind = (m.group(2) or "").split("(")[0].strip()
            pt = ((parsec, m.group(1)), i, kind)
            continue
        if re.search(r'\\end\{parsec\}', line) and pt:
            out[pt[0]] = (pt[1], i, pt[2])
            pt = None
    if pt:
        out[pt[0]] = (pt[1], len(tex_text.splitlines()), pt[2])
    return out
# `a`/`b`, vn.tex:2362/2684 -- one citation naming two points at once.  The
# labels pair with the lines in order, and CITE alone would pair the *last*
# label with the *first* line and report a defect that is not there.
PAIRED = re.compile(r'((?:`[A-Za-z0-9][A-Za-z0-9:_-]*`/)+`[A-Za-z0-9][A-Za-z0-9:_-]*`)'
                    r',\s*`?([a-z]+\.tex):((?:\d+/)+\d+)')


# `ineq-square-root` (cstar.tex:3611) -- the same claim with a paren instead of a
# comma.  Only 20 in the tree, and the form is ambiguous: `k` (eff.tex:2853) is a
# Lean binder, not a label.  So this shape is checked only when the name really
# is a label of the file it names, and the ones skipped are counted.
PARENCITE = re.compile(r'`([A-Za-z0-9][A-Za-z0-9:_-]*)`\s*\(\s*`?([a-z]+\.tex):(\d+)')


def citations(line):
    """Yield (label, tex, line-number) for one source line, slash-pairs first."""
    rest = line
    for m in PAIRED.finditer(line):
        labs = [x.strip('`') for x in m.group(1).split('/')]
        nums = [int(x) for x in m.group(3).split('/')]
        for lab, num in zip(labs, nums):
            yield lab, m.group(2), num
        rest = rest.replace(m.group(0), ' ' * len(m.group(0)))
    for m in CITE.finditer(rest):
        yield m.group(1), m.group(2), int(m.group(3))


def extents():
    """label -> {tex name: [(start, end), ...]}"""
    out = defaultdict(lambda: defaultdict(list))
    for tex in sorted(ROOT.glob("*.tex")):
        for lab, spans in extents_from_text(tex.read_text(errors="replace")).items():
            out[lab][tex.name].extend(spans)
    return out


def extents_from_text(text):
    """label -> [(start, end), ...] for one .tex file's contents.

    A frame on the stack carries the labels claimed for it: the one in its own
    header, plus every bare `\\label` met before it closes.  Equation labels are
    the reason for the second part -- `\\begin{equation}\\label{x}` inside a point
    is how the theses name a display, and such a label has to inherit the whole
    point's extent.  Giving it only the line the point opens on would report
    every citation of that display as drifted.
    """
    out = defaultdict(list)
    lines = text.splitlines()
    stack = []
    for i, line in enumerate(lines, 1):
        m = OPEN.search(line)
        if m:
            kind, rest = m.group(1), m.group(2)
            lm = (BRACE_LABEL if kind == "solution" else BRACKET_LABEL).match(rest)
            stack.append([i, [lm.group(1)] if lm else []])
        elif CLOSE.search(line):
            if stack:
                start, labs = stack.pop()
                for lab in labs:
                    out[lab].append((start, i))
        for lm in LABEL_CMD.finditer(line):
            if stack:
                stack[-1][1].append(lm.group(1))
            else:
                out[lm.group(1)].append((i, i))
    # environments left open at EOF run to the end of the file
    for start, labs in stack:
        for lab in labs:
            out[lab].append((start, len(lines)))
    return dict(out)


def contains(spans, n):
    return any(a <= n <= b for a, b in spans)


def with_proofs(table):
    """Extend each point's extent over the proof that follows it.

    `docs/STATEMENT-AUDIT.md`: "The proof, where there is one, is normally the
    *next* point (`Proof`), or the following few."  So a doc comment tagged with
    a statement is entitled to cite a line in that statement's proof, and the
    region a self-citation may land in runs from the point's own opening to the
    next point that states something new -- across `Proof`, across the
    unlabelled continuation points, and across the ones headed with a case
    split, none of which is a fresh statement.

    The extension stops at the end of the parsec whatever else happens.  The
    parsec is the unit a DISP tag names, and a run of unlabelled narrative
    points would otherwise let one tag's region swallow three hundred lines of
    the next subject -- which is how a checker stops catching anything.
    """
    order = sorted(table.items(), key=lambda kv: kv[1][0])
    out = {}
    for i, (key, (start, end, kind)) in enumerate(order):
        stop = end
        for k2key, (_s2, e2, k2) in order[i + 1:]:
            if k2key[0] != key[0]:
                break
            if k2 and k2.split()[0].rstrip("(") in KINDS:
                break
            stop = e2
        out[key] = (start, stop, kind)
    return out


def disp_check():
    """Check the self-citation of every DISP-tagged doc comment against its tag."""
    tables = {tex.name: with_proofs(points(tex.read_text(errors="replace")))
              for tex in sorted(ROOT.glob("*.tex"))}
    bad_line, bad_kind, unknown, ok = [], [], [], 0
    for src in sorted(LEAN.rglob("*.lean")):
        if ".lake" in src.parts:
            continue
        rel = src.relative_to(ROOT)
        lines = src.read_text(errors="replace").splitlines()
        for i, line in enumerate(lines):
            m = TAG.match(line)
            if not m:
                continue
            head = " ".join(lines[i:i + 3])
            ref = SELFREF.search(head)
            if not ref:
                continue
            tex, num = ref.group(1), int(ref.group(2))
            if tex in NO_PARSECS:
                continue
            parsec = str(int(m.group(1)) * 10 + (ord(m.group(2)) - 96 if m.group(2) else 0))
            point = str(roman(m.group(3)) * 10)
            tag = f"{m.group(1)}{m.group(2)}{m.group(3)}"
            where = tables.get(tex, {}).get((parsec, point))
            if where is None:
                unknown.append((rel, i + 1, tag, tex, num, parsec, point))
                continue
            start, end, kind = where
            if not (start <= num <= end):
                bad_line.append((rel, i + 1, tag, tex, num, start, end))
                continue
            ok += 1
            claimed = re.search(r'\(\s*`?[a-z]+\.tex:\d+`?\s*,\s*([A-Za-z]+)', head)
            if (claimed and kind and claimed.group(1) in KINDS
                    and claimed.group(1) != kind.split()[0]):
                bad_kind.append((rel, i + 1, tag, claimed.group(1), kind))

    for rel, ln, tag, tex, num, a, b in bad_line:
        print(f"TAGLINE {rel}:{ln}  **{tag}** cites {tex}:{num}; the tag decodes to "
              f"{tex}:{a}-{b}")
    for rel, ln, tag, tex, num, ps, pt in unknown:
        print(f"TAGGONE {rel}:{ln}  **{tag}** decodes to parsec {{{ps}}} point "
              f"{{{pt}}}, which {tex} does not have")
    for rel, ln, tag, claimed, real in bad_kind:
        print(f"TAGKIND {rel}:{ln}  **{tag}** calls it a {claimed}; the source says {real}")
    print(f"\n{ok} DISP self-citations land in the point their tag decodes to, "
          f"{len(bad_line)} do not, {len(unknown)} decode to a point that is not "
          f"there; {len(bad_kind)} name a different kind than the source")
    return bad_line or unknown or bad_kind


def main():
    if "--disp" in sys.argv:
        return 1 if disp_check() else 0
    ext = extents()
    drifted, unknown = [], []
    ok = paired = bare_total = skipped = 0
    for src in sorted(LEAN.rglob("*.lean")):
        if ".lake" in src.parts:
            continue
        rel = src.relative_to(ROOT)
        for i, line in enumerate(src.read_text(errors="replace").splitlines(), 1):
            bare_total += len(BARE.findall(line))
            for m in PARENCITE.finditer(line):
                lab, tex, num = m.group(1), m.group(2), int(m.group(3))
                if tex not in ext.get(lab, {}):
                    skipped += 1
                    continue
                paired += 1
                if contains(ext[lab][tex], num):
                    ok += 1
                else:
                    drifted.append((rel, i, lab, tex, num, ext[lab][tex]))
            for lab, tex, num in citations(line):
                paired += 1
                where = ext.get(lab, {})
                if tex not in where:
                    unknown.append((rel, i, lab, tex, num, sorted(where)))
                elif contains(where[tex], num):
                    ok += 1
                else:
                    drifted.append((rel, i, lab, tex, num, where[tex]))

    for rel, i, lab, tex, num, spans in sorted(drifted):
        real = ", ".join(f"{a}-{b}" for a, b in spans)
        print(f"DRIFT   {rel}:{i}  `{lab}` cited at {tex}:{num}, extent {tex}:{real}")
    for rel, i, lab, tex, num, elsewhere in sorted(unknown):
        seen = (" (found in " + ", ".join(elsewhere) + ")") if elsewhere else " (no label of that name)"
        print(f"NOLABEL {rel}:{i}  `{lab}` cited at {tex}:{num}{seen}")

    print(f"\n{ok} of {paired} label+line citations land inside the labelled extent, "
          f"{len(drifted)} outside it, {len(unknown)} name a label the cited file "
          f"does not carry; {skipped} parenthesised references name something that "
          f"is not a label of the file and are skipped; {bare_total - paired} "
          f"further file:line references carry no label and are not checked")
    return 1 if drifted or unknown else 0


if __name__ == "__main__":
    sys.exit(main())
