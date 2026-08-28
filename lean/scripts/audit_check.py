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

2. SCHEMA

A row is `DISP|lean_name|module|stmt|proof|note[|status]` -- six or seven
fields.  Prose that contains a literal `|` silently splits into extra ones,
and every field after the break is then read as the wrong column.  Three
causes have occurred: ASCII norms `||a||`, modulus and ket-bra bars (`|z|`,
`|z><z|`) and maps-to arrows (`|->`), and dated status notes appended with a
`|` instead of merged.  32 rows across seven files were broken this way
before the check existed.

3. UNROWED DECLARATIONS

The audit's stated invariant is one row per DISP-carrying declaration.  The
inverse of a phantom: a declaration whose doc comment OPENS with a DISP tag,
so it claims to carry that point, and which no row names.  Detection is
deliberately strict -- only `/-- **NNN**` counts, not a DISP appearing later
in the prose, because an opening citation ("by **88VI** `double_commutant`")
reads the same to a looser matcher and a 220-character window reported 202
where the strict rule reports 139.  False negatives are the safe direction.

A row names a declaration by its qualified name (`DPoset.sub_left_cancel`),
so the tagged declaration is matched under every enclosing-namespace suffix,
as in the phantom check.  Matching the bare name alone reported 15 rowed
B/Eff declarations as unrowed, and 28 more elsewhere, on 2026-08-27; a
worker's natural repair for that is to STRIP the namespace out of
`lean_name`, which loses information the audit deliberately records.  Two
further sources of false reports are described on `tagged_declarations`:
prose inside a doc comment read as a declaration, and a doc comment on an
anonymous `instance` attributed to the next named declaration.

4. MISPLACED ROWS

A row whose declaration exists, but not in the module the row names.  The
phantom check matches names tree-wide, so a rename is invisible whenever some
*other* file happens to define a declaration of the old name: `avn-projections`
named `CentreSeparating` long after it became `CentrePositiveSeparating`, and
passed, because an unrelated `CentreSeparating` lives in `A/CStar/Positive`.
A negative grep on such a row reads false today while being true of what it
meant.

5. PHANTOM ROWS

A row naming a declaration that no longer exists.  Every comma-separated
name in `lean_name` is checked; a `lean_name` that is prose rather than a name
list (`Mathlib EuclideanSpace C (Fin N)`) is skipped.  Proof repairs delete the
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


def code_lines(path):
    """(lineno, line) for every line, with block and doc comment spans blanked.

    Comment text must be removed, not merely skipped line-by-line: a line that
    CLOSES a comment carries prose before its `-/`, and yielding it whole is
    how `instance clashes on lattice carriers.) -/` produced a declaration
    named `clashes`.  Eleven such phantoms existed tree-wide, and because
    tree_declarations() feeds the phantom check, a row naming one of them
    would have PASSED it.
    """
    depth = 0
    for i, ln in enumerate(open(path, encoding='utf-8'), 1):
        out, j = [], 0
        while j < len(ln):
            if depth == 0 and ln.startswith('/-', j):
                depth += 1; j += 2
            elif depth > 0 and ln.startswith('-/', j):
                depth -= 1; j += 2
            else:
                out.append(' ' if depth else ln[j]); j += 1
        yield i, ''.join(out)


def declaration_files():
    """name -> the set of files defining it, for locating a row's declaration."""
    where = {}
    for path in glob.glob(os.path.join(ROOT, 'Theses', '**', '*.lean'),
                          recursive=True):
        rel = os.path.relpath(path, ROOT)
        stack = []
        for _, ln in code_lines(path):
            m = NS_OPEN.match(ln)
            if m:
                stack.extend(m.group(1).split('.')); continue
            m = NS_END.match(ln)
            if m:
                parts = m.group(1).split('.')
                if stack[-len(parts):] == parts:
                    del stack[-len(parts):]
                continue
            m = DECL.match(ln)
            if m:
                n = m.group(1)
                where.setdefault(n, set()).add(rel)
                for i in range(len(stack)):
                    where.setdefault('.'.join(stack[i:] + [n]), set()).add(rel)
    return where


def module_file(field):
    """The .lean path a row's `module` field names, or None if it is loose."""
    f = field.strip()
    if not f:
        return None
    if not f.endswith('.lean'):
        f = f + '.lean'
    if not f.startswith('Theses/'):
        f = 'Theses/' + f
    return f if os.path.exists(os.path.join(ROOT, f)) else None


def tree_declarations():
    """Every declaration name under Theses/, qualified by every enclosing
    namespace suffix -- the audit may name it at any depth."""
    names = set()
    for path in glob.glob(os.path.join(ROOT, 'Theses', '**', '*.lean'),
                          recursive=True):
        stack = []
        for _, ln in code_lines(path):
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
        for _, ln in code_lines(path):
            m = DECL.match(ln)
            if m:
                cur = m.group(1)
                # a one-line `:= by sorry` lives on the declaration line itself
                if SORRY.search(ln[m.end():]):
                    out[cur] = rel
                continue
            if cur and '`' not in ln:
                code = ln.split('--')[0]
                if SORRY.search(code):
                    out[cur] = rel
    return out


def schema_violations():
    """Rows whose prose has split into extra columns."""
    bad = []
    for path in sorted(glob.glob(os.path.join(ROOT, 'docs', 'audit', '*.csv'))):
        for i, line in enumerate(open(path, encoding='utf-8'), 1):
            f = line.rstrip('\n').split('|')
            if len(f) > 1 and len(f) not in (6, 7):
                bad.append((os.path.basename(path), i, len(f),
                            f[0], f[1] if len(f) > 1 else ''))
    return bad


def name_list(field):
    """The declaration names a `lean_name` field cites, or None if it is prose.

    A field is a name list when every comma-separated part is a bare
    identifier -- no spaces, no parentheses.  Anything else (`Mathlib
    EuclideanSpace C (Fin N)`, `... (no declaration; Basic.lean:47)`) names a
    Mathlib carrier or a doc block rather than a declaration of ours, and is
    not checked.

    Multi-name rows were invisible to the phantom check until 2026-08-27: the
    check skipped any field containing a space, which is every list of two or
    more names.  46 rows were exempt and one of them was a phantom.
    """
    parts = [p.strip() for p in field.split(',')]
    if all(p and ' ' not in p and '(' not in p for p in parts):
        return parts
    return None


# A sub-clause label may carry a parenthesised part -- `**189aII.3(a)**`.
# Without the optional group the number matches but the closing `**` does not,
# so such a declaration reads as untagged and the unrowed check never sees it.
TAG_OPENS = re.compile(r'^/--\s*\**\s*\*\*(\d{1,3}[a-z]?[IVXL]+(?:\.[0-9a-z]+)?(?:\([a-z]\))?)\*\*')
PRIVATE = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*private\b')


# Lines that may sit between a doc comment and the declaration it documents
# without breaking the pairing: attributes, and the `open X in` /
# `set_option ... in` / `attribute [...] in` prefixes.
CARRIES_DOC = re.compile(r'^\s*(?:@\[|attribute\b)|(?:\bin)$')


def tagged_declarations():
    """(disp, name, names, private, location) for each declaration whose doc
    comment opens with a DISP tag.

    `names` is the declaration's name under every enclosing namespace suffix,
    the same convention `tree_declarations` uses, because that is how the
    audit cites it: a declaration inside `namespace DPoset` is
    `DPoset.sub_left_cancel` in a row, and matching only the bare name
    reported 15 rowed declarations as unrowed on 2026-08-27.

    Two things the first version of this got wrong, both of which made it
    report declarations that do not exist, or not the ones documented:

    * `DECL` was matched against every line, INCLUDING PROSE INSIDE THE DOC
      COMMENT.  A doc comment that wraps as "... to avoid\ninstance clashes
      on lattice carriers" was read as a declaration named `clashes`; eleven
      such phantoms were reported across the tree, and the same regex feeds
      `tree_declarations`, so a row naming one of them would have passed the
      phantom check.
    * A doc comment on an ANONYMOUS declaration (`instance : Category
      HilbObj`) matches no name, so the doc stayed pending and was attributed
      to the *next* named declaration -- `hilb_comp` was reported as carrying
      214II, and three more elsewhere (`dupEquivSetOp`, `algebraMap_coe`,
      `le_def`).  A doc block not followed by a nameable declaration is now
      dropped: a false negative, which is the safe direction, and the same
      blind spot as the 198II `PredSquare.category` phantom.
    """
    out = []
    for path in glob.glob(os.path.join(ROOT, 'Theses', '**', '*.lean'),
                          recursive=True):
        rel = os.path.relpath(path, ROOT)
        stack = []
        doc = None
        in_comment = False
        in_doc = False
        for i, ln in enumerate(open(path, encoding='utf-8'), 1):
            s = ln.strip()
            if in_comment:
                if in_doc:
                    doc = doc + ' ' + s
                if '-/' in s:
                    in_comment = False
                    in_doc = False
                continue
            if s.startswith('/--'):
                doc = s
                in_comment = '-/' not in s[3:]
                in_doc = in_comment
                continue
            if s.startswith('/-'):
                doc = None
                in_comment = '-/' not in s[2:]
                continue
            m = NS_OPEN.match(ln)
            if m:
                stack.extend(m.group(1).split('.'))
                doc = None
                continue
            m = NS_END.match(ln)
            if m:
                parts = m.group(1).split('.')
                if stack[-len(parts):] == parts:
                    del stack[-len(parts):]
                doc = None
                continue
            m = DECL.match(ln)
            if m:
                if doc:
                    d = TAG_OPENS.match(doc)
                    if d:
                        n = m.group(1)
                        names = {n} | {'.'.join(stack[k:] + [n])
                                       for k in range(len(stack))}
                        out.append((d.group(1), n, names,
                                    bool(PRIVATE.match(ln)), f'{rel}:{i}'))
                doc = None
                continue
            if s and not CARRIES_DOC.search(s):
                doc = None
    return out


def audit_rows():
    for path in sorted(glob.glob(os.path.join(ROOT, 'docs', 'audit', '*.csv'))):
        for i, line in enumerate(open(path, encoding='utf-8'), 1):
            f = line.rstrip('\n').split('|')
            if len(f) > 5 and f[1] and f[1] != 'lean_name':
                yield os.path.basename(path), i, f


def stale_status(names):
    """Declarations `docs/status.txt` still names that the tree has deleted.

    `status.txt` is generated by `scripts/StatusDump.lean` and is the data
    behind the Sorry Map and behind every "it is green" claim in the docs.  It
    is regenerated by hand, so a deletion round leaves it naming declarations
    that are gone -- and a reader who checks a name against it gets a `green`
    for something that no longer exists.  Only that direction is checked: the
    file holds theorems only, so a `def` missing from it is not an error.
    """
    path = os.path.join(ROOT, 'docs', 'status.txt')
    if not os.path.exists(path):
        return []
    # A structure field, a `where`-block component and an auto-generated
    # projection are all in `status.txt` and in none of `tree_declarations`'s
    # `theorem`/`def` lines, so the declaration list alone reports 305 false
    # positives.  The second test is the blunt one that removes them: does the
    # short name occur in the sources at all?  A deleted declaration's name
    # occurs nowhere; a projection's occurs in the structure that declares it.
    blob = []
    for pth in glob.glob(os.path.join(ROOT, 'Theses', '**', '*.lean'),
                         recursive=True):
        blob.append(''.join(ln for _, ln in code_lines(pth)))
    text = '\n'.join(blob)
    out = []
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            f = line.rstrip('\n').split('|')
            if len(f) != 3:
                continue
            short = f[1].rsplit('.', 1)[-1]
            if f[1] in names or short in names:
                continue
            # `instFooBar` is a name Lean synthesises for an anonymous
            # `instance`, and `toParentClass` one it synthesises for an
            # `extends` projection.  Neither is written anywhere, so neither
            # test above can find it.
            if short.startswith('inst') or re.match(r'to[A-Z]', short):
                continue
            if re.search(r'(?<![\w.])' + re.escape(short) + r'(?![\w])', text):
                continue
            out.append(f[1])
    return sorted(set(out))


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

    # Unrowed DISP-tagged declarations.
    all_names = set()
    for _, _, f in rows:
        for n in name_list(f[1]) or []:
            all_names.add(n)
    unrowed = [t for t in tagged_declarations() if not (t[2] & all_names)]
    for disp, name, _names, priv, loc in unrowed:
        print(f'UNROWED    {loc}  {disp}  {name}'
              f'{"  (private)" if priv else ""}')

    # Misplaced rows: the declaration exists, but not where the row says.
    where = declaration_files()
    misplaced = []
    for fn, i, f in rows:
        mf = module_file(f[2])
        if mf is None:
            continue
        for n in name_list(f[1]) or []:
            homes = where.get(n)
            if homes and mf not in homes:
                misplaced.append((fn, i, f[0], n, mf, sorted(homes)))
    for fn, i, disp, n, mf, homes in misplaced:
        print(f'MISPLACED  {fn}:{i}  {disp}  {n}')
        print(f'           row says {mf}; defined in {", ".join(homes)}')

    schema = schema_violations()
    for fname, i, nf, disp, name in schema:
        print(f'SCHEMA     {fname}:{i}  {disp}  {name}')
        print(f'           {nf} fields, expected 6 or 7 -- a literal `|` in the prose')

    # Phantom rows.
    names = tree_declarations()
    by_point = {}
    for _, _, f in rows:
        by_point.setdefault(f[0], []).append(f)
    phantom = []
    for fn, i, f in rows:
        cited = name_list(f[1])
        if cited is None:
            continue
        missing = [n for n in cited if n not in names]
        if missing:
            phantom.append((fn, i, f, missing))
    for fn, i, f, missing in phantom:
        print(f'PHANTOM    {fn}:{i}  {f[0]}  {", ".join(missing)}  '
              f'(proof={f[4]})')
        live = []
        for g in by_point[f[0]]:
            for n in name_list(g[1]) or []:
                if n not in missing and n in names:
                    live.append((n, g[4]))
        if live:
            print(f'           {f[0]} still covered by: '
                  + ', '.join(f'{n} ({pr})' for n, pr in live))
        else:
            print(f'           {f[0]} HAS NO OTHER LIVE ROW -- coverage lost')

    stale = stale_status(names)
    for name in stale:
        print(f'STALE      docs/status.txt  {name}')
        print(f'           status.txt names a declaration the tree does not have; '
              f'regenerate with `lake env lean scripts/StatusDump.lean`')

    print(f'\n{len(tree)} sorries in the tree, {len(recorded)} rows classed '
          f'`sorry`; {len(orphaned)} orphaned, {len(unrecorded)} unrecorded, '
          f'{len(phantom)} phantom, {len(schema)} schema, '
          f'{len(unrowed)} unrowed, {len(misplaced)} misplaced, '
          f'{len(stale)} stale in status.txt')
    return 1 if (orphaned or unrecorded or phantom or schema or unrowed
                 or misplaced or stale) else 0


if __name__ == '__main__':
    sys.exit(main())
