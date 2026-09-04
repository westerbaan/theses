#!/usr/bin/env python3
"""Find proofs that cite a later point of the thesis than the one they prove.

The author's ruling of 2026-09-04 on docs/DECISIONS.md §2.2: a proof of a
statement at point P may use only what the thesis has at or before P, except
where the printed proof of P itself cites a later point (`\\sref{label}` to a
label whose point comes later).  This lists, per DISP-tagged declaration, the
DISP-tagged declarations of a LATER point that its proof body names, minus the
forward references the printed point makes itself.  A lead list, not a defect
list: a name can be mentioned in a comment, or be a definition rather than a
result.
"""
import glob, os, re, sys, collections
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
import faithful_check as fc
SRC = os.path.dirname(ROOT)
TAG = re.compile(r'/--\s*\*\*(\d+[a-z]?[IVXL]+[a-z]?)(?:\.\d+)?\*\*')
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|local\s+|scoped\s+)*(?:theorem|lemma|def|abbrev|instance|structure|class)\s+([A-Za-z_][\w\'.₀-₉]*)')
def thesis_of(path):
    return 'A' if '/A/' in path else 'B'
def parse_tagged(path):
    """-> {(parsec,point): (label, tag, body)} for top-level points, in order."""
    txt = open(path, encoding='utf-8').read().split('\n')
    out = {}; parsec = None; stack = []
    for line in txt:
        m = re.match(r'\\begin\{parsec\}\{(\d+)\}', line)
        if m: parsec = int(m.group(1)); continue
        m = re.match(r'\\begin\{point\}\{(\d+)\}(?:\[([^\]]*)\])?(?:\{([^}]*)\})?', line)
        if m:
            stack.append([int(m.group(1)), m.group(2), m.group(3) or '', []]); continue
        if line.startswith('\\end{point}'):
            if not stack: continue
            q, lab, tag, body = stack.pop()
            if not stack: out[(parsec, q)] = (lab, tag, '\n'.join(body))
            else: stack[-1][3].append(line)
            continue
        for fr in stack: fr[3].append(line)
    return out
def load():
    points = {}
    for th, fs in fc.FILES.items():
        for f in fs:
            for k, v in parse_tagged(os.path.join(SRC, f)).items():
                points[(th,) + k] = v      # (label, tag, body)
    label_to_key = {}
    for k, (lab, tag, body) in points.items():
        if lab: label_to_key[(k[0], lab)] = k[1:]
    return points, label_to_key
def proof_extent(points, key):
    """The printed proof of `key`: its own body plus the following Proof-tagged
    (or untagged) points; returns (max point key in the extent, text)."""
    th, p, q = key
    keys = sorted(k[1:] for k in points if k[0] == th)
    i = keys.index((p, q)) if (p, q) in keys else None
    text = points[key][2]; last = (p, q)
    if i is None: return last, text
    STATEMENT = re.compile(r'Lemma|Proposition|Theorem|Corollary|Exercise|Definition|Example|Remark|Beware|Notation|Convention', re.I)
    for k2 in keys[i+1:]:
        lab, tag, body = points[(th,) + k2]
        if k2[0] != p or STATEMENT.search(tag or ''):
            break                      # the next statement of the parsec ends the printed proof
        text += '\n' + body; last = k2
    return last, text
def declarations():
    """-> list of (path, name, disp, key, proof_text) for DISP-tagged declarations."""
    out = []
    for path in sorted(glob.glob(os.path.join(ROOT, 'Theses', '**', '*.lean'), recursive=True)):
        th = thesis_of(path)
        lines = open(path, encoding='utf-8').read().split('\n')
        i = 0
        while i < len(lines):
            m = TAG.match(lines[i])
            if m:
                disp = m.group(1); key = fc.decode(disp)
                j = i
                while j < len(lines) and not DECL.match(lines[j]): j += 1
                if j < len(lines) and key:
                    name = DECL.match(lines[j]).group(1)
                    if re.match(r'^\s*(?:@\[[^\]]*\]\s*)?private\b', lines[j]):
                        i = j + 1; continue          # a private helper's DISP is provenance, not a claim
                    # body: until the next blank-line-separated top-level declaration or doc comment
                    k = j + 1; body = []
                    while k < len(lines) and not lines[k].startswith('/--') and not lines[k].startswith('/-!') and not DECL.match(lines[k]) and not lines[k].startswith('end ') and not lines[k].startswith('section'):
                        body.append(lines[k]); k += 1
                    out.append((path, name, disp, (th,) + key, '\n'.join(body)))
                    i = k; continue
            i += 1
    return out
def recorded_allowances():
    """lean_names whose audit row records that the forward reference is the
    thesis's own (an `\\sref`, a sub-point of the printed proof, a definition,
    or a filing artifact): the status field says so ('forward', 'allowed', 'sub-point', 'later point', 'filing artifact', 'provenance')."""
    out = set()
    for f in glob.glob(os.path.join(ROOT, 'docs', 'audit', '*.csv')):
        for line in open(f, encoding='utf-8'):
            q = line.rstrip('\n').split('|')
            if len(q) >= 6 and re.search(r'forward|allowed|sub-point|later point|filing artifact|provenance', ' '.join(q[5:7]), re.I):
                for name in q[1].split(','):
                    out.add(name.strip().split('.')[-1])
    return out
def main():
    points, l2k = load()
    decls = declarations()
    allowed_rows = recorded_allowances()
    by_name = {}
    for path, name, disp, key, body in decls:
        by_name.setdefault(name.split('.')[-1], []).append(key)
    hits = collections.Counter(); lines_out = []
    for path, name, disp, key, body in decls:
        th, p, q = key
        pt = points.get(key)
        allowed = set(); last = (p, q)
        if pt:
            last, text0 = proof_extent(points, key)
            for lab in re.findall(r'\\sref\{([^}]*)\}', text0):
                k2 = l2k.get((th, lab))
                if k2 and k2 > (p, q): allowed.add(k2)
        # strip comments
        text = re.sub(r'--[^\n]*', '', body); text = re.sub(r'/-.*?-/', '', text, flags=re.S)
        # names that are Mathlib fields/lemmas, not thesis declarations, collide by short spelling
        MATHLIB_FP = {'map_comp','map_id','map_eta','map_smul','map_add','map_mul','map_one','comp_id','id_comp'}
        idents = set(re.findall(r"[A-Za-z_][\w'₀-₉]*", text)) - MATHLIB_FP
        later = set()
        for ident in idents:
            if len(ident) < 8 or ('_' not in ident and not re.search(r'[a-z][A-Z]', ident)):
                continue            # short or generic names collide with Mathlib
            keys2 = by_name.get(ident, [])
            if len(set(keys2)) != 1: continue   # declared under several points: ambiguous
            k2 = keys2[0]
            if k2[0] == th and k2[1:] > last and k2[1:] not in allowed and k2 != key:
                later.add((ident, k2[1:]))
        if later and name.split('.')[-1] in allowed_rows:
            later = set()             # the row records the allowance; not re-listed
        if later:
            hits[os.path.relpath(path, ROOT)] += 1
            cites = ', '.join(sorted(f"{i}({pp}.{qq})" for i, (pp, qq) in later))[:200]
            lines_out.append(f"FORWARD  {os.path.relpath(path, ROOT)}  {disp} {name} -> {cites}")
    for l in lines_out: print(l)
    print()
    for f, n in sorted(hits.items()): print(f"{n:4d}  {f}")
    print(f"{len(lines_out)} DISP-tagged proofs cite a later point the printed proof does not (rows that record an allowance are not listed)")
if __name__ == '__main__': main()
