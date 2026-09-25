#!/usr/bin/env python3
"""Number the theorem-like environments of each paper as LaTeX does.

All three papers use one global counter shared by every theorem-like
environment (no per-section reset), so "Theorem 12" is the 12th numbered
environment of the paper.  Starred environments are unnumbered and listed
with number "-".  Writes papers/<tag>-points.csv:
    tag|num|kind|label|file:line|first line of the statement
"""
import re, os
PAPERS = {
    'EJA': ('1805.11496/main.tex',
            'Pure Maps between Euclidean Jordan Algebras (2018)'),
    'OAP': ('1912.10040/first.tex',
            'A characterisation of ordered abstract probabilities (2019)'),
    'SEA': ('2004.12749/second.tex',
            'The three types of normal sequential effect algebras (2020)'),
    'REC': ('2109.10707/short.tex',
            "A computer scientist's reconstruction of quantum theory (2021)"),
}
ENV = re.compile(r'\\begin\{(theorem\*?|proposition|lemma|corollary|definition|example|remark|notation|note)\}(?:\[([^\]]*)\])?')
LAB = re.compile(r'\\label\{([^}]*)\}')
here = os.path.dirname(os.path.abspath(__file__))
for tag, (path, title) in PAPERS.items():
    lines = open(os.path.join(here, path), encoding='utf-8').read().split('\n')
    n = 0; rows = []
    for i, l in enumerate(lines):
        if l.lstrip().startswith('%'):
            continue
        m = ENV.search(l)
        if not m:
            continue
        kind = m.group(1)
        if kind.endswith('*'):
            num = '-'
        else:
            n += 1; num = str(n)
        lab = ''
        for j in range(i, min(i + 4, len(lines))):
            ml = LAB.search(lines[j])
            if ml:
                lab = ml.group(1); break
        body = ' '.join(x.strip() for x in lines[i:i + 4])
        body = re.sub(r'\\label\{[^}]*\}|\\begin\{[^}]*\}(\[[^\]]*\])?', '', body)
        body = re.sub(r'\s+', ' ', body).replace('|', '/').strip()[:140]
        rows.append(f"{tag}|{num}|{kind.rstrip('*').capitalize()}|{lab}|{os.path.basename(path)}:{i+1}|{body}")
    with open(os.path.join(here, f'{tag}-points.csv'), 'w') as o:
        o.write('tag|num|kind|label|loc|start\n' + '\n'.join(rows) + '\n')
    print(tag, n, 'numbered points', '—', title)
