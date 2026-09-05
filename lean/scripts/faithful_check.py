#!/usr/bin/env python3
"""Flag rows graded `faithful` whose thesis point prints no argument at all.

The 2026-09-04 sample found three wrong grades in 77 rows, all of one shape: a
bare Corollary with no nested proof point and no solution, graded `faithful`
where the vocabulary says `none`.  This check finds that shape mechanically.

A point "prints an argument" when it contains a nested point (a `{Proof}`, an
(2026-09-05: also a Hint, an imperative `\\sref`, a solution keyed to a sibling
point of the same parsec, or a row note saying where the print is), an
"Ad n", a "1 => 2"), or a `\\qed`, or the words "proof"/"follows"/"since" in
its own body, or has a solution in asols.tex (keyed parsec-P.Q) / bsols.tex
(keyed by label).  Rows whose point prints none of these and are graded
`faithful` are reported; the grade may still be right (an exercise's printed
instruction can be the argument), so this is a lead list, not a defect list.
"""
import sys, glob, os, re, sys, collections
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.dirname(ROOT)
ROMAN = {'I':1,'V':5,'X':10,'L':50}
def roman(s):
    t=0
    for i,c in enumerate(s):
        v=ROMAN[c]
        if i+1<len(s) and ROMAN[s[i+1]]>v: t-=v
        else: t+=v
    return t
def decode(disp):
    m=re.match(r'^(\d+)([a-z]?)([IVXL]+)([a-z]?)', disp)
    if not m: return None
    p=int(m.group(1))*10+(ord(m.group(2))-96 if m.group(2) else 0)
    q=roman(m.group(3))*10+(ord(m.group(4))-96 if m.group(4) else 0)
    return p,q
def parse(path):
    """-> {(parsec,point): (label, body_text, n_children)} for top-level points."""
    txt=open(path,encoding='utf-8').read().split('\n')
    out={}; parsec=None; stack=[]
    for line in txt:
        m=re.match(r'\\begin\{parsec\}\{(\d+)\}',line)
        if m: parsec=int(m.group(1)); continue
        m=re.match(r'\\begin\{point\}\{(\d+)\}(?:\[([^\]]*)\])?(?:\{([^}]*)\})?',line)
        if m:
            if stack: stack[-1][3]+=1
            stack.append([int(m.group(1)),m.group(2),[],0]); continue
        if line.startswith('\\end{point}'):
            if not stack: continue
            q,lab,body,nch=stack.pop()
            if not stack: out[(parsec,q)]=(lab,'\n'.join(body),nch)
            continue
        for fr in stack: fr[2].append(line)
    return out
FILES={'A':['cstar.tex','vn.tex','proc.tex'],'B':['dils.tex','eff.tex']}
def main():
    points={}
    for th,fs in FILES.items():
        for f in fs:
            for k,v in parse(os.path.join(SRC,f)).items(): points[(th,)+k]=(f,)+v
    asols=set(re.findall(r'solution\}\{parsec-([0-9.]+)\}',open(os.path.join(SRC,'asols.tex'),encoding='utf-8').read()))
    bsols=set(re.findall(r'solution\}\{([^}]+)\}',open(os.path.join(SRC,'bsols.tex'),encoding='utf-8').read()))
    hits=[]; n=0
    for path in sorted(glob.glob(os.path.join(ROOT,'docs','audit','*.csv'))):
        th='A' if os.path.basename(path).startswith('a') else 'B'
        for i,line in enumerate(open(path,encoding='utf-8'),1):
            q=line.rstrip('\n').split('|')
            if len(q)<6 or q[1] in ('','lean_name') or q[4]!='faithful': continue
            n+=1
            d=decode(q[0]); 
            if not d: continue
            pt=points.get((th,)+d)
            if not pt: continue
            f,lab,body,nch=pt
            if nch>0 or '\\qed' in body or re.search(r'\bproof\b|\bfollows\b|\bsince\b|\bbecause\b|\bindeed\b|\bhence\b|\bthus\b|\bso\b|\bHint\b|\\sref\{|\bUse\b|\bDeduce\b|\bConclude\b|\busing\b',body,re.I): continue
            key='%d.%d'%d
            if th=='A' and key in asols: continue
            if th=='A' and any(k.startswith('%d.'%d[0]) for k in asols): continue      # solution keyed to a sibling point
            if th=='B' and lab and lab in bsols: continue
            if th=='B' and any(v[1] in bsols for k2,v in points.items() if k2[0]=='B' and k2[1]==d[0] and v[1]): continue
            if re.search(r'printed (at|in)|solution (to|at)|proof (at|in) ', ' '.join(q[5:7]), re.I): continue   # the row says where the print is
            hits.append((os.path.basename(path),i,q[0],q[1],f))
    for h in hits: print('NOARG   %s:%d  %s  %s  (%s)'%h)
    print('%d faithful rows; %d name a point that prints no argument and has no solution'%(n,len(hits)))
    sys.exit(1 if hits else 0)
if __name__=='__main__': main()
