#!/usr/bin/env python3
"""Regenerate the exact replacement tables; Python standard library only."""
from pathlib import Path
import sys
from fractions import Fraction as Q
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'companion'))
from verify import load, slacks, verify
from polynomials import expr_signature, compose_affine
names=[r'\epsp',r'\PP_2',r'\SSS_2',r'\PP_3',r'\SSS_3',r'\DD',r'\EE']
def rat(a):
    a=Q(a)
    return str(a.numerator) if a.denominator==1 else r'\frac{%d}{%d}'%(a.numerator,a.denominator)
def poly(p,var='x'):
    terms=[]
    for k,a in reversed(list(enumerate(p))):
        if not a: continue
        v='' if k==0 else var if k==1 else var+'^{%d}'%k
        text=('' if abs(a)==1 and k else rat(abs(a)))+v
        terms.append(('-' if a<0 else '+' if terms else '')+text)
    return ''.join(terms) or '0'
def network(r): return r['op']+'('+names[r['i']]+','+names[r['j']]+')'
def table(filename,columns,caption,label,head,rows,stretch="1.25"):
    text=r'\begingroup\renewcommand{\arraystretch}{'+stretch+'}'+'\n'+r'\begin{longtable}{'+columns+'}\n'+r'\caption{'+caption+r'}\label{'+label+r'}\\'+'\n'+r'\toprule'+'\n'+head+r'\\ \midrule'+'\n'+r'\endfirsthead'+'\n'+r'\multicolumn{'+str(len(columns))+r'}{c}{\tablename~\thetable{} --- continued}\\[3pt]'+'\n'+r'\toprule'+'\n'+head+r'\\ \midrule'+'\n'+r'\endhead'+'\n'+'\n'.join(rows)+'\n'+r'\bottomrule'+'\n'+r'\end{longtable}'+'\n'+r'\endgroup'+'\n'
    (ROOT/'tables'/filename).write_text(text)
def main():
    print(verify());rep,full=load();ps=[expr_signature(p['expr']) for p in rep['pool']]
    rows=[]
    for n,p,rec in zip(names,ps,rep['pool']):
        rows.append(' & '.join('$'+s+'$' for s in [n,str(len(rec['edges'])),*map(str,rec['sig'][:2]),*[poly(a) for a in p]])+r' \\')
    table('profiles.tex','lrrrrrrr',r'The seven profiles; $h$ is the number of real edges. Here $\DD=S(\PP_2,\PP_2)$ and $\EE=P(\SSS_2,\SSS_2)$.','tab:profiles',r'$H$ & $h$ & $T$ & $F$ & $A(x)$ & $I(x)$ & $C(x)$ & $B(x)$',rows)
    rows=[]
    for r in rep['records']:
        for j,t in enumerate(r['certificate']):
            rows.append(' & '.join('$'+s+'$' if s else '' for s in [network(r) if j==0 else '',names[t['h']],*[rat(t[k]).replace(r'\frac',r'\dfrac') for k in ('u','v','w')]])+(r' \\*[5pt]' if j+1<len(r['certificate']) else r' \\[7pt]'))
    table('replacements.tex','llrrr',r'All 21 representative replacements and their 37 terms. Each row specifies $(H,u,v,w)$. The dual replacement exchanges $P$ and $S$, applies $\epsp^*=\epsp$, $\PP_k^*=\SSS_k$, and $\DD\leftrightarrow\EE$, and exchanges $u,v$ while preserving $w$.','tab:replacements',r'Network & $H$ & $u$ & $v$ & $w$',rows,stretch='1.45')
    lookup={(r['i'],r['j'],r['op']):r for r in full['records']}
    rows=[]
    def status(r):
        if r['status']=='new':return '$'+names[r['equal']]+'$'
        return 'replacement' if r['status']=='mixture' else 'excluded'
    for i in range(7):
        for j in range(i,7):
            rows.append('$'+names[i]+','+names[j]+'$ & '+status(lookup[i,j,'S'])+' & '+status(lookup[i,j,'P'])+r' \\')
    table('composition.tex','lll','All 56 compositions of unordered profile pairs. Excluded means that a real parallel or series class has at least four elements; a profile name means exact closure.','tab:composition',r'Pair & Series & Parallel',rows)
    rows=[];exceptions=[]
    coords=['A','A+I','C','C+B']
    for r in rep['records']:
        for j,s in enumerate(slacks(r,ps)):
            co=compose_affine(s,2,1)
            if min(co)<0:exceptions.append((network(r),coords[j],co))
            rows.append('$'+network(r)+'$ & $'+coords[j]+'$ & $('+', '.join(rat(c) for c in co)+r')$ \\')
    assert len(rows)==84 and len(exceptions)==4
    table('slacks.tex','lll',r'Coefficients $(c_0,\ldots,c_d)$ of every representative slack $\sum_{j=0}^d c_jt^j$, where $t=x-2$. Coordinates denote the target quantity minus the corresponding weighted cost. There are 80 nonnegative coefficient sequences and four exceptional cubics.','tab:slacks',r'Network & Coordinate & $(c_0,\ldots,c_d)$',rows)
    r=rep['records'][0];assert (r['i'],r['j'],r['op'])==(0,1,'S')
    worked=r'''For example, $S(\epsp,\PP_2)$ is replaced by the two terms
\[
(H,u,v,w)=(\epsp,4/5,5/4,1),\qquad(\SSS_2,3/5,5/3,1).
\]
Both satisfy $uv=w^2=1$, and the tree and forest budgets are
$1+1=2=T(S(\epsp,\PP_2))$ and $1+2=3=F(S(\epsp,\PP_2))$.
The replacement graphs have respectively one and two edges, whereas the
original has three. In coordinate order $(A,A+I,C,C+B)$, the four slacks are
\[
'''+r'\left('+r',\;'.join(poly(s) for s in slacks(r,ps))+r'\right).'+ '\n'+r'\]'+'\n'+r'''After $x=2+t$, their coefficient sequences are
\[
'''+r'\left('+r',\;'.join('('+','.join(rat(c) for c in compose_affine(s,2,1))+')' for s in slacks(r,ps))+r'\right),'+ '\n'+r'\]'+'\n'+r'all of which are nonnegative for $t\geq0$.'+'\n'
    (ROOT/'tables'/'worked_replacement.tex').write_text(worked)
    text=r'''The four exceptional representative cubics are listed below. For
$0\leq t\leq1$, a coefficient sequence $(a,b,c,d)$ with $d<0$ gives
\[
a+bt+ct^2+dt^3=a+bt+t^2\bigl((c+d)+(-d)(1-t)\bigr)\geq0.
\]
In every listed case $a,b,c+d\geq0$.
\begin{align*}
'''
    text+='\n'.join(n+r',\ '+c+r':\quad &'+poly(co,'t')+r'\\' for n,c,co in exceptions)
    text+='\n'+r'\end{align*}'+'\n'
    (ROOT/'tables'/'exceptional_cubics.tex').write_text(text)
if __name__=='__main__':main()
