#!/usr/bin/env python3
"""Check the finite replacement certificate using only exact stdlib arithmetic."""
if not __debug__:
    raise SystemExit("Verification requires assertions: rerun without -O/-OO or PYTHONOPTIMIZE.")

from pathlib import Path
from fractions import Fraction as Q
import json
from graphs import Net, combine, rank_table, identify, locally_reduced
from polynomials import add, scale, expr_signature, poly_combine, axis_polynomials, compose_affine, evaluate
HERE = Path(__file__).resolve().parent

def key(r): return r['i'], r['j'], r['op']

def load():
    return json.loads((HERE/'representative_certificate.json').read_text()), json.loads((HERE/'reduced_certificate.json').read_text())

def slacks(row, polys):
    val = poly_combine(polys[row['i']],polys[row['j']],row['op'])
    sums = [(Q(0),)]*4
    for term in row['certificate']:
        A,I,C,B = polys[term['h']]
        u,v = Q(term['u']),Q(term['v'])
        sums = [add(s,c) for s,c in zip(sums,(scale(A,u),scale(add(A,I),u),scale(C,v),scale(add(C,B),v)))]
    A,I,C,B = val
    return [add(t,scale(c,-1)) for t,c in zip((A,add(A,I),C,add(C,B)),sums)]

def direct(g):
    A,B=axis_polynomials(rank_table(g.n,g.edges));I,C=axis_polynomials(rank_table(*identify(g.n,g.edges)))
    return A,I,C,B

def verify():
    rep,full=load(); dual=rep['dual_profile_map']
    assert dual == [0,2,1,4,3,6,5]
    assert rep['pool']==full['pool'] and len(rep['pool'])==7
    graphs=[Net(p['n'],p['edges'],tuple(p['sig']),p['expr']) for p in rep['pool']]
    polys=[expr_signature(p['expr']) for p in rep['pool']]
    for k,(g,p) in enumerate(zip(graphs,polys)):
        assert direct(g)==p
        ranks=rank_table(g.n,g.edges); identified=rank_table(*identify(g.n,g.edges))
        counts=lambda rs:sum(r==rs[-1] and mask.bit_count()==r for mask,r in enumerate(rs))
        assert g.sig==(counts(ranks),counts(identified),*[evaluate(a,2) for a in p])
        A,I,C,B=p
        assert polys[dual[k]]==(C,B,A,I)
        assert graphs[dual[k]].sig[:2]==(g.sig[1],g.sig[0])
    generated={}
    for row in rep['records']:
        k=key(row);i,j=sorted((dual[k[0]],dual[k[1]]));partner=(i,j,'P' if k[2]=='S' else 'S')
        assert k<partner and k not in generated and partner not in generated
        generated[k]=row['certificate']
        generated[partner]=[dict(h=dual[t['h']],u=t['v'],v=t['u'],w=t['w']) for t in row['certificate']]
    assert len(rep['records'])==21 and sum(len(r['certificate']) for r in rep['records'])==37
    assert len(generated)==42 and sum(map(len,generated.values()))==74
    assert len(full['records'])==56
    assert {key(r) for r in full['records']}=={(i,j,o) for i in range(7) for j in range(i,7) for o in ('S','P')}
    counts={'mixture':0,'new':0,'inadmissible':0}; positive=exceptional=0
    for row in full['records']:
        counts[row['status']]+=1
        g=combine(graphs[row['i']],graphs[row['j']],row['op'])
        assert direct(g)==poly_combine(polys[row['i']],polys[row['j']],row['op'])
        assert row['edges']==g.m
        if 'signature' in row: assert tuple(row['signature'])==g.sig
        if row['status']=='inadmissible':
            assert not locally_reduced(g);continue
        assert locally_reduced(g)
        if row['status']=='new':
            assert direct(g)==polys[row['equal']] and g.sig==graphs[row['equal']].sig;continue
        assert row['certificate']==generated[key(row)]
        budgets=[Q(0),Q(0)]
        for term in row['certificate']:
            h=graphs[term['h']];u,v,w=map(Q,(term['u'],term['v'],term['w']))
            assert min(u,v,w)>0 and w*w<=u*v and h.m<g.m
            budgets=[b+w*s for b,s in zip(budgets,h.sig[:2])]
        assert all(b>=s for b,s in zip(budgets,g.sig[:2]))
        for slack in slacks(row,polys):
            co=compose_affine(slack,2,1)
            if min(co)>=0:
                assert max(co)>0;positive+=1
            else:
                assert len(co)==4
                a,b,c,d=co
                assert a>=0 and b>=0 and c>=0 and d<0 and c+d>=0
                assert a+b+c+d>0;exceptional+=1
    assert counts=={'mixture':42,'new':6,'inadmissible':8}
    assert (positive,exceptional)==(160,8)
    result=dict(status='PASS',profiles=7,composition_cases=56,representative_replacements=21,representative_terms=37,replacements=42,terms=74,exact_slacks=168,nonnegative_shifted=160,exceptional_cubics=8,certified_interval=['2','3'])
    return result

if __name__=='__main__': print(json.dumps(verify(),indent=2))
