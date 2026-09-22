import sys,json
from dataclasses import asdict
from pathlib import Path
ROOT=Path(__file__).parent
from network_reduction import Net,combine,admissible
from cone_explore import solve
P=[Net(2,[(0,1)],(1,1,2,0,2,0),'e')];done=set();rec=[]
def data(h):return dict(n=h.n,edges=h.edges,sig=h.sig,expr=h.expr)
while True:
 pending=[(P[i].m+P[j].m,i,j,op) for i in range(len(P)) for j in range(i,len(P)) for op in ['P','S'] if (i,j,op) not in done]
 if not pending:break
 _,i,j,op=min(pending);done.add((i,j,op));g=combine(P[i],P[j],op);r=dict(i=i,j=j,op=op,edges=g.m)
 if not admissible(g):r['status']='inadmissible'
 else:
  equal=next((k for k,h in enumerate(P) if h.sig==g.sig and h.m<=g.m),None)
  if equal is not None:r.update(status='equal',equal=equal)
  else:
   hs=[k for k,h in enumerate(P) if h.m<g.m];sol=solve(data(g),[data(P[k]) for k in hs])
   if sol['lam']>=1.000001:r.update(status='mixture',hs=hs,solution=sol,signature=list(g.sig))
   else:r.update(status='new',equal=len(P),best_lam=sol['lam']);P.append(g);print('new',len(P)-1,g.m,g.sig,sol['lam'],flush=True)
 rec.append(r)
print('CLOSED',len(P),len(rec),flush=True)
json.dump(dict(pool=[data(x) for x in P],records=rec),open(ROOT/'mix_pool_explore.json','w'),indent=2)
