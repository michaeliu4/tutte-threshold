"""Exact universal two-terminal replacement certificates.
Signature order: trees, separating two-forests, acyclic, incomparable acyclic,
almost totally cyclic, totally cyclic. Terminals are vertices 0,1.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
@dataclass
class Net:
 n:int
 edges:list
 sig:tuple
 expr:object
 @property
 def m(self):return len(self.edges)

def combine(a,b,op):
 if op=='P':
  mp={0:0,1:1};mp.update({j:a.n+j-2 for j in range(2,b.n)})
  n=a.n+b.n-2
 else:
  # a terminal1 becomes intermediate a.n, b terminal0 merges it,
  # b terminal1 is terminal1 of output.
  mp={0:a.n,1:1};mp.update({j:a.n+j-1 for j in range(2,b.n)})
  n=a.n+b.n-1
 ae=[(u if u!=1 or op=='P' else a.n,v if v!=1 or op=='P' else a.n) for u,v in a.edges]
 es=ae+[(mp[u],mp[v]) for u,v in b.edges]
 t,f,A,I,C,B=a.sig;u,h,D,J,F,E=b.sig
 if op=='S':sig=(t*u,t*h+f*u,A*D,A*D-(A-I)*(D-J)//2,C*F-(C-B)*(F-E)//2,B*E)
 else:sig=(t*h+f*u,f*h,A*D-(A-I)*(D-J)//2,I*J,C*F,C*F-(C-B)*(F-E)//2)
 return Net(n,es,sig,[op,a.expr,b.expr])

def components(n,es,omit):
 p=list(range(n))
 def rt(v):
  while p[v]!=v:v=p[v]
  return v
 for i,(u,v) in enumerate(es):
  if i in omit:continue
  x,y=rt(u),rt(v);p[x]=y
 return len({rt(v) for v in range(n)})

def admissible(a):
 """Necessary local condition inside a globally pair/triple reduced host.
 Boundary classes may be completed by the external network; internal classes
 must have size 2 or 3. At most 3 actual edges per boundary class.
 """
 es=a.edges+[(0,1)];m=len(es);assert components(a.n,es,set())==1
 assert all(components(a.n,es,{i})==1 for i in range(m))
 p=list(range(m))
 def rt(i):
  while p[i]!=i:i=p[i]
  return i
 for i in range(m):
  for j in range(i):
   if components(a.n,es,{i,j})>1:p[rt(i)]=rt(j)
 for i,(u,v) in enumerate(a.edges):
  parallel=[j for j,e in enumerate(a.edges) if set(e)=={u,v}]
  series=[j for j in range(m) if rt(i)==rt(j)]
  if {u,v}=={0,1}:
   if 1<=len(parallel)<=3:continue
  elif 2<=len(parallel)<=3:continue
  actual=len(series)-(m-1 in series)
  if m-1 in series:
   if 1<=actual<=3:continue
  elif 2<=actual<=3:continue
  return False
 return True

def replaces(g,h):
 if g.m<=h.m:return False
 gs,hs=g.sig,h.sig
 u=max(Fraction(gs[i],hs[i]) for i in (0,1))
 a=min(Fraction(gs[i],hs[i]) for i in (2,3) if hs[i])
 b=min(Fraction(gs[i],hs[i]) for i in (4,5) if hs[i])
 return u*u<=a*b

def pool_search():
 pool=[Net(2,[(0,1)],(1,1,2,0,2,0),'e')];done=set();records=[]
 while True:
  pending=[(pool[i].m+pool[j].m,i,j,op) for i in range(len(pool)) for j in range(i,len(pool)) for op in ['P','S'] if (i,j,op) not in done]
  if not pending:break
  _,i,j,op=min(pending);done.add((i,j,op))
  net=combine(pool[i],pool[j],op)
  record=dict(i=i,j=j,op=op,edges=net.m)
  if not admissible(net):record['status']='inadmissible'
  else:
   existing=next((k for k,h in enumerate(pool) if h.sig==net.sig and h.m<=net.m),None)
   replacement=next((k for k,h in enumerate(pool) if replaces(net,h)),None)
   if existing is not None:record.update(status='same_signature',replacement=existing)
   elif replacement is not None:record.update(status='reducible',replacement=replacement)
   else:
    record.update(status='new',replacement=len(pool));pool.append(net)
    print('new',len(pool)-1,'edges',net.m,'sig',net.sig,flush=True)
    if len(pool)>150:raise RuntimeError('Pool did not close by 150 states')
  records.append(record)
 return pool,records

if __name__=='__main__':
 pool,records=pool_search()
 out=dict(pool=[dict(n=h.n,edges=h.edges,sig=h.sig,expr=h.expr) for h in pool],records=records)
 json.dump(out,open(Path(__file__).parent/'network_reduction.json','w'),indent=2)
 print('CLOSED',len(pool),'states',len(records),'compositions')
