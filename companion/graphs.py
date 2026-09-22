"""Exact graph operations and subset-rank calculations for the replacement checker.
Signature order: trees, separating forests, A(2), I(2), C(2), B(2).
"""
from dataclasses import dataclass

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

def locally_reduced(a):
 """Local series/parallel-class condition in a pair/triple reduced host.
 This is distinct from global matroid admissibility (no loops or coloops).
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

def rank_table(n,edges):
    # Independent recurrence on partitions, not a DSU scan for each subset.
    N=1<<len(edges); part=[None]*N; part[0]=tuple(range(n));rank=[0]*N
    for mask in range(1,N):
        bit=mask&-mask; rest=mask^bit; u,v=edges[bit.bit_length()-1]
        p=part[rest];x,y=p[u],p[v]
        rank[mask]=rank[rest]+(x!=y)
        part[mask]=p if x==y else tuple(x if z==y else z for z in p)
    return rank

def identify(n,edges):
    return n-1,[(0 if u<2 else u-1,0 if v<2 else v-1) for u,v in edges]
