"""Turn exploratory floating candidates into exact rational certificates."""
import json,math
from fractions import Fraction as Q
from pathlib import Path
ROOT=Path(__file__).parent
D=json.load(open(ROOT/'mix_pool_explore.json'));P=D['pool']
def val(h):
 t,f,a,i,c,b=h['sig'];return [t,f,a,a+i,c,c+b]
def cert_valid(g,terms):
 out=[Q(0) for _ in range(6)]
 for term in terms:
  h=P[term['h']];u,v,w=[Q(term[k]) for k in ('u','v','w')]
  if min(u,v,w)<0 or w*w>u*v or len(h['edges'])>=g['edges']:return False
  vv=val(h)
  for j in range(6):out[j]+=vv[j]*([w,w,u,u,v,v][j])
 target=g['signature'];target=[target[0],target[1],target[2],target[2]+target[3],target[4],target[4]+target[5]]
 return all(out[j]>=target[j] for j in (0,1)) and all(out[j]<=target[j] for j in (2,3,4,5))
for row in D['records']:
 if row['status']!='mixture':continue
 sol=row['solution'];hs=row['hs'];z=sol['x'];n=len(hs);lam=sol['lam'];theta=(1+1/lam)/2
 gt=sum(row['signature'][:2])
 for denominator in (100,1000,10000,100000,1000000):
  terms=[]
  for j,k in enumerate(hs):
   factor=theta*gt/sum(P[k]['sig'][:2]);u0,v0,w0=[factor*z[j+a*n] for a in range(3)]
   if max(u0,v0,w0)<1e-7:continue
   u=Q(math.ceil(max(0,u0)*denominator),denominator)
   v=Q(math.ceil(max(0,v0)*denominator),denominator)
   w=Q(math.floor(max(0,w0)*denominator),denominator)
   if w*w>u*v:v=w*w/u
   terms.append(dict(h=k,u=str(u),v=str(v),w=str(w)))
  if cert_valid(row,terms):break
 else:raise RuntimeError(('cannot rationalize',row))
 row['certificate']=terms;del row['solution'];del row['hs']
# Make the elementary mixed-network certificates short and transparent.
for row in D['records']:
 if row['status']=='mixture' and row['signature']==[2,3,4,2,6,0]:
  row['certificate']=[dict(h=0,u='4/5',v='5/4',w='1'),dict(h=2,u='3/5',v='5/3',w='1')]
  assert cert_valid(row,row['certificate'])
 if row['status']=='mixture' and row['signature']==[3,2,6,0,4,2]:
  row['certificate']=[dict(h=0,u='5/4',v='4/5',w='1'),dict(h=1,u='5/3',v='3/5',w='1')]
  assert cert_valid(row,row['certificate'])
 forkey=['best_lam']
 for k in forkey:row.pop(k,None)
json.dump(D,open(ROOT/'mixture_certificate.json','w'),indent=2)
from collections import Counter
print(Counter(x['status'] for x in D['records']))
print('Exact rational mixtures:',sum(x['status']=='mixture' for x in D['records']))
