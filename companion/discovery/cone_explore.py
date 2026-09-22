"""Exploratory convex mixture replacement; numerical search, not a certificate."""
import json,numpy as np
from pathlib import Path
ROOT=Path(__file__).parent
from scipy.optimize import minimize
P=json.load(open(ROOT/'prior_network_reduction.json'))['pool']
def vec(h):
 t,f,a,i,c,b=h['sig'];return np.array([t,f,a,a+i,c,c+b],float)/(t+f)
def solve(g,hs):
 G=vec(g);H=np.array([vec(h) for h in hs]);n=len(hs)
 # u[n],v[n],w[n] >=0, w^2<=u*v, lambda. Tree lower covers lambda*G.
 L=np.zeros((6,3*n+1));R=np.zeros(6)
 L[:2,2*n:3*n]=H[:,:2].T;L[:2,-1]=-G[:2]
 L[2:4,:n]=-H[:,2:4].T;R[2:4]=G[2:4]
 L[4:6,n:2*n]=-H[:,4:6].T;R[4:6]=G[4:6]
 def fun(x):return -x[-1]
 def jac(x):j=np.zeros(len(x));j[-1]=-1;return j
 def con(x):
  u,v,w=x[:n],x[n:2*n],x[2*n:3*n];return np.r_[L@x+R,u+v-np.sqrt((u-v)**2+4*w*w)]
 def cjac(x):
  u,v,w=x[:n],x[n:2*n],x[2*n:3*n];d=np.sqrt((u-v)**2+4*w*w);d=np.maximum(d,1e-20)
  J=np.zeros((n,3*n+1));k=np.arange(n);J[k,k]=1-(u-v)/d;J[k,k+n]=1+(u-v)/d;J[k,k+2*n]=-4*w/d
  return np.vstack([L,J])
 x=np.ones(3*n+1)*(.1/n);x[2*n:3*n]*=.5;x[-1]=0
 res=minimize(fun,x,jac=jac,bounds=[(0,None)]*len(x),constraints=[dict(type='ineq',fun=con,jac=cjac)],method='SLSQP',options=dict(ftol=1e-11,maxiter=1000))
 return dict(lam=float(res.x[-1]),success=bool(res.success),minimum_constraint=float(min(con(res.x))),x=res.x.tolist())
if __name__=='__main__':
 pool=[];out=[]
 for k,g in enumerate(P):
  hs=[P[j] for j in pool if len(P[j]['edges'])<len(g['edges'])]
  r=solve(g,hs) if hs else {'lam':0};print(k, r['lam'],flush=True)
  if r['lam']<1-1e-8:pool.append(k)
  out.append(dict(k=k,from_pool=pool[:],result=r))
 print('SURVIVORS',pool)
 json.dump(out,open(ROOT/'cone_explore.json','w'),indent=2)
