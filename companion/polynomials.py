"""Univariate exact polynomials, coefficients in increasing degree order."""
from fractions import Fraction as Q
from math import comb


def trim(p):
    p=list(map(Q,p))
    while len(p)>1 and p[-1]==0:p.pop()
    return tuple(p) or (Q(0),)


def add(*ps):
    r=[Q(0)]*max(map(len,ps))
    for p in ps:
        for j,a in enumerate(p):r[j]+=a
    return trim(r)


def scale(p,c):return trim([Q(c)*a for a in p])


def mul(p,q):
    r=[Q(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):r[i+j]+=a*b
    return trim(r)


def power(p,k):
    r=(Q(1),)
    for _ in range(k):r=mul(r,p)
    return r


def divide_x(p):
    assert p[0]==0
    return trim(p[1:])


def evaluate(p,x):
    r=Q(0)
    for a in reversed(p):r=r*x+a
    return r


def compose_affine(p,a,b):
    r=(Q(0),)
    for c in reversed(p):r=add(mul(r,(Q(a),Q(b))),(c,))
    return r


def bernstein(p,left,right):
    """Coefficients in degree-d Bernstein basis on [left,right]."""
    q=compose_affine(p,left,right-left);d=len(q)-1
    return [sum(q[i]*Q(comb(j,i),comb(d,i)) for i in range(j+1)) for j in range(d+1)]


def axis_polynomials(ranks):
    R=ranks[-1];m=len(ranks).bit_length()-1
    a=[0]*(R+1);b=[0]*(m-R+1)
    for mask,r in enumerate(ranks):
        corank=R-r;nullity=mask.bit_count()-r
        for j in range(corank+1):a[j]+=(-1)**(nullity+corank-j)*comb(corank,j)
        for j in range(nullity+1):b[j]+=(-1)**(corank+nullity-j)*comb(nullity,j)
    assert min(a)>=0 and min(b)>=0
    return trim(a),trim(b)


def poly_glue(a,b):
    A,I,C,B=a;aa,ii,cc,bb=b;z=(Q(-1),Q(1))
    alpha=divide_x(add(mul(A,aa),mul(A,ii),mul(I,aa),scale(mul(z,mul(I,ii)),-1)))
    beta=divide_x(add(mul(C,cc),mul(C,bb),mul(B,cc),scale(mul(z,mul(B,bb)),-1)))
    return alpha,beta


def poly_combine(a,b,op):
    A,I,C,B=a;aa,ii,cc,bb=b
    alpha,beta=poly_glue(a,b)
    if op=='S':return mul(A,aa),alpha,beta,mul(B,bb)
    assert op=='P'
    return alpha,mul(I,ii),mul(C,cc),beta


def expr_signature(ex):
    if ex=='e':return (Q(0),Q(1)),(Q(0),),(Q(0),Q(1)),(Q(0),)
    return poly_combine(expr_signature(ex[1]),expr_signature(ex[2]),ex[0])
