"""Exact exponent certificate for an independent weighted-numerator proposal.

The new analytic lemma must be proved separately. This script certifies only
the rational inequalities, with fixed ORIGINAL kappa=3/4, not kappa feedback.
Contour choice depends only on delta, never on a pointwise amplitude bin.
"""
from fractions import Fraction as F
from itertools import product
from math import comb
import json
import argparse
def add(*polys):
    out = {}
    for p in polys:
        for ij, a in p.items():
            out[ij] = out.get(ij, F(0)) + a
    return {ij: a for ij, a in out.items() if a}


def scale(a, p):
    return {ij: a * b for ij, b in p.items() if a * b}


def mul(p, q):
    out = {}
    for (i, j), a in p.items():
        for (k, l), b in q.items():
            ij = i + k, j + l
            out[ij] = out.get(ij, F(0)) + a * b
    return {ij: a for ij, a in out.items() if a}


def constant(a):
    return {(0, 0): F(a)}


def evaluate(p, d, x):
    return sum(a * d**i * x**j for (i, j), a in p.items())


def bernstein_bounds(p, box):
    """Convex hull bounds on a rectangle, after exact affine substitution."""
    d0, d1, x0, x1 = box
    n = max(i for i, j in p)
    m = max(j for i, j in p)
    power = {}
    for (i, j), a in p.items():
        for k in range(i + 1):
            for l in range(j + 1):
                value = (a * comb(i, k) * d0**(i-k) * (d1-d0)**k
                         * comb(j, l) * x0**(j-l) * (x1-x0)**l)
                power[k, l] = power.get((k, l), F(0)) + value
    values = [sum(power.get((k, l), F(0))
                  * F(comb(i, k), comb(n, k)) * F(comb(j, l), comb(m, l))
                  for k in range(i+1) for l in range(j+1))
              for i, j in product(range(n+1), range(m+1))]
    return min(values), max(values)


def certify(p, box, depth=0, leaves=None):
    if leaves is None:
        leaves = []
    lower, upper = bernstein_bounds(p, box)
    if lower >= 0:
        leaves.append((box, lower))
        return leaves
    assert depth < 46, ('Undecided positivity', box, lower, upper)
    assert upper >= 0, ('Negative rectangle', box, upper)
    d0, d1, x0, x1 = box
    # First reject actual negative points, avoiding huge subdivision on failure.
    for d, x in product((d0, (d0+d1)/2, d1), (x0, (x0+x1)/2, x1)):
        assert evaluate(p, d, x) >= 0, ('Negative value', d, x)
    if d1-d0 >= x1-x0:
        mid = (d0+d1)/2
        halves = [(d0, mid, x0, x1), (mid, d1, x0, x1)]
    else:
        mid = (x0+x1)/2
        halves = [(d0, d1, x0, mid), (d0, d1, mid, x1)]
    for half in halves:
        certify(p, half, depth+1, leaves)
    return leaves




def certificate(theta=F(10499,12000), ell=F(167,1000), b=F(43,500), margin=F(1,10000)):
    kappa=F(3,4); c=F(2,9); alpha=F(5,6); z0=F(17,50)
    lx=(1-ell-b)/2; ly=(1-ell+b)/2; h=1-lx+ell
    delta={(1,0):F(1)}; x={(0,1):F(1)}; q=mul(delta,x)
    D=add(constant(3),scale(-(1+4*c),x))
    P=mul(add(constant(2),scale(-4*c,x)),add(constant(1),scale(-1,x)))
    AP=mul(mul(add(constant(alpha),scale(-1,delta)),delta),P)
    J=add(mul(add(constant(alpha),scale(-1,delta)),D),mul(delta,P))
    RJ=add(mul(add(constant(1),scale(-1,delta)),J),scale(F(1,2),AP))
    # Direct numerator of E_old, before dividing by positive J.
    rest=add(constant((1-ly)/2-ell/2-h/6-theta),
             scale((1-ly)/2+h/2,delta),scale(ell,q))
    oldEJ=add(mul(rest,J),scale(h,RJ))
    correction=add(scale(h/4,add(J,scale(-1,RJ))),
                   scale((ly-h)/2,mul(delta,J)),
                   scale(-(2*ly-h)/(12*kappa),mul(q,J)))
    newEJ=add(oldEJ,correction)
    checks={}
    def require(name,value,strict=True):
        assert value>0 if strict else value>=0,(name,value)
        checks[name]=str(value)
    require('low comparison identity', theta-(F(11,12)-ell/4),False)
    require('improves public benchmark',F(874957019420098946128604623,10**27)-theta)
    require('original kappa admissible from 7/8', (1+kappa)/2-F(7,8),False)
    require('positive b',b)
    require('ell <= 1/5',F(1,5)-ell)
    require('X rescaled length',lx-ell)
    require('Y rescaled length',ly-ell)
    require('row rescaled length',1-3*ell)
    require('Gram domination',ly-ell-F(11,6)*b)
    require('row-count prime supply',ell/h-F(7,37))
    require('row extension supply',5*ell-h)
    require('reflected numerator short',2*ly-h)
    require('Y below intermediate cutoff',F(1,2)-ly)
    # On d in [1/2,h], requested numerator capacity decreases with d.
    maxcap=(4*ly-1)/(6*kappa)
    require('numerator prime supply at d=1/2',2*ell-maxcap)
    require('numerator capacity supply all d',ell-(2*ly-F(1,2))/(6*kappa))
    require('weighted frequency slope',F(3,4)*(1-F(3,4))+F(1,4)-z0)
    require('Euler-tail decay gap /delta',F(1,4)-1/(12*kappa))
    require('small rows',-(h*(z0-F(1,6))-ly/2+F(63,5000)))
    require('w residue margin',ly/20)
    require('z residue margin',h/600)
    for v in (F(0),ell):
        require('low rescaled tuple '+str(v),v-max(F(0),5*ell-1+v)/8,False)
    for i,exp in enumerate((-theta,-6*F(33,200),4-5*theta-6*F(33,200),1-F(19,20)-6*F(33,200))):
        require('Euler principal local '+str(i),-theta-exp,False)
    require('Euler defect A',-1-(4-6*theta-6*F(33,200)))
    require('Euler defect B',-1-(1-theta-F(19,20)-6*F(33,200)))

    def values(d,xv,row=h):
        j=evaluate(J,d,xv);r=evaluate(RJ,d,xv)/j
        old=(1+d)*(1-ly)/2-ell/2+xv*d*ell+h*(z0-F(1,6))+row*(r+d/2-z0)-theta
        new=old+row*((1-r)/4-d/2)+ly*d/2-xv*d*(2*ly-row)/(12*kappa)
        return old,new,j
    def genericE(d,qv,r,row):
        return (1+d)/2-theta+h*(z0-F(1,6))-(1+d)*ly/2-ell/2+qv*ell+row*(r+d/2-z0)
    require('floor bin',-genericE(F(1,50),F(1,100),F(1),h))
    for d in (F(1,50),F(3,4)):
        require('intermediate '+str(d),-genericE(d,d/2,F(76,75)-2*d/3,F(1,2)))
    for d,xv in product((F(0),F(1,3),F(2,5),F(3,4)),(F(0),F(1,4),F(1,2))):
        old,new,j=values(d,xv)
        assert evaluate(oldEJ,d,xv)==j*old
        assert evaluate(newEJ,d,xv)==j*new
    require('J positive',bernstein_bounds(J,(F(0),F(3,4),F(0),F(1,2)))[0])
    branches=[]
    for name,ej,box in [
        ('original numerator',oldEJ,(F(0),F(1,3),F(0),F(1,2))),
        ('weighted reflected numerator',newEJ,(F(1,3),F(3,4),F(0),F(1,2))),
    ]:
        polynomial=scale(-1,add(ej,scale(margin,J)))
        leaves=certify(polynomial,box)
        assert sum((v[1]-v[0])*(v[3]-v[2]) for v,_ in leaves)==(box[1]-box[0])*(box[3]-box[2])
        branches.append(dict(name=name,box=list(map(str,box)),leaf_count=len(leaves),
            leaves=[dict(box=list(map(str,v)),lower=str(lo)) for v,lo in leaves]))
    return dict(status='Exact exponent certificate only; requires the new weighted-numerator analytic lemma',
                theta=str(theta),ell=str(ell),b=str(b),lx=str(lx),ly=str(ly),h=str(h),
                kappa=str(kappa),endpoint_margin=str(margin),checks=checks,branches=branches)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output');args=parser.parse_args()
    result=certificate()
    if args.output:
        with open(args.output,'w') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('checks','branches')},indent=2))
    for branch in result['branches']:print('PASS:',branch['name'],'on',branch['box'],'with',branch['leaf_count'],'exact Bernstein rectangles')
    print('PASS:',len(result['checks']),'auxiliary rational checks')
