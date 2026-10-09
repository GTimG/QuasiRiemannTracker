#!/usr/bin/env python3
"""Exact coefficient discovery, not a proof oracle. Standard library only.
Generated rational coefficients will be checked by Lean polynomial identities.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import json
class Poly:
 def __init__(self,v=0):self.d=v if isinstance(v,dict) else {(0,0):Q(v)}
 def __add__(self,b):
  b=aspoly(b);d=self.d.copy()
  for k,v in b.d.items():d[k]=d.get(k,Q(0))+v
  return Poly({k:v for k,v in d.items() if v})
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
 def __sub__(self,b):return self+-aspoly(b)
 def __rsub__(self,b):return aspoly(b)+-self
 def __mul__(self,b):
  b=aspoly(b);d={}
  for (i,j),v in self.d.items():
   for (k,l),w in b.d.items():d[i+k,j+l]=d.get((i+k,j+l),Q(0))+v*w
  return Poly(d)
 __rmul__=__mul__
 def __truediv__(self,b):return self* (1/Q(b))
 def __pow__(self,n):
  ans=Poly(1)
  for _ in range(n):ans=ans*self
  return ans
 def sub(self,d,y):return sum(v*d**i*y**j for (i,j),v in self.d.items())
def aspoly(x):return x if isinstance(x,Poly) else Poly(x)
theta=Q(874957019421,10**12);ell=Q(11,3)-4*theta;kappa=2*theta-1
b=-(3*ell+1)*(36*ell**2-75*ell+19)/(3*(114*ell**2-159*ell-7))
lx=(1-ell-b)/2;ly=(1-ell+b)/2;h=(1+3*ell+b)/2;c=1/(3*kappa)
d=Poly({(1,0):Q(1)});y=Poly({(0,1):Q(1)});x=Q(1,2)-y
D=3-(1+2*c)*x;P=(2-2*c*x)*(1-x);J=(Q(5,6)-d)*D+d*P;a=(1+d)/2
base=a-theta-h/6-a*ly-ell/2+x*d*ell+h*(1-d/2)
F=-J*base-h*(Q(5,6)-d)*d*P/2
p=657*ell**3-954*ell**2+21*ell+20
dv=(5-9*ell)/(6*(3*ell+1));Av=(3*ell+1)*(414*ell**3-1191*ell**2+878*ell-29)/(4*(3*ell-5)*(114*ell**2-159*ell-7))
Dv=-(153*ell**2-201*ell-20)*p/(36*(3*ell-5)*(3*ell+1)*(114*ell**2-159*ell-7))
assert F.sub(d,Poly(0)).d==(Av*(d-dv)**2+Dv).d
shift=F.sub(d+Q(1,3),y)
assert all(shift.d.get((j,i),0)>=Q(bound,1000) for i,row in enumerate([(3,112,605),(41,269,434),(16,98,148)],1) for j,bound in enumerate(row))
assert Av>Q(1,5) and Dv>Q(5,10**12)
mat=[]
for lo,hi in [(Q(0),Q(1,4)),(Q(1,4),Q(1,3))]:
 g=F.sub(lo+(hi-lo)*d,y/2)
 beta=[[sum(g.d.get((k,l),Q(0))*Q(comb(i,k),comb(2,k))*Q(comb(j,l),comb(3,l)) for k in range(i+1) for l in range(j+1)) for j in range(4)] for i in range(3)]
 assert all(v>=Q(723,10**6) for row in beta for v in row)
 mat.append(beta)
obj={'theta':str(theta),'ell':str(ell),'b':str(b),'kappa0':str(kappa),'Av':str(Av),'Dv':str(Dv),'dv':str(dv),'shift_coefficients':[[str(shift.d.get((j,i),0)) for j in range(3)] for i in range(1,4)],'bernstein':[[[str(v) for v in row] for row in matrix] for matrix in mat]}
Path('audit/discovered-coefficients.json').write_text(json.dumps(obj,indent=2)+'\n')
print('Exact coefficient discovery passes; not an analytic proof or Lean certificate.')
