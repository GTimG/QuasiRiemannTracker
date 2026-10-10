"""Exact arithmetic model of the current QRH certificate; not a Lean proof."""
from fractions import Fraction as Q
from math import comb

ORIGINAL_THETA=Q(874957019421,10**12)
F_MARGIN=Q(5,10**12)
BERNSTEIN_FLOOR=Q(723,10**6)

class Poly:
    def __init__(self,value=0):
        self.d=value if isinstance(value,dict) else {(0,0):Q(value)}
    def __add__(self,other):
        other=aspoly(other);result=self.d.copy()
        for key,value in other.d.items():result[key]=result.get(key,Q(0))+value
        return Poly({key:value for key,value in result.items() if value})
    __radd__=__add__
    def __neg__(self):return Poly({key:-value for key,value in self.d.items()})
    def __sub__(self,other):return self+-aspoly(other)
    def __rsub__(self,other):return aspoly(other)+-self
    def __mul__(self,other):
        other=aspoly(other);result={}
        for (i,j),value in self.d.items():
            for (k,l),weight in other.d.items():
                key=i+k,j+l;result[key]=result.get(key,Q(0))+value*weight
        return Poly({key:value for key,value in result.items() if value})
    __rmul__=__mul__
    def __truediv__(self,other):return self*(1/Q(other))
    def __pow__(self,n):
        result=Poly(1)
        for _ in range(n):result=result*self
        return result
    def substitute(self,delta,y):return sum(value*delta**i*y**j for (i,j),value in self.d.items())

def aspoly(value):return value if isinstance(value,Poly) else Poly(value)

def parameters(theta,b_override=None):
    theta=Q(theta);ell=Q(11,3)-4*theta;kappa=2*theta-1
    b=-(3*ell+1)*(36*ell**2-75*ell+19)/(3*(114*ell**2-159*ell-7)) if b_override is None else Q(b_override)
    lx=(1-ell-b)/2;ly=(1-ell+b)/2;h=(1+3*ell+b)/2;c=1/(3*kappa)
    return dict(theta=theta,ell=ell,kappa=kappa,b=b,lx=lx,ly=ly,h=h,c=c)

def endpoint_polynomial(theta,b_override=None):
    p=parameters(theta,b_override);ell,b,kappa,lx,ly,h,c=(p[x] for x in ['ell','b','kappa','lx','ly','h','c'])
    delta=Poly({(1,0):Q(1)});y=Poly({(0,1):Q(1)});x=Q(1,2)-y
    D=3-(1+2*c)*x;P=(2-2*c*x)*(1-x);J=(Q(5,6)-delta)*D+delta*P;a=(1+delta)/2
    base=a-theta-h/6-a*ly-ell/2+x*delta*ell+h*(1-delta/2)
    return -J*base-h*(Q(5,6)-delta)*delta*P/2

def certificate(theta,b_override=None):
    p=parameters(theta,b_override);F=endpoint_polynomial(theta,b_override)
    delta=Poly({(1,0):Q(1)});y=Poly({(0,1):Q(1)})
    Av=F.d[(2,0)];dv=-F.d[(1,0)]/(2*Av);Dv=F.d[(0,0)]-Av*dv**2
    assert F.substitute(delta,Poly(0)).d==(Av*(delta-dv)**2+Dv).d
    shift=F.substitute(delta+Q(1,3),y)
    shifted=[[shift.d.get((j,i),Q(0)) for j in range(3)] for i in range(1,4)]
    matrices=[]
    for lo,hi in [(Q(0),Q(1,4)),(Q(1,4),Q(1,3))]:
        g=F.substitute(lo+(hi-lo)*delta,y/2)
        beta=[[sum(g.d.get((k,l),Q(0))*Q(comb(i,k),comb(2,k))*Q(comb(j,l),comb(3,l))
                   for k in range(i+1) for l in range(j+1)) for j in range(4)] for i in range(3)]
        matrices.append(beta)
    return dict(**p,F=F,Av=Av,dv=dv,Dv=Dv,shift=shifted,bernstein=matrices)

def validate(cert,margin=F_MARGIN,zeta=Q(1,10**14),t_cap=Q(1,10**16)):
    old_shift_bounds=[(3,112,605),(41,269,434),(16,98,148)]
    p=cert;e=p['ell'];b=p['b'];h=p['h'];lx=p['lx'];ly=p['ly'];M=1-e
    checks={
        'Av_gt_one_fifth':cert['Av']>Q(1,5),
        'Dv_gt_margin':cert['Dv']>margin,
        'square_region_vertex':Q(1,3)<cert['dv']<Q(5,6),
        'shift_positive':all(v>0 for row in cert['shift'] for v in row),
        'original_shift_lower_bounds':all(cert['shift'][i][j]>=Q(old_shift_bounds[i][j],1000) for i in range(3) for j in range(3)),
        'bernstein_floor':all(v>=BERNSTEIN_FLOOR for matrix in cert['bernstein'] for row in matrix for v in row),
        'kappa_lower':p['kappa']>=Q(13,18),
        'h_zeta_upper':h+zeta<=Q(17,20),
        'ell_bounds':0<e<Q(1,5),
        'ell_at_least_one_sixth':Q(1,6)<=e,
        'h_bounds':Q(4,5)<=h<=Q(9,10),
        'lx_bounds':0<=lx<=1,
        'ly_nonneg':0<=ly,
        'theta_lower':p['theta']>=Q(87,100),
        'mass_bounds':Q(49,100)+2*e<M<=1,
        'shape_positive':b>0,
        'count_coefficient_bounds':Q(4,9)<=p['c']<=Q(6,13),
        'floor_saving':(Q(51,100)-p['theta']-h/6-Q(51,100)*ly-e/2+e/100+h*Q(101,100)) < -Q(1,200),
        'large_saving_endpoint':(-3*b+15*e-3)/12 < -Q(7,100),
        'transport_geometry':ly/2-Q(13,75)*h-Q(1,50)>=Q(7,100),
        'C_theta_nonnegative':p['theta']+lx/2-1+h/6>=0,
        'transport_height_cap':h+zeta+t_cap<=Q(7,8),
    }
    return checks

def endpoint_margin(theta):
    p=parameters(theta);e=p['ell'];polynomial=657*e**3-954*e**2+21*e+20
    return -(153*e**2-201*e-20)*polynomial/(36*(3*e-5)*(3*e+1)*(114*e**2-159*e-7))

def floor_grid_theta(denominator,margin=F_MARGIN):
    low=(Q(87,100)*denominator).__floor__();high=(ORIGINAL_THETA*denominator).__ceil__()
    while high-low>1:
        mid=(low+high)//2
        if endpoint_margin(Q(mid,denominator))>margin:high=mid
        else:low=mid
    return Q(high,denominator)
