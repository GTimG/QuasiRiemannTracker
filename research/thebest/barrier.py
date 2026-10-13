#!/usr/bin/env python3
"""Exact algebraic obstruction for the unchanged Cycle25 B0.47 envelope.
Run with SymPy. This is not a Lean replay or a new zero-free theorem.
"""
import json
from pathlib import Path
import sympy as s

l, h = s.symbols('ell h', real=True)
p = 927*l**4 - 3135*l**3 + 2433*l**2 + 275*l - 100
k = (5-3*l)/6
d = k*(5-9*l)/(6*k+(6*k+2)*l)
c = (6*k-1)/(15*k-2)
v = s.Rational(5,6)-d
r = 1-d+d*c*v/(2*(v+d*c))
b = s.Rational(11,12)-l/4
f = (1+l)/2+d/2+h*(3*r/4-s.Rational(5,12))+d/2*(l-(h-4*l)/(12*k))
den_cubic = 234*l**3-753*l**2+525*l+100
factor = (21*l-40)/(24*(3*l**2-4*l-5)*den_cubic)
assert s.cancel(f-b-h*factor*p) == 0
lo, hi = s.Rational(16712007850680,10**14), s.Rational(16712007850682,10**14)
assert p.subs(l,lo)<0<p.subs(l,hi)
# Exact whole-interval sign bounds for 1/6 <= ell <= 1/5.
checks = {
 'quartic_derivative_lower': -s.Rational(9405,25)+s.Rational(4866,6)+275,
 'negative_linear_upper': s.Rational(21,5)-40,
 'negative_quadratic_upper': s.Rational(3,25)-s.Rational(4,6)-5,
 'positive_cubic_lower': -s.Rational(753,25)+s.Rational(525,6)+100,
 'delta_numerator_factor_lower': 5-s.Rational(9,5),
 'delta_denominator_factor_lower': 5-s.Rational(3,25)+s.Rational(4,6),
}
assert checks['quartic_derivative_lower']>0
assert checks['negative_linear_upper']<0
assert checks['negative_quadratic_upper']<0
assert checks['positive_cubic_lower']>0
assert checks['delta_numerator_factor_lower']>0
assert checks['delta_denominator_factor_lower']>0
# d=(5-3l)(5-9l)/(6*(5+4l-3l²)); d is positive and below 5/6.
assert s.cancel(d-(5-3*l)*(5-9*l)/(6*(5+4*l-3*l**2)))==0
assert s.expand(5*(5+4*l-3*l**2)-(5-3*l)*(5-9*l)-2*l*(40-21*l)) == 0
root = next(x for x in s.nroots(p,maxsteps=100) if abs(s.im(x))<1e-12 and s.Rational(1,6)<s.re(x)<s.Rational(1,5))
report = {
 'status':'exact symbolic identities and rational sign checks passed; not kernel verification',
 'upstream_commit':'d716ecaae80f7823a5b8314916364fdfa0d133fb',
 'identity':'F(ell,h,delta(ell),1/2)-b(ell) = h * factor(ell) * quartic(ell)',
 'factor':str(factor),
 'root_interval':[str(lo),str(hi)],
 'baseline_theta_approx':float(b.subs(l,root)),
 'sign_checks':{key:str(val) for key,val in checks.items()},
 'conclusion':'For ell0 < ell <= 1/5 and every h>0 the unchanged B0.47 envelope exceeds b(ell) at this admissible (delta,p).',
 'limits':'Obstruction to certification by this scalar envelope, not a lower bound for actual sums, and not a no-go for coherent probes or stronger moments.'
}
Path(__file__).with_name('barrier-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
