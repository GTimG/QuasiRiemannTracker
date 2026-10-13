#!/usr/bin/env python3
"""Local, conditional mixed-moment diagnostic; never a zero-free certificate."""
import json
from pathlib import Path

ell = 0.16712007850681
h = 0.793947597388136
y = 0.459707440374516
delta = 0.469344858698143
kappa = (5 - 3 * ell) / 6
p = 0.5
q = delta * p
C = 2 * (1-p) * (1-p/(3*kappa)) / (3-p-2*p/(3*kappa))
V = 5/6-delta
t = 1 + delta*C/(2*(V+delta*C))
r = (2*(1-p/(3*kappa))*t+p/(3*kappa)-p)/(3-p-2*p/(3*kappa))
m = t-r
R = 1-delta+delta*C*V/(2*(V+delta*C))
n = 1-y/h
z_I = (1-r)/2
z_P = (1-2*m)/(6*kappa)
z_A = (1-2*n)/(6*kappa)
current = .25+.75*R-q*z_A/2
critical_loss = 2*(current-R)
pointwise_loss = delta*n
result = {
    'status': 'LOCAL CONDITIONAL DIAGNOSTIC, NOT A ZERO-FREE BOUND',
    'ell': ell, 'delta': delta, 'kappa': kappa, 't': t,
    'inverse_witness_r': r, 'plain_witness_m': m,
    'reflected_numerator_n': n, 'row_count_R': R,
    'z_I': z_I, 'z_P': z_P, 'z_A': z_A,
    'current_numerator_exponent': current,
    'mixed_exponent_if_loss_zero': R,
    'critical_mixed_loss': critical_loss,
    'available_pointwise_mixed_loss': pointwise_loss,
    'required_gain_over_pointwise': pointwise_loss-critical_loss,
    'inverse_naive_length_with_marks': r+n+2*z_I,
    'plain_naive_length_with_marks': 2*m+n+6*kappa*z_P,
    'sixth_numerator_moment_naive_length': 3*n,
}
assert abs((1-delta*r-2*q*z_I)-R) < 1e-12
assert abs((1-2*delta*m-2*q*z_P)-R) < 1e-12
assert abs((1+5*t)/6-delta*t-R) < 1e-12
out = Path(__file__).resolve().parent
(out/'joint-moment.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
xs = [i*.006/240 for i in range(241)]
fig, ax = plt.subplots(figsize=(8, 4.8))
ax.plot(xs, [R+(pointwise_loss-x)/2 for x in xs],
        label='Conditional mixed estimate: R + (δn − ρ)/2')
ax.axhline(current, color='tab:orange', label='Current B0.41 exponent')
critical_gain = pointwise_loss-critical_loss
ax.axvline(critical_gain, color='tab:green', linestyle=':', label=f'Critical ρ = {critical_gain:.6f}')
ax.scatter([0], [R+pointwise_loss/2], color='tab:red', zorder=4,
           label='Available via pointwise numerator bound')
ax.set(xlabel='Hypothetical saving ρ over pointwise mixed loss δn', ylabel='Local numerator sum exponent',
       title='Conditional local mixed-moment test at the Cycle25 binding cell\nNot a zero-free bound')
ax.legend(fontsize=8, loc='upper right')
ax.grid(alpha=.2)
fig.tight_layout()
fig.savefig(out/'joint-moment.png', dpi=170)
