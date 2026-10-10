#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Zhongpai Gao
"""Exact continuous endpoint and recovery budgets; no analytic or kernel proof."""
import argparse
import json
from fractions import Fraction as Q
from hashlib import sha256
from math import comb
from pathlib import Path

# Polynomial arithmetic adapted from the author's MIT-licensed certificate
# package. Upstream analytic formulas and their attribution are in PROOF_NOTE.md.
def add(left, right):
    result = dict(left)
    for key, value in right.items():
        result[key] = result.get(key, Q(0)) + value
    return {key: value for key, value in result.items() if value}


def c(value):
    return {(0, 0): Q(value)}


def scale(poly, coefficient):
    return {key: value*coefficient for key, value in poly.items() if value*coefficient}


def mul(left, right):
    result = {}
    for (i, j), value in left.items():
        for (k, l), weight in right.items():
            key = i+k, j+l
            result[key] = result.get(key, Q(0)) + value*weight
    return {key: value for key, value in result.items() if value}


def ser(poly):
    return [{"delta_power": i, "y_power": j, "coefficient": str(value)}
            for (i, j), value in sorted(poly.items())]


ROOT = Path(__file__).resolve().parent
OWNER = "PROOF_NOTE.md"
REPORT = ROOT / "certificate.json"
PIN = "40844a7614b67840801e65b836b3da2e1f7ff029"
OLD = Q(874957019420098946128604623, 10**27)
THETA = Q(874957019420098946128603851334, 10**30)
FMARGIN, EMARGIN = Q(5, 10**27), Q(2, 10**27)
CENTRAL, ZETA, TCAP = Q(1, 10**27), Q(1, 10**29), Q(1, 10**31)


def power(p, n):
    result = c(1)
    for _ in range(n):
        result = mul(result, p)
    return result


def substitute(p, delta, y):
    result = {}
    for (i, j), coefficient in p.items():
        result = add(result, scale(mul(power(delta, i), power(y, j)), coefficient))
    return result


def exact_certificate():
    # Primary formulas: ProofCouncil geometry and continuous certificate;
    # Nielstron's refinement retains those formulas. This derives them anew.
    ell, kappa = Q(11, 3)-4*THETA, 2*THETA-1
    b = -(3*ell+1)*(36*ell**2-75*ell+19)/(3*(114*ell**2-159*ell-7))
    lx, ly, h = (1-ell-b)/2, (1-ell+b)/2, (1+3*ell+b)/2
    capacity = 1/(3*kappa)
    delta, y = {(1, 0): Q(1)}, {(0, 1): Q(1)}
    x = add(c(Q(1, 2)), scale(y, -1))
    d = add(c(3), scale(x, -(1+2*capacity)))
    p = mul(add(c(2), scale(x, -2*capacity)), add(c(1), scale(x, -1)))
    alpha_minus_delta = add(c(Q(5, 6)), scale(delta, -1))
    j = add(mul(alpha_minus_delta, d), mul(delta, p))
    a = scale(add(c(1), delta), Q(1, 2))
    base = add(scale(a, 1-ly), c(-THETA-h/6-ell/2+h))
    base = add(base, add(scale(mul(x, delta), ell), scale(delta, -h/2)))
    f = add(scale(mul(j, base), -1), scale(mul(mul(alpha_minus_delta, delta), p), -h/2))
    assert max(i for i, _ in f) <= 2 and max(k for _, k in f) <= 3
    av = (3*ell+1)*(414*ell**3-1191*ell**2+878*ell-29)/(4*(3*ell-5)*(114*ell**2-159*ell-7))
    dv = (5-9*ell)/(6*(3*ell+1))
    cubic = 657*ell**3-954*ell**2+21*ell+20
    offset = -(153*ell**2-201*ell-20)*cubic/(36*(3*ell-5)*(3*ell+1)*(114*ell**2-159*ell-7))
    f0 = {key: value for key, value in f.items() if key[1] == 0}
    assert f0 == add(scale(power(add(delta, c(-dv)), 2), av), c(offset))
    shifted = substitute(f, add(delta, c(Q(1, 3))), y)
    coefficients = [[shifted.get((i, k), Q(0)) for i in range(3)] for k in range(1, 4)]
    patches = []
    for lo, hi in [(Q(0), Q(1, 4)), (Q(1, 4), Q(1, 3))]:
        raw = substitute(f, add(c(lo), scale(delta, hi-lo)), scale(y, Q(1, 2)))
        patches.append([[sum(raw.get((k, l), Q(0))*Q(comb(i, k), comb(2, k))*Q(comb(z, l), comb(3, l))
                             for k in range(i+1) for l in range(z+1))
                         for z in range(4)] for i in range(3)])
    lower = [(3, 112, 605), (41, 269, 434), (16, 98, 148)]
    checks = {
        "square_coefficient": av > Q(1, 5), "strict_F_margin": offset > FMARGIN,
        "square_vertex": Q(1, 3) < dv < Q(5, 6),
        "shift_positive": all(v > 0 for row in coefficients for v in row),
        "shift_lower_bounds": all(coefficients[i][z] >= Q(lower[i][z], 1000) for i in range(3) for z in range(3)),
        "Bernstein_lower_bound": all(v >= Q(723, 10**6) for patch in patches for row in patch for v in row),
        "kappa_gate": kappa >= Q(13, 18), "outer_row_gate": h+ZETA <= Q(17, 20),
        "ell_range": 0 < ell < Q(1, 5), "ell_lower": ell >= Q(1, 6),
        "h_range": Q(4, 5) <= h <= Q(9, 10), "lx_range": 0 <= lx <= 1,
        "ly_nonnegative": ly >= 0, "principal_region": THETA >= Q(87, 100),
        "mass_range": Q(49, 100)+2*ell < 1-ell <= 1, "shape_positive": b > 0,
        "capacity_range": Q(4, 9) <= capacity <= Q(6, 13),
        "floor_saving": Q(51, 100)-THETA-h/6-Q(51, 100)*ly-ell/2+ell/100+h*Q(101, 100) < -Q(1, 200),
        "large_range_saving": (-3*b+15*ell-3)/12 < -Q(7, 100),
        "transport_geometry": ly/2-Q(13, 75)*h-Q(1, 50) >= Q(7, 100),
        "principal_exponent_nonnegative": THETA+lx/2-1+h/6 >= 0,
        "transport_height_gate": h+ZETA+TCAP <= Q(7, 8),
        # Geometry assumptions used by the full low/principal proof sources,
        # rather than only by the endpoint polynomial.
        "strict_principal_region": THETA > Q(87, 100),
        "ly_principal_lower": ly >= Q(2, 5),
        "ly_low_upper": ly < 1,
        "low_remote_scale_gap": lx-ell > 0,
        "low_gram_admissible_gap": 2*lx-ly-ell > 0,
        "ordered_physical_lengths": ly >= lx,
        "slot_mass_identity": (1-ell)+ell == 1,
        "low_gram_identity": lx+b/6 == 2*(THETA+lx/2-1+h/6),
        "strict_normalized_exponent": THETA+lx/2-1+h/6 > 0,
        "certificate_denominator_signs": 3*ell-5 < 0 < 3*ell+1 and 114*ell**2-159*ell-7 < 0,
        "principal_w_reserve": ly/20-(1+h)/1000-Q(1, 3000) > 0,
        "principal_z_reserve": h/600-Q(1, 1000)-Q(1, 3000) > 0,
    }
    assert len(checks) == 34 and all(checks.values()), checks
    expense = 19*TCAP+2*ZETA
    assert FMARGIN*Q(2, 5) == EMARGIN and expense < CENTRAL < EMARGIN
    assert Q(18)+Q(185, 2000) < 19 and 0 < ZETA <= Q(1, 48)
    assert OLD-THETA == Q(771666, 10**30)
    # Restricting to the old central budget cannot validate the new endpoint.
    assert offset < Q(5, 10**24)
    assert 2*Q(1, 10**26)+19*Q(1, 10**28) > EMARGIN
    geometry = dict(ell=ell, b=b, kappa=kappa, lx=lx, ly=ly, h=h, capacity=capacity)
    return dict(geometry={k: str(v) for k, v in geometry.items()}, checks=checks,
                endpoint_polynomial=ser(f), square=dict(A=str(av), vertex=str(dv), offset=str(offset)),
                shifted_coefficients=[[str(v) for v in row] for row in coefficients],
                Bernstein_patches=[[[str(v) for v in row] for row in patch] for patch in patches],
                F_margin=str(FMARGIN), E_margin=str(EMARGIN), central_budget=str(CENTRAL),
                zeta=str(ZETA), t_cap=str(TCAP), maximum_central_expense=str(expense),
                central_expense_ratio=str(expense/CENTRAL), old_budget_negative_control=True)


def report():
    digest = lambda p: sha256(p.read_bytes()).hexdigest()
    result = exact_certificate()
    return dict(status="PASS_EXACT_TRACKER_SLACK_CONTROLS", theta=str(THETA),
                reference_theta=str(OLD), strict_difference=str(OLD-THETA),
                tracker_commit=PIN, script_sha256=digest(Path(__file__)),
                input_sha256={p: digest(ROOT/p) for p in (OWNER,)},
                certificate=result, arithmetic="Exact rational polynomial and Bernstein identities",
                scope="Continuous endpoint and finite recovery-budget arithmetic only. Analytic source re-instantiation and the complete nonvanishing proof remain unverified.",
                analytic_bound_certified=False, new_arithmetic_gain_proved=False,
                runs_Lean=False, runs_kernel_replay=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = report()
    if args.check:
        assert json.loads(REPORT.read_text()) == data, "Report stale; review before regeneration"
    else:
        REPORT.write_text(json.dumps(data, indent=2, sort_keys=True)+"\n")
    print(json.dumps({key: data[key] for key in ("status", "theta", "strict_difference", "runs_Lean", "analytic_bound_certified")}, indent=2))


if __name__ == "__main__":
    main()
