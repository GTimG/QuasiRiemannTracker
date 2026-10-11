#!/usr/bin/env python3
"""Exact conditional endpoint screen for a new local physical moment.

The encoded scalar inequalities are certified on whole rectangles. The new
analytic moment and its literal formal physical adapter are not certified here.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import tracker_weighted_numerator_audit as poly

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "numerics/results/local_moment_endpoint_audit.json"
INPUTS = (
    "framework/programs/fixed_strip/candidates/LOCAL_PHYSICAL_MOMENT_EXTENSION.md",
    "framework/programs/fixed_strip/candidates/JOINT_HIGH_ZERO_SQUARED_LABEL_PAYMENT.md",
    "tools/tracker_weighted_numerator_audit.py",
)
THETA = Q(4374433, 5000000)
ELL = Q(11, 3)-4*THETA
H = Q(3969737987, 5000000000)
Y, X = H-2*ELL, 1+ELL-H
KAPPA = 2*THETA-1
CAP = Q(2249, 500)
ROW_EXTENSION = Q(1, 10**10)
ROW_WINDOW = Q(1, 1000)
SHIFT_WINDOW = Q(1, 1000)
MARGIN = Q(1, 10**7)


def density_polynomials():
    delta, p = {(1, 0): Q(1)}, {(0, 1): Q(1)}
    one = poly.const(1)
    D = poly.add(poly.const(3), poly.smul(-1-Q(2)/(3*KAPPA), p))
    P = poly.smul(2, poly.mul(poly.add(one, poly.smul(-1, p)),
                             poly.add(one, poly.smul(-Q(1)/(3*KAPPA), p))))
    V = poly.add(poly.const(Q(5, 6)), poly.smul(-1, delta))
    J = poly.add(poly.mul(V, D), poly.mul(delta, P))
    RJ = poly.add(poly.mul(poly.add(one, poly.smul(-1, delta)), J),
                  poly.smul(Q(1, 2), poly.mul(poly.mul(delta, P), V)))
    return delta, p, J, RJ


def exponent_numerator(d, physical_capacity, margin):
    delta, p, J, RJ = density_polynomials()
    z0 = Q(17, 50)
    # Here d>=1/2>Y, so min(d,2Y-d)=2Y-d.
    common = poly.add(poly.const(Q(1, 2)+H*(z0-Q(1, 6))-Y/2-ELL/2
                                +d*(Q(1, 4)-z0)-THETA+margin),
                       poly.smul(Q(1, 2), delta),
                       poly.smul(ELL-(2*Y-d)/(2*physical_capacity),
                                 poly.mul(delta, p)))
    return poly.smul(-1, poly.add(poly.mul(J, common), poly.smul(3*d/4, RJ))), J


def certificates():
    box = (Q(0), Q(3, 4), Q(0), Q(1, 2))
    records = []
    for name, d, cap, margin in (
        ("local_upper_row", H, CAP, MARGIN),
        ("incumbent_below_local_window", H-ROW_WINDOW, 6*KAPPA, Q(1, 100000)),
        ("incumbent_lower_row", Q(1, 2), 6*KAPPA, Q(1, 1000)),
    ):
        numerator, J = exponent_numerator(d, cap, margin)
        leaves = poly.certify(numerator, box)
        coverage = poly.coverage(leaves, box)
        records.append({"name": name, "row_power": str(d),
                        "physical_capacity": str(cap), "saving": str(margin),
                        "coverage": coverage, "leaves": leaves})
    _, _, J, _ = density_polynomials()
    Jleaves = poly.certify(poly.add(J, poly.const(-Q(1, 10))), box)
    return records, {"lower_bound": "1/10", "leaves": Jleaves,
                     "coverage": poly.coverage(Jleaves, box)}


def local_interface_gates():
    lo, hi = H-ROW_WINDOW, H+ROW_EXTENSION
    nlo, nhi = 1-Y/lo, 1-Y/hi+SHIFT_WINDOW
    zlo, zhi = (1-2*nhi)/CAP, (1-2*nlo)/CAP
    assert Q(41, 100) < nlo <= nhi < Q(11, 25)
    assert Q(3, 100) < zlo <= zhi < Q(1, 25)
    assert (Q(9, 2)-CAP)*zhi < Q(1, 12500)
    assert hi*zhi < ELL
    assert hi < 2*Y
    # The scalar high exponent is affine in d with slope at most 2.
    assert MARGIN-2*ROW_EXTENSION > Q(9, 10**8)
    # Full original free Euler shifts: use the incumbent for t>=1/1000.
    # At positive old capacity the following reserve increases with t;
    # at capacity zero its derivative is 1/2. q<=delta/2 is retained.
    bmax = 1-2*nlo
    assert bmax < Q(9, 50) and bmax > 2*SHIFT_WINDOW
    shift_reserve = SHIFT_WINDOW/2-(bmax/CAP-(bmax-2*SHIFT_WINDOW)/Q(9, 2))/4
    assert shift_reserve > Q(3, 10000)
    return {
        "row_window": [str(lo), str(hi)], "free_shift_window": ["0", str(SHIFT_WINDOW)],
        "both_plain_exponents": [str(nlo), str(nhi)],
        "selected_prime_width": [str(zlo), str(zhi)],
        "local_moment_defect_upper": str((Q(9, 2)-CAP)*zhi),
        "local_moment_defect_allowed": "1/12500",
        "total_physical_slot_supply_margin": str(ELL-hi*zhi),
        "retained_endpoint_saving_after_row_extension": str(MARGIN-2*ROW_EXTENSION),
        "incumbent_payment_for_all_larger_free_shifts": {
            "delta_and_q_condition": "0<=q<=delta/2",
            "inequality": "-delta*t/2-q*z_old(t)/2 <= -q*z_new(0)/2 for t>=1/1000",
            "normalized_reserve_at_first_shift": str(shift_reserve),
            "old_capacity_range": [str(6*KAPPA), "9/2"],
            "monotonic_derivative_lower": str(Q(1, 2)-1/(2*6*KAPPA)),
        },
        "physical_adapter_verified_by_kernel": False,
    }


def geometry_and_feedback():
    assert X+Y == 1-ELL and H == 1-X+ELL
    assert THETA == Q(11, 12)-ELL/4
    assert Q(1, 6) < ELL < Q(1, 5)
    assert ELL < X < Y < 2*X and Y < Q(1, 2) < H < 2*Y
    assert H-4*ELL > 0
    floor_margin = THETA-(Q(51, 100)+H/3+Q(51, 100)*ELL)
    assert floor_margin > Q(1, 100)
    principal_w = Y/20-(1+H)/1000-Q(1, 4000)
    principal_z = H/600-Q(1, 1000)-Q(1, 4000)
    assert principal_w > 0 and principal_z > 0
    assert 6*KAPPA > CAP
    # Only the detector R_kappa varies; the new physical capacity is constant.
    derivative_upper = 3*H/4*Q(5, 12)*Q(1, 18)
    assert derivative_upper < Q(1, 50)
    assert Q(7, 10) < KAPPA < Q(3, 4)
    quartic = lambda x: 927*x**4-3135*x**3+2433*x**2+275*x-100
    assert quartic(Q(1, 6)) < 0 < quartic(ELL)
    assert -Q(9405, 25)+Q(4866, 6)+275 == Q(3549, 5) > 0
    return {"theta": str(THETA), "ell": str(ELL), "h": str(H), "x": str(X), "y": str(Y),
            "kappa_endpoint": str(KAPPA), "new_physical_capacity": str(CAP),
            "signal_boundary_relation": "theta=11/12-ell/4",
            "floor_saving": str(floor_margin),
            "principal_w_reserve": str(principal_w), "principal_z_reserve": str(principal_z),
            "detector_feedback_derivative_upper": str(derivative_upper),
            "supremum_feedback": "F_kappa-beta <= -24/25*(beta-theta)-margin, kappa=2beta-1",
            "exact_quartic_comparison": {"polynomial_at_candidate_ell": str(quartic(ELL)),
                "derivative_lower_bound_on_root_interval": "3549/5",
                "candidate_is_strictly_below_exact_incumbent": True},
            "proof_assembly_or_kernel_verified": False}


def report():
    certs, positivity = certificates()
    digest = lambda p: sha256(p.read_bytes()).hexdigest()
    return {"schema": "local-physical-moment-conditional-endpoint-v1",
            "status": "PASS_exact_conditional_endpoint",
            "script": "tools/local_moment_endpoint_audit.py", "script_sha256": digest(Path(__file__)),
            "input_sha256": {p: digest(ROOT/p) for p in INPUTS},
            "geometry": geometry_and_feedback(), "positive_density_denominator": positivity,
            "row_endpoint_certificates": certs, "local_physical_and_shift_gates": local_interface_gates(),
            "scope": "Whole-rectangle exact exponent inequalities and scalar local-interface, shift, geometry and feedback gates. Does not prove the analytic local moment, literal physical-state adapter, full family assembly or a record.",
            "new_moment_kernel_verified": False, "all_family_kernel_verified": False,
            "eligible_for_tracker_submission": False, "runs_Lean": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = report()
    if args.check:
        assert json.loads(OUTPUT.read_text()) == result, "Stale local moment endpoint screen"
    else:
        OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": result["status"], "theta": str(THETA),
                      "endpoint_rectangles": [len(r["leaves"]) for r in result["row_endpoint_certificates"]],
                      "beats_exact_quartic_algebraically": True,
                      "eligible_for_tracker_submission": False}, indent=2))


if __name__ == "__main__":
    main()
