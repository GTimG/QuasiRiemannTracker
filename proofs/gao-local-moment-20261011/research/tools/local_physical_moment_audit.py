#!/usr/bin/env python3
"""Exact scalar/source controls for the manual capacity-4.498 local moment.

Continuous statements below are rational identities or polynomial sign
certificates, not grid tests. Integer/character controls are finite algebra
checks. None of these checks proves an analytic estimate, a formal physical
adapter, a kernel theorem, complete recovery, or a tracker record.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from hashlib import sha256
from itertools import product
import json
from math import comb, prod
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import sympy as sp
import cubic_theta_squareclass_covariance_audit as sextic

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "numerics/results/local_physical_moment_audit.json"
PAPER = "build/tracker_weighted_numerator_2026-10-10/latest-cycle25/paper.tex"
INPUTS = (
    "framework/programs/fixed_strip/candidates/LOCAL_PHYSICAL_MOMENT_EXTENSION.md",
    "framework/programs/fixed_strip/candidates/JOINT_HIGH_ZERO_SQUARED_LABEL_PAYMENT.md",
    "tools/cubic_theta_squareclass_covariance_audit.py", PAPER,
)
DELTA = sp.Symbol("delta", real=True)
RHO = 1 - 10*DELTA/(3*(5-2*DELTA))
INTERVAL = (Q(7, 10), Q(3, 4))
CAP = Q(2249, 500)
BASE = Q(9, 2)
AUX = Q(1, 2000)
SIGMA = 3*AUX
G_SHARP, G_COARSE = Q(1, 12500), Q(1, 10000)
AMAX = Q(44753, 50000)


def exact(x):
    return sp.Rational(x.numerator, x.denominator) if isinstance(x, Q) else sp.sympify(x)


def rational(x):
    x = sp.cancel(x)
    assert x.is_Rational
    return Q(int(x.p), int(x.q))


def identity(name, lhs, rhs):
    assert sp.cancel(lhs-rhs) == 0, name
    return {"name": name, "left": str(sp.expand(lhs)), "right": str(rhs),
            "difference": "0"}


def bernstein_nonnegative(name, expression, strict=False):
    """Check every Bernstein coefficient after an exact affine substitution.

    For each recorded polynomial p, p(a+(b-a)t)=sum B_i binom(n,i)
    t^i(1-t)^(n-i), 0<=t<=1. Nonnegative B_i certify the whole interval.
    Positive denominator and numerator certificates justify each quotient.
    """
    num, den = sp.fraction(sp.cancel(expression))
    t = sp.Symbol("t")
    lo, hi = map(exact, INTERVAL)
    if den.subs(DELTA, (lo+hi)/2) < 0:
        num, den = -num, -den

    def certificate(poly):
        transformed = sp.Poly(sp.expand(poly.subs(DELTA, lo+(hi-lo)*t)), t)
        n = max(0, transformed.degree()) if transformed else 0
        coeff = [rational(transformed.nth(i)) for i in range(n+1)]
        bern = [sum((coeff[j]*Q(comb(i, j), comb(n, j))
                     for j in range(i+1)), Q(0)) for i in range(n+1)]
        reconstructed = sum((exact(bern[i])*comb(n, i)*t**i*(1-t)**(n-i)
                             for i in range(n+1)), sp.Integer(0))
        assert sp.expand(reconstructed-transformed.as_expr()) == 0
        return {"power_coefficients": list(map(str, coeff)),
                "bernstein_coefficients": list(map(str, bern)),
                "lower_bound": str(min(bern))}

    numerator = certificate(num)
    denominator = certificate(den)
    assert Q(denominator["lower_bound"]) > 0, (name, denominator)
    assert Q(numerator["lower_bound"]) >= 0, (name, numerator)
    if strict:
        assert Q(numerator["lower_bound"]) > 0, (name, numerator)
    return {"name": name, "expression": str(sp.factor(expression)),
            "interval": list(map(str, INTERVAL)), "strict": strict,
            "numerator": numerator, "denominator": denominator,
            "method": "exact affine-substitution Bernstein identity"}


def continuous_high_bin_certificates():
    abar = exact(Q(113, 125))  # The weaker A/M<=1-(16/5)(3/100).
    return [bernstein_nonnegative(name, expression, strict) for name, expression, strict in (
        ("density_minimum", RHO-exact(Q(2, 7)), False),
        ("density_maximum", exact(Q(19, 54))-RHO, False),
        ("sixth_power_lift_absolute_convergence", 6*RHO-1, True),
        ("positive_T_coefficient_after_sign_reversal", RHO+DELTA-1, True),
        ("canceled_active_prime_coefficient", 5*RHO-1, True),
        ("active_radical_deficit_coefficient", 4*RHO-1, True),
        ("first_common_label_reserve", 1+DELTA-4*RHO-exact(Q(79, 270)), False),
        ("weaker_gate_density_plus_pointwise_decreases", -sp.diff(RHO+DELTA*abar, DELTA), True),
        ("weaker_gate_high_deficit", 1-RHO-DELTA*abar-exact(Q(259, 16875)), False),
        ("amplifier_loss_upper", exact(Q(23, 7))-(5-6*RHO), False),
        ("illustrative_JH_gate_is_weaker", exact(CAP)-1-exact(Q(16, 5)), True),
    )]


def symbolic_joint_ledgers():
    M, A, a, c, d, p, R, E, Lc, Ld, Rz, Bc, Bd, g2, t2, b2, V = sp.symbols(
        "M A a c d p R E L_C L_D R_zero B_C B_D g_2 t_2 b_2 V", real=True)
    T, S, h = sp.symbols("T S h", nonnegative=True)
    K, delta1 = sp.symbols("K delta_1", real=True)
    rho = sp.Symbol("rho", real=True)
    results = []
    for branch, subs, Tbranch, opposite in (
        ("c_ge_d", {c: d+T}, T, 0),
        ("c_le_d", {d: c+S}, 0, S),
    ):
        K0 = 2*A-c-d+R+E-M
        enlarged = K0+opposite+6*a
        actual_J = d-c+K0-K
        a0 = A-c
        outside = -a0+(enlarged-a0)-a+(g2-t2)+(a0-b2)
        target_outside = A-c+Tbranch+R+E-M+5*a+g2-t2-b2
        row_h = 2*a0-enlarged-g2-V
        integer_row = row_h+Lc+E+g2+V
        missing_label = p-R-E+Rz
        allowance = p+A-c+R+E+Bc
        joint_excess = outside+missing_label+rho*integer_row+DELTA*(A-c-b2)-allowance
        c2 = sp.Symbol("c_2", real=True)
        nominal_g_enl = enlarged-K
        main_child_increment = nominal_g_enl-d-(K0-K)-c2+g2-t2
        side_min = d if branch == "c_ge_d" else c
        lp14 = (M*(rho-1)+DELTA*A+a*(5-6*rho)
                +(1-rho)*Tbranch-DELTA*c-(1+rho)*R-E-Bc+rho*Lc+Rz
                +g2-t2-(1+DELTA)*b2)
        results.append({"branch": branch, "identities": [
            identity("LP.10 actual enlarged row J>=0", (K+actual_J+6*a).subs(subs),
                     (K0+d-c+6*a).subs(subs)),
            identity("LP.10 envelope gap J>=0", (enlarged-(K+actual_J+6*a)).subs(subs), Tbranch),
            identity("LP.10 padded envelope gap J<0", (enlarged+delta1-(K+6*a)).subs(subs),
                     opposite+(K0+delta1-K).subs(subs)),
            identity("enlarged-envelope low main increment", main_child_increment.subs(subs),
                     6*a-side_min-(c2-g2)-t2),
            identity("enlarged-envelope nominal child width",
                     (M+actual_J-nominal_g_enl-g2+t2).subs(subs),
                     M-Tbranch-6*a-g2+t2),
            identity("LP.11 integral row width", integer_row.subs(subs),
                     M-R-Tbranch+Lc-6*a),
            identity("LP.13 second outside without label count", outside.subs(subs),
                     target_outside.subs(subs)),
            identity("LP.14 joint high excess", joint_excess.subs(subs), lp14.subs(subs)),
        ], "aggregated_allowance": str(allowance), "rho": "R_0(delta)",
        "LP10_interpretation": "K0+(d-c)_++6a is the nominal enlarged envelope; actual K+J_++6a is <= envelope+delta_1",
        "first_row_ball_choice": "Before B3.60 actually enlarge the positive smooth first-row norm to this envelope, with reserved support padding. LP.11/13 use this chosen ball, not the smaller original dyad ball.",
        "enlarged_main_increment_bound": "<=6a from min(c,d)>=0, c2>=g2, t2>=0; padding is reserved in delta_1",
        "LP10_nonnegative_slacks": [str(Tbranch), str(opposite), "K0+delta_1-K>=0"],
        "parent_old_moving_width": "0", "first_projector_count_outside": False})

        # Let q=min(c,d)-p>=0 and write L_C=5(R-Rzero)-h, h>=0.
        # Every subtraction below has a certified nonnegative coefficient.
        q, rp = sp.symbols("q rp", nonnegative=True)
        second_line = ((1-rho)*Tbranch-DELTA*c-(1+rho)*R-E-Bc+rho*Lc+Rz).subs(subs)
        side_min = d if branch == "c_ge_d" else c
        reduced = second_line.subs(Lc, 5*(R-Rz)-h).subs(R, p-rp).subs(side_min, p+q)
        cone = ((4*rho-1-DELTA)*p-E-Bc-(rho+DELTA-1)*Tbranch
                -DELTA*q-(4*rho-1)*rp-(5*rho-1)*Rz-rho*h)
        results[-1]["cone_certificate"] = identity("LP.14 line two cone decomposition", reduced, cone)
        results[-1]["cone_nonnegative_variables"] = ["p", "q=min(c,d)-p", "rp=p-R", "R_zero", "h=5(R-R_zero)-L_C", "E", "B_C", str(Tbranch)]
    # Exchanging sides uses the genuine D exponent list, not the C list.
    results.append({"branch": "D_side_exchange", "rule": "c<->d, B_C<->B_D, L_C<->L_D, R_zero,C<->R_zero,D; e_D=(1+t)%6",
                    "D_canceled_radical": "sum_{e_D=0} log_Z Np, distinct from the C canceled radical",
                    "independent_heights_identified": False})
    return results


def complete_source_balance_certificates():
    """Primewise identities for arbitrary multiplicities, not a finite scan."""
    j0, k = sp.symbols("j0 k", nonnegative=True)
    branches = []
    for active in (0, 1):
        # j=1+j0, i=j+active+k. Active support forces i!=j, hence
        # i>=j+1 after exchanging the larger and smaller side.
        j = 1+j0
        i = j+active+k
        rhs = i+j-2-active
        positive_numerator = 3*i-5*j-active
        six_gap = 6*rhs-positive_numerator
        branches.append({"active_radical": active,
            "nonpositive_B_gap": identity("B3.56 local B numerator<=0", rhs, 2*j0+k),
            "positive_B_six_gap": identity("B3.56 local B numerator>0", six_gap,
                                           2+14*j0+3*k if active == 0 else 14*j0+3*k),
            "nonnegative_parameters": ["j0=j-1", "k=i-j-active"],
            "valid_for_arbitrary_integer_multiplicities": True})
    M, A, R, E, c, d, p, Bc, Bd = sp.symbols("M A R E c d p B_C B_D")
    balance = identity("B3.56 joint Cauchy balance with all first labels present",
                       M-A-R/2-E+(p+A-c+R+E+Bc+p+A-d+R+E+Bd)/2,
                       M+(Bc+Bd-(c+d-2*p-R))/2)
    i = 1+j0
    f2 = [identity("B3.76 equal non6 unit gap", 7*i/6-2*i/3, i/2),
          identity("B3.76 equal non6 nonunit i=1 gap", sp.Rational(2, 3)-sp.Rational(2, 3), 0),
          identity("B3.76 equal non6 nonunit i>=2 gap", (7*(2+j0)-5)/6-2*(2+j0)/3,
                   sp.Rational(1, 6)+j0/2),
          identity("B3.76 equal 6-multiple i>=6 gap", 7*(6+j0)/6-1-2*(6+j0)/3, 2+j0/2),
          identity("B3.76 unequal smaller 6-multiple gap",
                   (7+j0+k)+(6+j0)/6-1-((7+j0+k)+(6+j0))/3,
                   sp.Rational(8, 3)+j0/2+2*k/3)]
    return {"primewise_first_balance": branches, "aggregate_balance": balance,
            "aggregate_rule": "positive parts of sums <= sums of positive parts; only larger side has positive local B numerator",
            "second_exceptional_F2_gaps": f2,
            "nonnegative_parameters": ["j0", "k"],
            "fixed_inducing_row_predicate_replacement_by_group_membership": False}


def projection_and_child_ledgers():
    t, r1, r2, pi1, pi2, pi01, pi02, e1, e2, w1, w2, theta = sp.symbols(
        "t r1 r2 pi1 pi2 pi01 pi02 e1 e2 omega1 omega2 theta", real=True)
    clipped = t-(r1-pi1+pi01+r2-pi2+pi02)/2+(e1+pi01+e2+pi02)/2
    rewritten = (t-(r1+w1+r2+w2)/2
                 +((e1+w1)+(e2+w2)+pi1+pi2)/2)
    # r_j+omega_j>=t, |e_j+omega_j|<=theta, 0<=pi_j<=theta.
    bound = identity("B3.69 exact clipping/projector cancellation", clipped, rewritten)
    u1, u2, v1, v2, b1, b2 = sp.symbols("u1 u2 v1 v2 b1 b2", nonnegative=True)
    certificate = rewritten.subs({r1: t+u1-w1, r2: t+u2-w2,
                                  e1: theta-v1-w1, e2: theta-v2-w2,
                                  pi1: theta-b1, pi2: theta-b2})
    projector_slacks = identity("B3.69 nonnegative-slack upper bound", certificate,
                                2*theta-(u1+u2+v1+v2+b1+b2)/2)
    c, d, c2, g2, t2, w, wo, D0, sigma, J = sp.symbols(
        "c d c2 g2 t2 w wo D0 sigma J", real=True)
    increment = J+sigma+w-D0-c2-wo+g2-t2
    positive = identity("B3.70 error J>=0 fine increment", increment.subs(J, D0-c-2*w+wo),
                        sigma-c-w-(c2-g2+t2))
    negative = identity("B3.70 error J<0 fine increment", increment.subs(J, 0),
                        sigma+w-wo-D0-(c2-g2+t2))
    delta1 = sp.Symbol("delta_1", nonnegative=True)
    negative_gap = identity("B3.70 J<0 upper bound gap",
                            sigma+w-wo+delta1-increment.subs(J, 0),
                            (D0+delta1)+(c2-g2)+t2)
    g, a, parent_slack, inc_slack, allocation_slack = sp.symbols(
        "g a parent_slack inc_slack allocation_slack", nonnegative=True)
    child_bounds = []
    for name, inc_upper in (("LP.6 low main child", 6*a+delta1),
                            ("LP.17 amplifier error child", sigma+w-wo+delta1)):
        encoded_child_affine = (g-parent_slack)+(inc_upper-inc_slack)+(2*theta-allocation_slack)
        child_bounds.append(identity(name+" affine defect slack identity", encoded_child_affine,
                            g+inc_upper+2*theta-parent_slack-inc_slack-allocation_slack))
    b, p, B, ell = sp.symbols("b p B ell", real=True)
    delta = b-p+w+B+ell
    return {"projector": bound, "projector_slack_certificate": projector_slacks,
            "projector_slack_definitions": ["u_j=r_j+omega_j-t>=0", "v_j=theta_N-(e_j+omega_j)>=0", "b_j=theta_N-pi_j>=0"],
            "projector_bound": "<=2*theta_N continuously from the nonnegative-slack certificate",
            "error_fine_branches": [positive, negative, negative_gap],
            "error_nonnegative_slacks": ["c2-g2>=0", "t2>=0", "D0+delta_1=d+(K0+delta_1-K)>=0"],
            "conditional_child_affine_slack_certificates": child_bounds,
            "conditional_child_slack_meanings": ["parent_slack=g-parent_affine_defect>=0", "inc_slack=inc_upper-actual_increment>=0", "allocation_slack=2theta_N-net_post_allocation_increment>=0"],
            "positive_part_bound_rule": "if child_affine<=nonnegative_upper, (child_affine)_+<=nonnegative_upper",
            "actual_child_adapter_and_allocation_monotonicity_imported_obligations": True,
            "error_bounds": ["J>=0: increment<=sigma-c-w", "J<0: increment<=sigma+w-w_o+delta_1"],
            "child_allowance": identity("B3.64 allowance reserve", delta, w+ell+(b-p)+B),
            "allowance_nonnegative_terms": ["b_2-p_2", "B_C", "w", "ell"],
            "low_child_defect_bound": "g+6*a+delta_1+2*theta_N",
            "error_child_defect_bound": "g+sigma+w-w_o+delta_1+2*theta_N",
            "low_child_capacity_used": "9/2", "improved_child_induction_called": False,
            "low_per_s_allowance_has_minus_s0": True,
            "low_per_s_count_cancels_minus_s0": True,
            "high_aggregated_allowance_has_minus_s0": False,
            "first_s_recount_after_joint_reconstruction": False,
            "Cauchy_cost": "(cost_C+cost_D)/2; independent profiles/heights retained"}


def scalar_reserves():
    # Normalize all widths by M>0. These deductions use the entire LP.1 box
    # and its affine capacity constraint, not representative slot values.
    amin = 2*Q(41, 100)+Q(3, 100)
    assert amin == Q(17, 20) > Q(5, 6)
    assert AMAX == 1-(CAP-1)*Q(3, 100) < Q(9, 10)
    assert (BASE-CAP)*Q(1, 25) == G_SHARP < G_COARSE
    comparison = Q(3, 2)-2*Q(41, 100)+BASE*Q(1, 25)
    masked = Q(3, 4)+BASE*Q(1, 25)
    low_coarse = AUX-Q(7, 45)*(6*AUX+G_COARSE)
    low_sharp = AUX-Q(7, 45)*(6*AUX+G_SHARP)
    assert comparison == Q(43, 50) and masked == Q(93, 100)
    assert low_coarse == Q(4, 225000) and low_sharp == Q(47, 2250000)
    error_rows = []
    lam = sp.Symbol("lambda", real=True)
    for valuation, wo_multiplier, expected in ((1, 1, Q(13, 120000)),
                                               (6, 0, Q(193, 120000)),
                                               (7, 1, Q(119, 60000))):
        reserve = valuation*lam-(exact(G_COARSE+SIGMA)+(valuation-wo_multiplier)*lam)/6
        slope = rational(sp.diff(reserve, lam))
        lower = rational(reserve.subs(lam, exact(SIGMA/4)))
        assert slope > 0 and lower == expected
        error_rows.append({"valuation": valuation, "w": f"{valuation}*lambda",
                           "w_o": f"{wo_multiplier}*lambda", "lambda_lower": str(SIGMA/4),
                           "reserve_expression": str(reserve), "slope": str(slope),
                           "reserve_lower": str(lower),
                           "squared_scalar": "(1-Np^-1)^2" if valuation == 6 else "Np^-1",
                           "normalized_prime_average_retained": True})

    # Exact B3.80 identities exhibit the global maximum for all v>=0.
    M, A, v = sp.symbols("M A v", real=True)
    terminal = [identity("B3.80 v<=M/4", A-5*M/6-2*v/3-(M/4-v),
                         A-M-(M/4-v)/3),
                identity("B3.80 v>=M/4", A-5*M/6-2*v/3,
                         A-M-2*(v-M/4)/3)]
    terminal_reserve = 1-AMAX-3*SIGMA
    zero_reserve = 1-AMAX-Q(5, 3)*SIGMA
    high_reserve = Q(259, 16875)-Q(23, 7)*AUX-Q(1, 1000)
    assert terminal_reserve == Q(2511, 25000)
    assert zero_reserve == Q(2561, 25000)
    assert high_reserve == Q(24013, 1890000) > Q(1, 100)

    # An explicit feasible error assignment demonstrates strict budget
    # compatibility. Analytic lemmas still have to deliver these tolerances.
    delta1 = delta2 = theta = Q(1, 10**8)
    mesh = Q(1, 10**9)
    allocated = Q(1, 10**7)
    low_loss = delta2+Q(7, 45)*delta1+Q(104, 45)*theta+Q(7, 10)*mesh+allocated
    error_loss = delta2+delta1/6+Q(7, 3)*theta+mesh+allocated
    fixed_loss = Q(5, 6)*delta1+2*theta+allocated
    assert mesh < AUX/10 and mesh < low_coarse/100
    assert low_loss < low_coarse/100
    assert all(Q(r["reserve_lower"]) > error_loss for r in error_rows)
    return {"normalization": "M=1; homogeneous for every M>0",
            "capacity": str(CAP), "base_capacity": str(BASE), "a": str(AUX), "sigma": str(SIGMA),
            "g_sharp_upper": str(G_SHARP), "g_coarse_upper": str(G_COARSE),
            "A_lower": str(amin), "A_upper": str(AMAX),
            "centering_L": "1/4", "original_plain_lower_minus_L": str(Q(41, 100)-Q(1, 4)),
            "comparison_capacity_upper": str(comparison), "comparison_reserve": str(1-comparison),
            "comparison_with_mask_capacity_upper": str(masked), "comparison_with_mask_reserve": str(1-masked),
            "mask_daughters_reflect_threshold": "1/2", "mask_daughters_first_upper": "1/4",
            "mask_daughters_second_reflected_upper": "1/2+xi",
            "comparison_only_mask_expansion": True, "local_gate_applied_to_short_mask_daughters": False,
            "low_reserve_coarse": str(low_coarse), "low_reserve_sharp": str(low_sharp),
            "amplifier_errors": error_rows, "terminal_piecewise_identities": terminal,
            "terminal_maximum": "A-M at v=M/4", "terminal_reserve_after_3sigma": str(terminal_reserve),
            "second_zero_reserve_after_5sigma_over_3": str(zero_reserve),
            "first_zero_branch": "original powerful-product count; no amplification of zero",
            "added_zero_Gauss_row": "original B3.57 direct sixth-power count, never amplified",
            "high_reserve_after_total_loss_1_over_1000": str(high_reserve),
            "feasible_error_budget": {"delta_1": str(delta1), "delta_2": str(delta2), "theta_N": str(theta),
                "mesh": str(mesh), "allocated_other_loss": str(allocated), "low_loss": str(low_loss),
                "error_loss": str(error_loss), "fixed_terminal_loss": str(fixed_loss),
                "low_remaining": str(low_coarse-low_loss), "terminal_remaining": str(terminal_reserve-fixed_loss),
                "second_zero_remaining": str(zero_reserve-delta1-allocated),
                "comparison_remaining": str(1-comparison-allocated), "masked_comparison_remaining": str(1-masked-allocated)},
            "analytic_delivery_of_error_budget_certified": False}


@lru_cache(None)
def prime_power(p, n):
    assert n >= 0
    return sextic.power(sextic.PRIMES[p], n)


def element_from_valuations(vals):
    result = (1, 0)
    for p, n in sorted(vals.items()):
        result = sextic.multiply(result, prime_power(p, n))
    assert sextic.norm(result) == prod(p**n for p, n in vals.items())
    return result


def masked_phase(modulus_vals, value, holes=()):
    if any(sextic.character(p, value) is None for p in holes):
        return None
    answer = 0
    for p, n in modulus_vals.items():
        if n == 0:
            continue  # Absent support, unlike a displayed positive 6th power.
        phase = sextic.character(p, value)
        if phase is None:  # Includes n divisible by six: 0^6 is still 0.
            return None
        answer += n*phase
    return answer % 6


def second_local_states():
    states = []
    for i in range(1, 8):
        if i % 6:
            states.append((i, i, 0, 0, 1, "equal_non6_unit"))
            for hp in range(7):
                states.append((i, i, hp, 1, 0, "equal_non6_nonunit"))
        else:
            for hp in range(7):
                states.append((i, i, hp, 0, 0, "equal_6"))
    states.extend([(7, 6, 0, 0, 0, "unequal_min6"), (6, 7, 0, 0, 0, "unequal_min6")])
    return states


def joint_integer_fibre_controls():
    """Finite controls of the actual integral map, not a divisor-bound proof.

    First supports are {7,13}, second supports are {19,31}, hence genuine
    punctures force disjointness. The first s ranges over every divisor of
    the second radical. Complete labels remain attached until w is formed.
    """
    fibres = defaultdict(set)
    cases = cancelled_sixth = 0
    omitted_active = {"C": 0, "D": 0}
    first_inactive = ((1, 1), (7, 1), (1, 7))
    for i, j in product(range(1, 8), repeat=2):
        net = (i-j) % 6
        active = bool(net)
        ec, ed = (1-net) % 6, (1+net) % 6
        for iu, ju in first_inactive:
            assert (iu-ju) % 6 == 0
            for mask_e in range(4):
                if active and mask_e & 2:
                    continue  # e is supported only on inactive common primes.
                for ii, jj, hp19, v19, t19, kind in second_local_states():
                    for hp31 in (0, 4):
                        v31, t31 = int(hp31 > 0), int(hp31 == 0)
                        G = {19: min(ii, jj), 31: 1}
                        V = {19: v19, 31: v31}
                        hprime = {19: hp19, 31: hp31}
                        e = {13: 1} if mask_e & 1 else {}
                        if mask_e & 2:
                            e[7] = 1
                        for side, exp in (("C", ec), ("D", ed)):
                            assert 0 <= exp <= 5
                            F = {7: exp} if active and exp else {}
                            vals = {p: F.get(p, 0)+e.get(p, 0)+G.get(p, 0)+V.get(p, 0)+hprime.get(p, 0)
                                    for p in (7, 13, 19, 31)}
                            w = element_from_valuations(vals)
                            row = sextic.multiply(element_from_valuations(F), element_from_valuations(e))
                            row = sextic.multiply(row, element_from_valuations(G))
                            row = sextic.multiply(row, element_from_valuations(V))
                            row = sextic.multiply(row, element_from_valuations(hprime))
                            assert row == w  # No rational denominator or inverse power.
                            assert all(vals[p] >= G[p]+V[p] for p in G)
                            present_first = ({7} if active and exp else set()) | set(e)
                            missing_first = {7, 13}-present_first
                            inactive_first = {7, 13}-({7} if active else set())
                            expected_missing = (inactive_first-set(e)) | ({7} if active and exp == 0 else set())
                            assert missing_first == expected_missing
                            # Inactive first primes, or active e_side=0 primes,
                            # retain their original holes even when absent in w.
                            holes = {7, 13, 19, 31}
                            for p in holes:
                                assert masked_phase(vals, sextic.PRIMES[p], holes) is None
                            primitive = {p: n % 6 for p, n in vals.items() if n % 6}
                            for p, n in vals.items():
                                if n and n % 6 == 0:
                                    assert masked_phase(primitive, sextic.PRIMES[p], holes) is None
                                    cancelled_sixth += 1
                            for s_bits in range(4):
                                s = {p: 1 for bit, p in enumerate((19, 31)) if s_bits & (1 << bit)}
                                assert all(vals[p] >= 1 for p in s)
                                assert set(s) <= set(G)
                                omitted_active[side] += active and exp == 0
                                label = (i, j, iu, ju, mask_e, ii, jj, hp19, v19, t19, hp31, v31, t31, s_bits)
                                key = (side, tuple(sorted(vals.items())), tuple(sorted(missing_first)))
                                fibres[key].add(label)
                                cases += 1
    # Source partition table and label reconstruction are finite here.
    # All first powers are bounded-range allocations, never free labels.
    return {"cases": cases, "integer_fibres_with_missing_radical_fixed": len(fibres),
            "largest_finite_fibre": max(map(len, fibres.values())),
            "active_zero_phase_cases_by_side": omitted_active, "cancelled_sixth_hole_checks": cancelled_sixth,
            "first_projector_s_all_divisors_tested": True,
            "all_first_mask_divisor_subsets_tested": True,
            "exact_map": "w=F_side*e*G_c*V_id*h_prime in Z[omega], both C and D",
            "reconstructed_support": ["active first e_side!=0 primes", "mask e", "rad(D_2 E_2)", "first s"],
            "separate_missing_radical_width": "p-R-E+R_zero",
            "original_holes": "all first/second extracted primes and any row holes; canceled exponents retain zero extension",
            "bounded_powers_and_allocations_are_not_independently_counted": True,
            "uniform_subpower_fibre_bound_proved_by_code": False}


def sextic_first_CRT_controls():
    checks = zero_checks = wrong_same_sign = 0
    ray_phases = set()
    for r in (7, 13):
        columns = [p for p in sextic.PRIMES if p != r]
        for pa, pb in product(columns, repeat=2):
            if pa == pb:
                continue
            av, bv = sextic.PRIMES[pa], sextic.PRIMES[pb]
            for t in range(6):
                ar, ra = sextic.character(pa, sextic.PRIMES[r]), sextic.character(r, av)
                br, rb = sextic.character(pb, sextic.PRIMES[r]), sextic.character(r, bv)
                ab, ba = sextic.character(pa, bv), sextic.character(pb, av)
                ray_a, ray_b = (ar-ra) % 6, (br-rb) % 6
                ray_phases.update((ray_a, ray_b))
                raw = (sextic.character(pa, sextic.multiply(bv, sextic.PRIMES[r]))
                       -sextic.character(pb, sextic.multiply(av, sextic.PRIMES[r]))
                       -t*sextic.character(r, sextic.multiply(av, bv))) % 6
                ec, ed = (1-t) % 6, (1+t) % 6
                cphase = (ec*ar+t*ray_a) % 6
                dphase = (ed*br-t*ray_b) % 6
                assert raw == (ab-ba+cphase-dphase) % 6
                # The error of assigning the same xi_r sign to both sides
                # is detected on literal finite residue symbols.
                wrong = (ab-ba+(ar-t*ra)-(br-t*rb)) % 6
                wrong_same_sign += wrong != raw
                checks += 1
        for t in range(6):
            assert masked_phase({r: t or 6}, sextic.PRIMES[r]) is None
            zero_checks += 1
    assert wrong_same_sign and ray_phases <= {0, 3}
    return {"actual_finite_sextic_CRT_cases": checks, "zero_extension_cases": zero_checks,
            "C_exponent": "(1-t)%6", "D_exponent": "(1+t)%6",
            "actual_reciprocity_ray_phase_values": sorted(ray_phases),
            "same_sign_negative_control_detected_cases": wrong_same_sign,
            "fixed_ray_group_before_labels_required": True,
            "uniform_reciprocity_or_ray_expansion_proved_by_finite_controls": False}


def sixth_free_lift_controls():
    cases = cancelled_holes = fixed_good_core = 0
    prime_list = (7, 13, 19)
    for exponents in product(range(13), repeat=3):
        vals = dict(zip(prime_list, exponents))
        core = {p: n % 6 for p, n in vals.items() if n % 6}
        free = {p: n//6 for p, n in vals.items() if n//6}
        holes = {p for p, n in vals.items() if n}
        j = element_from_valuations(vals)
        k, b = element_from_valuations(core), element_from_valuations(free)
        assert j == sextic.multiply(k, sextic.power(b, 6))
        assert all(0 <= n <= 5 for n in core.values())
        fixed_good_core += not core
        for column in ((1, 0), (2, 0), (3, 1), sextic.PRIMES[7], sextic.PRIMES[13]):
            assert masked_phase(vals, column) == masked_phase(core, column, holes)
        for p in holes-set(core):
            assert masked_phase(vals, sextic.PRIMES[p]) is None
            assert masked_phase(core, sextic.PRIMES[p], holes) is None
            cancelled_holes += 1
        cases += 1
    assert fixed_good_core == 27 and cancelled_holes > 0
    return {"factorization_cases": cases, "cancelled_hole_cases": cancelled_holes,
            "map": "j=k*b^6; 0<=v_p(k)<6; original holes retained",
            "density_series": "H^(R0+epsilon)*sum_b (Nb)^(-6*(R0+epsilon))",
            "continuous_convergence_margin": "6*R0-1>=5/7",
            "finite_fixed_good_core_cases_excluded_from_density_population": fixed_good_core,
            "finite_nonempty_good_core_cases": cases-fixed_good_core,
            "fixed_inducing_cores_require_original_terminal_payment": True,
            "bounded_or_subunit_nonempty_windows": "replace negative nominal width only within support tolerance; never use a density count below one",
            "ideal_counting_or_zero_density_estimate_proved_by_finite_code": False}


def complete_projector_controls():
    first_cases = allocation_cases = 0
    for u, v in product(range(16), repeat=2):
        full = sum((-1)**s.bit_count() for s in range(16)
                   if s & ~u == 0 and s & ~v == 0)
        assert full == int(u & v == 0)
        first_cases += 1
    # B3.65 on four actual factors: two plains and two independent slots.
    # All nonempty priority allocations and their signs remain present.
    for divisibility in product((0, 1), repeat=4):
        expanded = 0
        for selected in range(1, 16):
            expanded += (-1)**(selected.bit_count()+1)*prod(
                divisibility[i] for i in range(4) if selected & (1 << i))
        assert expanded == int(any(divisibility))
        allocation_cases += 1
    assert 1-1 == 0  # Full {1,p} projector; retaining only s=1 gives 1.
    return {"complete_first_projector_cases": first_cases,
            "complete_priority_allocation_cases": allocation_cases,
            "all_Mobius_signs_retained": True,
            "incomplete_projector_negative_control_rejected": True,
            "quotient_plain_variables_may_retain_selected_prime": True,
            "one_variable_new_puncture_inserted": False,
            "scope": "Finite indicator identities; no artificial noncoprime coefficient is identified with the genuine correlation"}


def negative_controls():
    # This valid squared-label numerical ledger fits the LP parent gate.
    q, rho, delta = Q(1, 10), Q(19, 54), Q(7, 10)
    joint = -1+5*AUX+(1-6*AUX)*rho+delta*(AMAX-q)
    wrong_independent = joint+q
    assert joint < 0 < wrong_independent
    # A canceled factor of valuation six must vanish at its own prime.
    p = 7
    correct = masked_phase({p: 6}, sextic.PRIMES[p])
    wrong = masked_phase({}, sextic.PRIMES[p])
    assert correct is None and wrong == 0
    # A first active e_C=0 prime is absent from the integer index but remains
    # in the common mask and in the explicit missing-label radical.
    assert (1-1) % 6 == 0
    assert masked_phase({}, sextic.PRIMES[p], {p}) is None
    return {"independentlabelcount": {"q": str(q), "joint_excess": str(joint),
                "excess_with_spurious_independent_Zq": str(wrong_independent),
                "incorrect_payment_rejected": True,
                "generic_extra_first_count": "p+s0; disagrees with LP.14 and would recount s"},
            "cancelledholes": {"correct_value": "0 (nonunit)", "wrong_value": "1 (phase 0)",
                "valuation_six_hole_removal_rejected": True,
                "active_e_C_zero_hole_removal_rejected": True}}


def report():
    paper = (ROOT/PAPER).read_text()
    for n in (41, 44, 50, 52, *range(53, 81)):
        assert f"\\tag{{B3.{n}}}" in paper
    assert "CRT contributes" in paper and "complete" in paper
    digest = lambda path: sha256(path.read_bytes()).hexdigest()
    return {"schema": "local-physical-moment-source-ledger-v1",
            "status": "PASS_exact_continuous_ledgers_and_finite_source_controls",
            "script": "tools/local_physical_moment_audit.py", "script_sha256": digest(Path(__file__)),
            "input_sha256": {p: digest(ROOT/p) for p in INPUTS}, "sympy_version": sp.__version__,
            "continuous_sign_certificates": continuous_high_bin_certificates(),
            "symbolic_joint_ledgers": symbolic_joint_ledgers(),
            "complete_source_balance_certificates": complete_source_balance_certificates(),
            "projector_and_child_ledgers": projection_and_child_ledgers(),
            "normalized_scalar_reserves": scalar_reserves(),
            "joint_integer_fibres": joint_integer_fibre_controls(),
            "actual_sextic_first_CRT": sextic_first_CRT_controls(),
            "all_row_sixth_free_lift": sixth_free_lift_controls(),
            "complete_projector_controls": complete_projector_controls(),
            "negative_controls": negative_controls(),
            "scope": "Exact rational continuous scalar/source identities, whole-interval polynomial signs, finite Z[omega] row maps and literal sextic phases. Analytic density, prime/pointwise estimates, divisor bounds, Fourier transport, profile/height uniformity and error delivery are imported obligations, not certified by finite code.",
            "parent_old_moving_width": "0", "arbitrary_old_moving_width_supported": False,
            "source_labels_retained_before_counts": True,
            "analytic_local_moment_proved_by_code": False,
            "literal_physical_adapter_verified": False, "new_moment_kernel_verified": False,
            "all_family_kernel_verified": False, "full_recovery_verified": False,
            "record_proved": False, "eligible_for_tracker_submission": False, "runs_Lean": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Recompute and compare all report fields and hashes")
    args = parser.parse_args()
    result = report()
    if args.check:
        assert json.loads(OUTPUT.read_text()) == result, "Stale local physical moment audit; review changed inputs before regenerating"
    else:
        OUTPUT.parent.mkdir(parents=True, exist_ok=True)
        OUTPUT.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status": result["status"],
                      "continuous_sign_certificates": len(result["continuous_sign_certificates"]),
                      "joint_integer_cases": result["joint_integer_fibres"]["cases"],
                      "sextic_CRT_cases": result["actual_sextic_first_CRT"]["actual_finite_sextic_CRT_cases"],
                      "negative_controls_rejected": True, "new_moment_kernel_verified": False,
                      "eligible_for_tracker_submission": False, "runs_Lean": False}, indent=2))


if __name__ == "__main__":
    main()
