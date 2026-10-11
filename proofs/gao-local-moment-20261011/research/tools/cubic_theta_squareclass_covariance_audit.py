#!/usr/bin/env python3
"""Exact finite Gauss/cube/parity controls, not an analytic covariance proof.

Gauss identities are checked in integer cyclotomic rings, using literal
split-prime characters and the trace additive character. No floating point,
exponent fitting, infinite Euler-product certification or Lean is used.
"""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from hashlib import sha256
from itertools import combinations, permutations, product
import json
from math import isqrt, prod
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "numerics/results/cubic_theta_squareclass_covariance_audit.json"
PRIMES = {7: (-2, -3), 13: (4, 3), 19: (-2, 3), 31: (1, 6)}


def norm(z):
    a, b = z
    return a*a - a*b + b*b


def multiply(z, w):
    a, b = z
    c, d = w
    return a*c - b*d, a*d + b*c - b*d


def power(z, k):
    out = (1, 0)
    for _ in range(k):
        out = multiply(out, z)
    return out


def character(p, z):
    a, b = PRIMES[p]
    omega = -a * pow(b, -1, p) % p
    assert (omega*omega + omega + 1) % p == 0
    value = (z[0] + z[1]*omega) % p
    if not value:
        return None  # Preserve the original nonunit zero.
    phases = {pow(1 + omega, j, p): j for j in range(6)}
    return phases[pow(value, (p - 1)//6, p)]


def factors(n):
    out, p = [], 2
    while p*p <= n:
        if n % p == 0:
            out.append(p)
            n //= p
            assert n % p != 0, "These controls use squarefree rational orders"
        p += 1
    if n > 1:
        out.append(n)
    return out


@lru_cache(None)
def cyclotomic(n):
    primes = factors(n)
    degree = n
    for p in primes:
        degree = degree//p*(p - 1)
    c = [1] + [0]*degree
    # Phi_n = product_(d|n)(1-X^d)^mu(n/d), computed to its exact degree.
    for k in range(len(primes) + 1):
        for selected in combinations(primes, k):
            d = prod(selected)
            if d > degree:
                continue
            if (len(primes) - k) % 2:
                for i in range(d, degree + 1):
                    c[i] += c[i-d]
            else:
                for i in range(degree, d - 1, -1):
                    c[i] -= c[i-d]
    assert c[-1] == 1
    return tuple(c)


def ring_reduce(poly, n):
    phi = cyclotomic(n)
    degree = len(phi) - 1
    lower = [(j, a) for j, a in enumerate(phi[:-1]) if a]
    c = [0]*n
    for k, a in poly.items():
        c[k % n] += a
    for k in range(n - 1, degree - 1, -1):
        a = c[k]
        if a:
            c[k] = 0
            for j, b in lower:
                c[k-degree+j] -= a*b
    return tuple(c[:degree])


def ring_product(a, b, n):
    c = {}
    for i, x in a.items():
        for j, y in b.items():
            k = (i + j) % n
            c[k] = c.get(k, 0) + x*y
    return c


def ring_shift(a, shift, n, scale=1):
    return {(k + shift) % n: scale*v for k, v in a.items()}


def gauss(selected, order, ambient, additive="trace"):
    modulus = prod(selected)
    assert ambient % (3*modulus) == 0
    z = (1, 0)
    for p in selected:
        z = multiply(z, PRIMES[p])
    assert norm(z) == modulus
    assert additive in ("trace","source")
    # lambda=1+2omega: Tr((a+b*omega)/lambda)=b.
    trace = 2*z[0]-z[1] if additive == "trace" else -z[1]
    answer = {}
    for x in range(modulus):
        phases = [character(p, (x, 0)) for p in selected]
        if any(j is None for j in phases):
            continue
        phase = order*sum(phases) % 6
        if phase % 2:
            assert ambient % 6 == 0
            phase_exponent = ambient//6*phase
        else:
            phase_exponent = ambient//3*(phase//2)
        exponent = (ambient//modulus*trace*x + phase_exponent) % ambient
        answer[exponent] = answer.get(exponent, 0) + 1
    return answer


def gauss_controls():
    checked = 0
    for p in PRIMES:
        n = 3*p
        actual = ring_product(gauss([p], 4, n), gauss([p], 2, n), n)
        assert ring_reduce(actual, n) == ring_reduce({0: p}, n)
        checked += 1
    z, f = 7, 13
    n = 3*z*f
    product = ring_product(gauss([z], 4, n), gauss([f], 4, n), n)
    exponent = 2*character(z, PRIMES[f]) % 6
    actual = gauss([z, f], 4, n)
    expected = ring_shift(product, n//3*(exponent//2), n)
    assert ring_reduce(actual, n) == ring_reduce(expected, n)
    assert ring_reduce(actual, n) != ring_reduce(product, n)
    checked += 1
    fp = 19
    n = 3*z*f*fp
    actual = ring_product(gauss([z, f], 4, n), gauss([z, fp], 2, n), n)
    outside = ring_product(gauss([f], 4, n), gauss([fp], 2, n), n)
    exponent = (2*character(z, PRIMES[f]) - 2*character(z, PRIMES[fp])) % 6
    expected = ring_shift(outside, n//3*(exponent//2), n, scale=z)
    assert ring_reduce(actual, n) == ring_reduce(expected, n)
    checked += 1
    return dict(exact_gauss_identities=checked, primewise_multiplicativity=False,
                common_core_norm=z, different_core_norms=[f, fp],
                largest_cyclotomic_order=n, arithmetic="integer cyclotomic polynomial remainder")


def quadratic_sextic_gauss_controls():
    checked = 0
    for p in PRIMES:
        ambient = 6*p
        left = ring_product(gauss([p],1,ambient),gauss([p],4,ambient),ambient)
        right = ring_product(gauss([p],2,ambient),gauss([p],3,ambient),ambient)
        phase = -character(p,(4,0)) % 6
        assert ring_reduce(left,ambient) == ring_reduce(
            ring_shift(right,ambient//6*phase,ambient),ambient)
        quadratic_square = ring_product(gauss([p],3,ambient),
                                        gauss([p],3,ambient),ambient)
        minus_one = 3*character(p,(-1,0)) % 6
        sign = 1 if minus_one == 0 else -1
        assert minus_one in (0,3)
        assert ring_reduce(quadratic_square,ambient) == ring_reduce({0:sign*p},ambient)
        checked += 2
    p,q = 7,13
    ambient = 6*p*q
    quadratic_crt_phase = (3*character(p,PRIMES[q])+
                           3*character(q,PRIMES[p])) % 6
    assert quadratic_crt_phase in (0,3)
    r_sign = 1 if quadratic_crt_phase == 0 else -1
    prime_product = ring_product(gauss([p],3,ambient),gauss([q],3,ambient),ambient)
    composite = gauss([p,q],3,ambient)
    assert ring_reduce(composite,ambient) == ring_reduce(
        ring_shift(prime_product,ambient//6*quadratic_crt_phase,ambient),ambient)
    conjugate_q = {(-k) % ambient:v for k,v in gauss([q],3,ambient).items()}
    phase_cancel = ring_product(ring_product(gauss([p],3,ambient),
                                            conjugate_q,ambient),composite,ambient)
    p_sign = 1 if 3*character(p,(-1,0)) % 6 == 0 else -1
    assert ring_reduce(phase_cancel,ambient) == ring_reduce({0:r_sign*p*q*p_sign},ambient)
    checked += 2
    return dict(identities=checked, largest_cyclotomic_order=ambient,
                hasse_davenport=True, quadratic_crt=True,
                reciprocal_bicharacter_cancellation=True,
                scope="Actual finite Gauss identities only; no nonzero-alias cancellation estimate.")


def nonzero_poisson_fourier_controls():
    p,q = 7,19  # This moving principal modulus has epsilon_p(pi_q)=-1.
    ambient = 6*p*q
    modulus = multiply(PRIMES[p],PRIMES[q])
    conjugate_modulus = (modulus[0]-modulus[1],-modulus[1])
    tau_negative = {(-k) % ambient:v for k,v in gauss([p],3,ambient,"source").items()}
    moving_phase = 3*character(p,PRIMES[q]) % 6
    assert moving_phase == 3
    epsilon_j = -1
    inputs = [(1,0),(2,0),PRIMES[p],PRIMES[q],
              multiply((2,0),PRIMES[p]),modulus]
    checked = 0
    for ell in inputs:
        numerator = multiply(ell,conjugate_modulus)
        trace = numerator[1]  # The pinned e_F(z)=exp(2pi*i*Tr(z/lambda)).
        direct = {}
        for x in range(p*q):
            phase = character(p,(x,0))
            if phase is None or character(q,(x,0)) is None:
                continue
            exponent = (ambient//6*(3*phase % 6)-ambient//(p*q)*trace*x) % ambient
            direct[exponent] = direct.get(exponent,0)+1
        epsilon = character(p,ell)
        if epsilon is None:
            expected = {}
        else:
            epsilon = 1 if 3*epsilon % 6 == 0 else -1
            ram = q-1 if character(q,ell) is None else -1
            expected = {k:epsilon_j*epsilon*ram*v for k,v in tau_negative.items()}
        assert ring_reduce(direct,ambient) == ring_reduce(expected,ambient)
        if ell == (1,0):
            wrong = {k:epsilon*ram*v for k,v in tau_negative.items()}
            assert ring_reduce(direct,ambient) != ring_reduce(wrong,ambient)
        checked += 1
    return dict(cases=checked, primitive_R=p, principal_J=q,
                negative_additive_gauss=True, moving_epsilon_R_J_required=True,
                additive_convention="Tr(z/lambda), lambda=1+2omega",
                primitive_and_principal_nonunits_retained=True,
                scope="Exact finite CRT Fourier coefficients, including the moving numerator and sign; no global alias bound.")


def source_additive_calibration_controls():
    checked = 0
    lam = (1,2)
    for p in PRIMES:
        ambient = 6*p
        trace_gauss = gauss([p],3,ambient,"trace")
        source_gauss = gauss([p],3,ambient,"source")
        calibration_phase = 3*character(p,lam) % 6
        assert calibration_phase in (0,3)
        expected = ring_shift(source_gauss,ambient//6*calibration_phase,ambient)
        assert ring_reduce(trace_gauss,ambient) == ring_reduce(expected,ambient)
        cubic = gauss([p],2,ambient,"source")
        cubic_cube = ring_product(ring_product(cubic,cubic,ambient),cubic,ambient)
        a,b = PRIMES[p]
        actual_primary = {0:-p*a, ambient//3:-p*b}
        assert ring_reduce(cubic_cube,ambient) == ring_reduce(actual_primary,ambient)
        checked += 2
    return dict(cases=checked, quadratic_source_trace_relation="Gamma3_trace=epsilon_R(lambda) Gamma3_source",
                cubic_gauss_cube="tau2(pi)^3=-Npi*pi",
                scope="Exact pinned additive calibration and primary generators at four split primes only.")


def gadd(a, b):
    return a[0] + b[0], a[1] + b[1]


def gmul(a, b):
    return a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0]


def gconj(a):
    return a[0], -a[1]


def gdiv(a, b):
    out = gmul(a, gconj(b))
    norm_b = b[0]**2 + b[1]**2
    return out[0]/norm_b, out[1]/norm_b


def gscale(a, x):
    return a[0]*x, a[1]*x


def parity_controls():
    count = 0
    for p in PRIMES:
        for unit in [(F(1), F(0)), (F(-1), F(0)), (F(0), F(1)), (F(3,5), F(4,5))]:
            x, one = gscale(unit, F(1,p)), (F(1), F(0))
            y, xx = gconj(x), gmul(x, x)
            denominator = gadd(one, gscale(xx, -1))
            even = gdiv(gadd(one, gscale(gmul(x, y), -1)), denominator)
            odd = gdiv(gadd(x, gscale(y, -1)), denominator)
            squared = lambda a: gmul(a, gconj(a))[0]
            assert squared(even) + squared(odd) == 1
            assert gadd(gmul(even, gconj(odd)), gmul(odd, gconj(even))) == (0, 0)
            forced_even0 = gdiv(gadd(gscale(xx, p), gscale(one, -1)), denominator)
            forced_odd = gdiv(gscale(x, p-1), denominator)
            forced_even1 = gdiv(gscale(one, p-1), denominator)
            unit_mass = squared(forced_even0) + squared(forced_odd)
            nonunit_mass = squared(forced_even1) + squared(forced_odd)
            mean = F(p,p+1)*unit_mass + F(1,p+1)*nonunit_mass
            assert mean == F(p*p,p+1)
            mixed_unit = gadd(gmul(forced_even0, gconj(odd)),
                             gmul(forced_odd, gconj(even)))
            mixed_nonunit = gadd(gmul(forced_even1, gconj(odd)),
                                gmul(forced_odd, gconj(even)))
            mixed_raw = gadd(mixed_unit, gscale(mixed_nonunit, F(1,p)))
            assert mixed_raw == unit
            # The actual scalar phase and relative P^3 profile shift supply
            # this inverse phase; the script checks only their local algebra.
            mixed_normalized = gscale(gmul(mixed_raw, gconj(unit)), F(1,p))
            assert mixed_normalized == (F(1,p), F(0))
            # This is a local SF-k density model, not a full Poisson adapter.
            unforced_k_model = F(p,p+1) + F(p,(p+1)**2)
            forced_k_model = F(p,p+1)*mean/p
            assert forced_k_model/unforced_k_model == F(p,p+2)
            joint_unforced_pole = (1-F(1,p))**2*(1+F(2,p))
            joint_forced_pole = (1-F(1,p))**2
            assert joint_forced_pole/joint_unforced_pole == F(p,p+2)
            full_ram_mean = -F(p,p+1) + F(p-1,p+1)
            unit_only_mean = -F(p,p+1)
            assert full_ram_mean == -F(1,p+1)
            assert full_ram_mean/unit_only_mean == F(1,p)
            count += 1
    u = PRIMES[13]
    v = (u[0] - u[1], -u[1])
    m = PRIMES[7]
    left, right = multiply(power(u, 6), m), multiply(power(v, 6), m)
    assert left != right and norm(left) == norm(right)
    assert character(19, left) == character(19, right)
    assert character(13, left) is None and character(13, right) is not None
    return dict(parity_cases=count, forced_mean="P^2/(P+1)",
                sf_alias_density_ratio_model="P/(P+2)",
                sf_alias_full_ramanujan_mean="-1/(P+1)",
                sf_alias_unit_only_mean="-P/(P+1)",
                opposite_parity_one_leg_forced_raw_mass="nu(p)^3 P^(3it)",
                with_scalar_phase_and_profile_shift="1/P",
                coherent_distinct_equal_norm_indices=True, natural_zero_preserved=True)


def complete_label_pole_controls():
    checked = 0
    one = (F(1), F(0))
    for p in PRIMES:
        omega = F(p,p+1)
        real_b = (F(1,p*p-1), F(0))
        imaginary_x = (F(0),F(1,p*p))
        complex_b = gdiv(imaginary_x, gadd(one,gscale(imaginary_x,-1)))
        for b in (real_b,complex_b):
            a = gadd(one,gscale(b,2))
            u = (1+omega/p,F(0))
            d = gscale(a,-omega/p)
            left = right = gscale(b,omega/p)
            assert gadd(gadd(u,d),gadd(left,right)) == one
            assert gadd(u,d) != one  # Missing one-sided labels leave stress.
            if b[1]:
                assert gadd(gadd(u,d),gadd(left,gconj(right))) != one
            checked += 1
    return dict(cases=checked, whole_good_prime_linear_mass="1",
                one_sided_label_erasure_rejected=True,
                hermitian_replacement_rejected=True,
                scope="Exact local algebra after the written scalar-phase/profile transport; not a finite-cap or full-source pole certificate.")


def reciprocal_mask_control():
    # Literal daughter m=pi_7 cancels F0=pi_7 out of T=sfcore(F0*m).
    # The cube cofactor may then contain pi_7; the SF core still may not.
    f, z = PRIMES[7], PRIMES[13]
    n = multiply(z, power(f, 4))
    n_prime = multiply(z, power(f, 3))
    theta_product = multiply(n, n_prime)
    norm_product = norm(theta_product)
    assert isqrt(norm_product)**2 != norm_product
    full_product = multiply(theta_product, f)
    root = multiply(z, power(f, 4))
    assert full_product == multiply(root, root)
    assert character(7, z) is not None
    assert character(7, multiply(z, power(f, 3))) is None
    return dict(theta_product_square=False, full_alias_product_square=True,
                separate_core_and_cube_masks_required=True,
                daughter_norm=7, residual_squarefree_T_norm=1)


def complete_cubic_opening_controls():
    """Complete the literal chi-weighted cubic sum, including its zero row.

    This is a source check against claiming a second square-root gain from
    opening NZ.8 and completing both residue variables independently.
    """
    checked = 0
    for p, z in PRIMES.items():
        ambient = 6*p
        source_frequency = -z[1]
        tau1 = gauss([p], 1, ambient, additive="source")
        tau3 = gauss([p], 3, ambient, additive="source")
        tau3_minus = {(-k) % ambient: v for k, v in tau3.items()}
        unit_base = ring_product(tau1, tau3_minus, ambient)
        for v in (0, 1, 2, p-1):
            total = {}
            for x in range(1, p):
                chi_exponent = ambient//6*character(p, (x, 0))
                for ell in range(p):
                    exponent = (chi_exponent + ambient//p*source_frequency*
                                (x*ell**3-v*ell)) % ambient
                    total[exponent] = total.get(exponent, 0)+1
            right = {} if v == 0 else ring_shift(
                unit_base, 0, ambient, (-1)**(character(p, (v, 0)) % 2))
            assert ring_reduce(total, ambient) == ring_reduce(right, ambient)
            if v:
                # |tau1*tau3^-|^2=p^2: after division by p the
                # completed transform has magnitude one, not p^-1/2.
                conjugate = {(-k) % ambient: c for k, c in right.items()}
                assert ring_reduce(ring_product(right, conjugate, ambient),
                                   ambient) == ring_reduce({0: p*p}, ambient)
            checked += 1
    return dict(cases=checked, nonunit_zero_retained=True,
                normalized_unit_magnitude_squared=1,
                extra_complete_square_root_gain_rejected=True,
                scope="Exact chi-weighted complete cubic transform only; incomplete coupled arithmetic cancellation remains open.")


def native_gauss_fold_controls():
    prime_list = list(PRIMES)[:3]
    crt_cases = 0
    for labels in product(range(3), repeat=len(prime_list)):
        n_primes = [p for p, label in zip(prime_list, labels) if label == 1]
        f_primes = [p for p, label in zip(prime_list, labels) if label == 2]
        ambient = 3*prod(n_primes+f_primes)
        f = (1, 0)
        for p in f_primes:
            f = multiply(f, PRIMES[p])
        phase = 4*sum(character(p, f) for p in n_primes) % 6
        assert phase % 2 == 0
        lhs = gauss(n_primes+f_primes, 2, ambient, additive="source")
        rhs = ring_product(gauss(n_primes, 2, ambient, additive="source"),
                           gauss(f_primes, 2, ambient, additive="source"), ambient)
        rhs = ring_shift(rhs, ambient//3*(phase//2), ambient)
        assert ring_reduce(lhs, ambient) == ring_reduce(rhs, ambient)
        crt_cases += 1
    masks = range(1 << len(prime_list))
    collapse_cases = ram_cases = 0
    for m1 in masks:
        for m2 in masks:
            common = m1 & m2
            for k in masks:
                lhs = sum((-1)**f.bit_count() for f in masks
                          if f & ~common == 0 and
                          (m1 & ~f) & k == 0 and (m2 & ~f) & k == 0)
                a1, a2 = m1 & k, m2 & k
                expected = (-1)**a1.bit_count() if a1 == a2 == common else 0
                assert lhs == expected
                collapse_cases += 1
    for q in masks:
        for k in masks:
            lhs = 0
            for r in masks:
                if r & ~q or r & ~k:
                    continue
                nr = prod(p for i, p in enumerate(prime_list) if r & (1 << i))
                lhs += nr*(-1)**(q & ~r).bit_count()
            rhs = prod((p-1 if k & (1 << i) else -1)
                       for i, p in enumerate(prime_list) if q & (1 << i))
            assert lhs == rhs
            ram_cases += 1
    # m1=pi7*pi13, m2=pi7*pi19, k=pi7 is a nonzero folded
    # sector although chi_pi7(k)=0. Only the residual unit is divided.
    assert character(7, PRIMES[7]) is None
    assert character(13, PRIMES[7]) is not None
    assert character(19, PRIMES[7]) is not None
    return dict(actual_source_gauss_CRT_cases=crt_cases,
                signed_fold_and_zero_cases=collapse_cases,
                full_ramanujan_return_cases=ram_cases,
                nonunit_Gauss_factor_division_rejected=True,
                free_label_returns_when_coprime_projector_opened=True,
                source_cap_return="N k_prime (N r)^2 = N q N k_full",
                scope="Exact finite source CRT, divisor and Ramanujan identities only. The written source return map provides no complete inverse saving; no contraction is certified here.")


def conjugate_product_core_control():
    p1, q1, p2, q2 = (1, 6), (7, 3), (7, 6), (4, 9)
    def cubic_exponent(pi, value):
        p = norm(pi)
        omega = -pi[0]*pow(pi[1], -1, p) % p
        assert (omega*omega+omega+1) % p == 0
        residue = (value[0]+value[1]*omega) % p
        assert residue  # This control is a literal unit sector.
        return {pow(omega,j,p):j for j in range(3)}[
            pow(residue,(p-1)//3,p)]
    phases = [cubic_exponent(p1,p2),cubic_exponent(q1,q2),
              cubic_exponent(q1,p2),cubic_exponent(p1,q2)]
    assert phases == [2,2,1,1]
    cross = (phases[0]+phases[1]-phases[2]-phases[3]) % 3
    assert cross == 2
    leg_norms = [norm(multiply(a,b)) for a,b in
                 [(p1,p2),(q1,q2),(q1,p2),(p1,q2)]]
    assert leg_norms == [1333,2257,1591,1891]
    product_norm = prod(norm(pi) for pi in [p1,q1,p2,q2])
    assert leg_norms[0]*leg_norms[1] == leg_norms[2]*leg_norms[3] == product_norm
    return dict(unit_symbol_cases=4, cubic_exponents=phases,
                cross_ratio_omega_exponent=cross, leg_norms=leg_norms,
                product_norm=product_norm,
                possible_common_period_norm=product_norm**2,
                full_curvature_or_recovery_gain_certified=False,
                scope="Exact finite cubic residue-symbol control. The conjugate-product slice retains its original masks and globally separated Gauss carriers; its constant comparison is not a full fixed-power estimate.")


def cubic_determinant_control():
    """Local divisibility is not an upper covariance contraction."""
    roots = [(1, 0), (0, 1), (-1, -1)]
    lam = (1, 2)
    def add(z, w):
        return (z[0]+w[0], z[1]+w[1])
    def negate(z):
        return (-z[0], -z[1])
    def conjugate(z):
        return (z[0]-z[1], -z[1])
    def valuation(z):
        if z == (0, 0):
            return None  # Infinite, kept separate from finite orders.
        order = 0
        while True:
            numerator = multiply(z, conjugate(lam))
            if any(c % 3 for c in numerator):
                return order
            z = tuple(c//3 for c in numerator)
            order += 1
    def determinant(entries, d):
        result = (0, 0)
        for sigma in permutations(range(d)):
            term = (1, 0)
            for i, j in enumerate(sigma):
                term = multiply(term, entries[d*i+j])
            if sum(sigma[i] > sigma[j] for i in range(d)
                   for j in range(i+1, d)) % 2:
                term = negate(term)
            result = add(result, term)
        return result
    cases = zero = 0
    for d in (2, 3):
        for entries in product(roots, repeat=d*d):
            order = valuation(determinant(entries, d))
            assert order is None or order >= d-1
            zero += order is None
            cases += 1
    quartet = [roots[2], roots[1], roots[1], roots[2]]
    assert determinant(quartet, 2) == lam and norm(lam) == 3
    gram = [[(0, 0)]*2 for _ in range(2)]
    for i, j in product(range(2), repeat=2):
        for k in range(2):
            gram[i][j] = add(gram[i][j], multiply(
                conjugate(quartet[2*k+i]), quartet[2*k+j]))
    assert gram == [[(2, 0), (-1, 0)], [(-1, 0), (2, 0)]]
    negative = 0
    for d in range(3, 33):
        if d % 3 == 0:
            continue
        det = multiply((d-1, 1), power((-1, 1), d-1))
        assert valuation(det) == d-1
        assert norm((d-1, 1)) == d*d-3*d+3
        negative += 1
    assert F(101*101-3*101+3, 101*101) > F(97, 100)
    return dict(exhaustive_cubic_matrices=cases,
                zero_determinants=zero,
                nonzero_sharp_valuation_counterexamples=negative,
                quartet_determinant=list(lam), quartet_determinant_norm=3,
                quartet_gram=[[2, -1], [-1, 2]],
                large_counterexample_norm_ratio_squared=str(F(9901, 10201)),
                analytic_covariance_contraction_certified=False,
                scope="Finite Z[omega] determinant, valuation and Gram checks. Sharp local divisibility and nonvanishing permit norm/d tending to one; no native source or tensor recovery is certified.")


def report():
    owners = ["framework/programs/fixed_strip/results/CUBIC_THETA_SQUARECLASS_COVARIANCE.md",
              "framework/programs/fixed_strip/results/SIGNED_SIXTH_DILATION_COVARIANCE.md",
              "framework/programs/fixed_strip/results/CUBIC_THETA_RECIPROCAL_PRINCIPAL_COVARIANCE.md",
              "framework/programs/fixed_strip/results/CUBIC_THETA_SAME_CORE_PRINCIPAL_COVARIANCE.md",
              "framework/programs/fixed_strip/candidates/INVERSE_NONZERO_ALIAS_COPRIME_CORE.md",
              "framework/programs/fixed_strip/candidates/CUBE_RECIPROCAL_PARITY_PRINCIPAL_RESIDUE.md"]
    owners.append("framework/programs/fixed_strip/candidates/INVERSE_LOW_ALIAS_GCD_FRAME.md")
    owners.append("framework/audits/PATTERSON_DISPERSION_SOURCE_MATCH_2026-10-09.md")
    owners.append("framework/audits/ZETA_VALUE_DETERMINANT_TRANSFER_2026-10-09.md")
    digest = lambda p: sha256(p.read_bytes()).hexdigest()
    return dict(status="PASS_exact_squareclass_gauss_and_parity_controls",
                script="tools/cubic_theta_squareclass_covariance_audit.py",
                script_sha256=digest(Path(__file__)),
                input_sha256={p:digest(ROOT/p) for p in owners},
                gauss=gauss_controls(), parity=parity_controls(),
                quadratic_sextic_gauss=quadratic_sextic_gauss_controls(),
                nonzero_poisson_fourier=nonzero_poisson_fourier_controls(),
                source_additive_calibration=source_additive_calibration_controls(),
                complete_label_pole=complete_label_pole_controls(),
                reciprocal_mask=reciprocal_mask_control(),
                complete_cubic_opening=complete_cubic_opening_controls(),
                native_gauss_fold=native_gauss_fold_controls(),
                conjugate_product_core=conjugate_product_core_control(),
                cubic_determinant=cubic_determinant_control(),
                scope="Exact finite Gauss/CRT and local parity identities only. No infinite sum, contour estimate, profile transport, source reconstruction or power-saving exponent is certified by this script.",
                analytic_theorems_certified=False, full_alias_principal_adapter_proved=False,
                complete_inverse_gain_proved=False, runs_Lean=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = report()
    if args.check:
        assert json.loads(REPORT.read_text()) == result, "Report stale; regenerate after reviewing inputs"
    else:
        REPORT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "gauss", "parity", "complete_label_pole",
                     "quadratic_sextic_gauss", "nonzero_poisson_fourier",
                     "source_additive_calibration", "reciprocal_mask",
                     "complete_cubic_opening",
                     "native_gauss_fold",
                     "conjugate_product_core",
                     "cubic_determinant",
                     "complete_inverse_gain_proved", "runs_Lean"]}, indent=2))


if __name__ == "__main__":
    main()
