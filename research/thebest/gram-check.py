#!/usr/bin/env python3
"""Exact finite sextic Gram checks; run: uv run research/thebest/gram-check.py.

No third-party dependencies. Arithmetic is Q[z]/(z^2-z+1), z=exp(pi*i/3).
Characters chi_p(u) are genuine order-six finite-field characters for p=7,13.
This checks finite identities, not the Eisenstein-family analytic estimate.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path


@dataclass(frozen=True)
class Q6:
    a: F = F(0)
    b: F = F(0)

    def __add__(self, other):
        if not isinstance(other, Q6):
            other = Q6(F(other))
        return Q6(self.a + other.a, self.b + other.b)

    __radd__ = __add__

    def __neg__(self):
        return Q6(-self.a, -self.b)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        if not isinstance(other, Q6):
            other = Q6(F(other))
        return Q6(self.a * other.a - self.b * other.b,
                  self.a * other.b + self.b * other.a + self.b * other.b)

    __rmul__ = __mul__

    def conjugate(self):
        return Q6(self.a + self.b, -self.b)

    def norm(self):
        value = self * self.conjugate()
        assert value.b == 0
        return value.a

    def json(self):
        return {"constant": str(self.a), "zeta6": str(self.b)}


ONE, ZERO, Z = Q6(F(1)), Q6(), Q6(F(0), F(1))
POWERS = [ONE]
for _ in range(5):
    POWERS.append(POWERS[-1] * Z)
assert POWERS[-1] * Z == ONE
PRIMES = (7, 13)
PERIOD = 91


def character_table(p):
    generator = next(g for g in range(2, p)
                     if len({pow(g, k, p) for k in range(p - 1)}) == p - 1)
    table = [ZERO] * p
    for k in range(p - 1):
        table[pow(generator, k, p)] = POWERS[k % 6]
    assert len(set(table[1:])) == 6
    for a, b in product(range(p), repeat=2):
        assert table[a * b % p] == table[a] * table[b]
    return table


TABLES = {p: character_table(p) for p in PRIMES}


def label(n, orientation=1):
    residual, support = [], []
    for p in PRIMES:
        exponent = 0
        while n % p == 0:
            n //= p
            exponent += 1
        residual.append(orientation * exponent % 6)
        support.append(bool(exponent))
    assert n == 1
    return tuple(residual), tuple(support)


def combine(*labels):
    return (tuple(sum(x[0][j] for x in labels) % 6 for j in range(2)),
            tuple(any(x[1][j] for x in labels) for j in range(2)))


def evaluate(key, u):
    residual, support = key
    value = ONE
    for j, p in enumerate(PRIMES):
        if support[j] and u % p == 0:
            return ZERO  # Crucial even when residual[j] == 0.
        if residual[j]:
            local = TABLES[p][u % p]
            for _ in range(residual[j]):
                value = value * local
    return value


def kernel(left, right, rows):
    return sum((evaluate(left, u) * evaluate(right, u).conjugate()) * w
               for u, w in rows)


def complete_kernel(left, right):
    if left[0] != right[0]:
        return ZERO
    support = tuple(a or b for a, b in zip(left[1], right[1]))
    return Q6(F(product_int(p - int(active) for p, active in zip(PRIMES, support))))


def product_int(values):
    result = 1
    for value in values:
        result *= value
    return result


# Actual integer Mobius signs on squarefree inverse indices. Fixed exact
# twists/profiles differ between M and S, exercising conjugation and signs.
INVERSE = {1: ONE, 7: -Z * F(1, 2), 13: -POWERS[2] * F(2, 3),
           91: POWERS[4] * F(1, 5)}
PLAIN = {1: ONE * F(2, 3), 7: POWERS[5] * F(1, 3),
         13: Z * F(2, 5), 49: POWERS[2] * F(1, 7),
         7**6: -ONE * F(1, 11)}


def check_case(orientation, rows, complete):
    coefficients = {}
    for (a, ca), (b, cb), (c, cc) in product(INVERSE.items(), PLAIN.items(), PLAIN.items()):
        key = combine(label(a), label(b, orientation), label(c, orientation))
        coefficients[key] = coefficients.get(key, ZERO) + ca * cb * cc
    direct, expanded = F(0), F(0)
    for u, weight in rows:
        m = sum(c * evaluate(label(n), u) for n, c in INVERSE.items())
        s = sum(c * evaluate(label(n, orientation), u) for n, c in PLAIN.items())
        q = sum(c * evaluate(key, u) for key, c in coefficients.items())
        assert q == m * s * s
        direct += weight * m.norm() * s.norm() ** 2
        expanded += weight * q.norm()
    gram, diagonal = ZERO, ZERO
    for left, cl in coefficients.items():
        for right, cr in coefficients.items():
            k = kernel(left, right, rows)
            if complete:
                assert k == complete_kernel(left, right)
            term = cl * cr.conjugate() * k
            gram += term
            if left[0] == right[0]:
                diagonal += term
    assert gram == Q6(direct) == Q6(expanded)
    assert diagonal.b == 0 and diagonal.a >= 0
    if complete:
        assert diagonal == gram
    # Conjugating S flips orientation and conjugates its fixed coefficients,
    # with no change to its absolute value. Conjugating the character alone
    # would generally change the value and is not the asserted identity.
    for u, _ in rows:
        s = sum(c * evaluate(label(n, orientation), u) for n, c in PLAIN.items())
        conjugate_s = sum(c.conjugate() * evaluate(label(n, -orientation), u)
                          for n, c in PLAIN.items())
        assert conjugate_s == s.conjugate()
    return {"orientation_M_S": [1, orientation], "row_count": len(rows),
            "grouped_coefficients": len(coefficients),
            "mixed_moment": str(direct), "sextic_diagonal": diagonal.json(),
            "off_diagonal": (gram - diagonal).json(),
            "direct_convolution_gram_equal": True,
            "complete_period_orthogonality_checked": complete,
            "whole_polynomial_orientation_alignment_checked": True}


def main():
    complete = [(u, F(1)) for u in range(PERIOD)]
    partial = [(u, F(1 + u % 3, 1 + u % 2)) for u in range(17)]
    cases = [check_case(sign, rows, full) for sign in (1, -1)
             for rows, full in ((complete, True), (partial, False))]
    trivial, sixth = label(1), label(7**6)
    assert trivial[0] == sixth[0] and trivial[1] != sixth[1]
    assert evaluate(trivial, 7) == ONE and evaluate(sixth, 7) == ZERO
    assert kernel(sixth, trivial, complete) == Q6(F(78))
    assert kernel(trivial, trivial, complete) == Q6(F(91))
    # Opposite orientations cancel the exponent but must retain its support.
    cancellation = combine(label(7), label(7, -1))
    assert cancellation == sixth
    # Incomplete-row off-diagonal can cancel the entire positive diagonal.
    # u=1 gives chi_7(u)=1, so (1-chi_7(u)) is zero there.
    k1, k7 = label(1), label(7)
    row = [(1, F(1))]
    d = kernel(k1, k1, row) + kernel(k7, k7, row)
    total = d - kernel(k1, k7, row) - kernel(k7, k1, row)
    assert d == Q6(F(2)) and total == ZERO
    results = {
        "status": "EXACT FINITE IDENTITIES ONLY; NO ASYMPTOTIC OR ZERO-FREE CLAIM",
        "arithmetic": "Q(zeta_6), zeta_6^2-zeta_6+1=0; rational coefficients",
        "model": "zero-extended order-six finite-field characters chi_7(u), chi_13(u)",
        "command": "uv run research/thebest/gram-check.py",
        "character_multiplicativity_exhaustively_checked": True,
        "cases": cases,
        "sixth_power_collision": {
            "indices": [1, 7**6], "same_residual_vector": True,
            "different_zero_support": True, "witness_row": 7,
            "values_at_witness": [ONE.json(), ZERO.json()],
            "correct_complete_cross_kernel": "78",
            "incorrect_kernel_if_support_dropped": "91",
            "opposite_orientation_cancellation_support_checked": True},
        "diagonal_is_not_a_general_lower_bound": {
            "polynomial": "1-chi_7(u)", "rows": [1],
            "sextic_diagonal": "2", "off_diagonal": "-2", "moment": "0"},
        "limitations": "Finite-field reciprocity-style model only. No Eisenstein annuli, independent real heights, conductor-uniform estimate, or analytic moment bound is tested."}
    output = Path(__file__).with_name("gram-check-results.json")
    output.write_text(json.dumps(results, indent=2) + "\n")
    print(f"PASS: {len(cases)} exact mixed-moment/Gram cases, sextic collisions, and cancellation; {output}")


if __name__ == "__main__":
    main()
