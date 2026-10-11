#!/usr/bin/env python3
"""Check the additional endpoint comparisons with exact rational arithmetic.

Run without arguments to regenerate the adjacent JSON receipt.  Run --check
to verify both the inequalities and the existing receipt without modifying it.
Only Python's standard library is required.  These comparisons do not certify
the analytic assembly or any Lean theorem.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path


def report() -> dict:
    h = Q(3969737987, 5000000000)
    ell = Q(626701, 3750000)
    theta = Q(4374433, 5000000)
    y = h - 2 * ell
    x = 1 + ell - h
    d0 = Q(1, 200)
    extension = Q(1, 10**10)
    k = Q(5, 6) - x / 3 - ell / 6
    total = x + y

    values = {
        "short_slot_incumbent_upper": 2 * Q(211, 500) + Q(9, 2) * Q(3, 100),
        "short_plain_incumbent_upper": Q(41, 100) + Q(211, 500)
        + Q(9, 2) * Q(71, 2000),
        "far_old_endpoint_upper": Q(7, 8) - Q(49, 150) * h
        + Q(7, 8) * ell + Q(33, 50) * d0,
        "floor_upper": Q(51, 100) + h / 3 + Q(51, 100) * ell,
        "small_row_relative": -Q(49, 150) * h + ell + Q(63, 50) * d0,
        "old_kappa_derivative_upper": Q(5, 288)
        + Q(3, 8) * Q(1, 2) / (12 * Q(7, 10) ** 2),
        "new_kappa_derivative_upper_extended": Q(3, 4) * (h + extension)
        * Q(5, 12) * Q(1, 18),
        "detector_supply_margin": ell / (h + extension) - Q(4, 21),
        "lower_row_supply_margin": 2 * ell - Q(1, 3),
        "low_geometry_gap": 2 * x - y - ell,
        "probe_geometry_signed_gap": y - 2 * x + ell,
        "probe_positive_part_argument": 1 + 3 * ell - 2 * total,
        "probe_normalized_exponent": (5 * x + y) / 12,
        "signal_exponent": theta - k,
        "physical_principal_w_margin": y / 20 - (1 + h) / 1000 - Q(1, 4000),
        "physical_principal_z_margin": h / 600 - Q(1, 1000) - Q(1, 4000),
        "local_saving_after_row_extension": Q(1, 10**7) - 2 * extension,
    }
    checks = {
        "short_slot_reserve": values["short_slot_incumbent_upper"] == Q(979, 1000),
        "short_plain_reserve": values["short_plain_incumbent_upper"] == 1 - Q(33, 4000),
        "far_old_endpoint_saving": values["far_old_endpoint_upper"] < theta - Q(1, 10),
        "floor_saving": values["floor_upper"] < theta - Q(1, 100),
        "small_row_saving": values["small_row_relative"] < -Q(1, 20),
        "old_feedback": values["old_kappa_derivative_upper"] < Q(1, 8),
        "new_feedback_including_extension": values["new_kappa_derivative_upper_extended"] < Q(1, 50),
        "detector_supply": values["detector_supply_margin"] > 0,
        "lower_row_supply": values["lower_row_supply_margin"] > 0,
        "positive_geometry_gap": values["low_geometry_gap"] > 0,
        "probe_signed_geometry_gap": values["probe_geometry_signed_gap"] < 0,
        "probe_positive_part_vanishes": values["probe_positive_part_argument"] < 0,
        "probe_exponent_identity": values["probe_normalized_exponent"] == values["signal_exponent"],
        "principal_w_margin": values["physical_principal_w_margin"] > 0,
        "principal_z_margin": values["physical_principal_z_margin"] > 0,
        "extension_saving": values["local_saving_after_row_extension"] > Q(9, 10**8),
        "geometry_sum": x + y == 1 - ell,
        "signal_boundary": theta == Q(11, 12) - ell / 4,
        "ordered_geometry": 0 < ell < x < y < 2 * x and y < Q(1, 2) < h < 2 * y,
        "zero_supremum_boundary_range": Q(87, 100) < theta < Q(7, 8),
    }
    failures = [name for name, passed in checks.items() if not passed]
    if failures:
        raise ArithmeticError("Exact checks failed: " + ", ".join(failures))
    return {
        "status": "exact rational checks passed",
        "checks": checks,
        "values": {name: str(value) for name, value in values.items()},
        "scope": "Additional endpoint arithmetic only; not analytic or kernel certification.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check existing JSON without writing")
    parser.add_argument(
        "--output", type=Path, default=Path(__file__).with_name("endpoint_extra_arithmetic.json")
    )
    args = parser.parse_args()
    result = report()
    if args.check:
        existing = json.loads(args.output.read_text())
        if existing != result:
            raise SystemExit("Receipt differs from exact recomputation: " + str(args.output))
    else:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"{len(result['checks'])} exact rational checks passed; receipt {'checked' if args.check else 'written'}.")


if __name__ == "__main__":
    main()
