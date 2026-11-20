/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.Constants

/-! Exact coarse-geometry facts for the supplied Cycle092 interval.
These remove the old numerical .816 cutoff as an arithmetic obstacle only.
They do not instantiate or alter the inherited BoundsCore/CoreBounds classes,
prove source admission or physical prices, or establish Candidate.bound. -/

namespace QRH.Cycle090

noncomputable def cycle092Ell : ℝ := 11 / 3 - 4 * theta
noncomputable def cycle092X (h : ℝ) : ℝ := 1 + cycle092Ell - h
noncomputable def cycle092Y (h : ℝ) : ℝ := h - 2 * cycle092Ell
noncomputable def cycle092FloorPrice (h d : ℝ) : ℝ :=
  51 / 100 - 49 / 150 * h + 51 / 100 * cycle092Ell + 33 / 50 * d

/-- The old .816 contract cannot hold anywhere in the supplied interval. -/
theorem cycle092_not_old_conductor_bound {h : ℝ} (hh : hLower ≤ h) :
    ¬ h < 816 / 1000 := by
  norm_num [hLower] at hh
  linarith

/-- The five coarse fields, with the conductor upper bound widened to .818.
This theorem is deliberately separate from the narrower inherited typeclass. -/
theorem cycle092_coarse_geometry {h : ℝ} (hl : hLower ≤ h) (hu : h ≤ hUpper) :
    (873 / 1000 < theta ∧ theta < 7 / 8) ∧
    (793 / 1000 < h ∧ h < 818 / 1000) ∧
    (458 / 1000 < cycle092Y h ∧ cycle092Y h < 473 / 1000) ∧
    (1672 / 10000 < cycle092Ell ∧ cycle092Ell < 175 / 1000) ∧
    7 / 100 < cycle092Y h / 2 - h * (17 / 50 - 1 / 6) - 1 / 50 := by
  norm_num [hLower, hUpper] at hl hu
  norm_num [theta, cycle092Y, cycle092Ell]
  constructor
  · constructor <;> linarith
  · constructor
    · constructor <;> linarith
    · linarith

/-- Exact conservative floor reserve at the upper directed conductor endpoint. -/
theorem cycle092_floor_margin_exact :
    theta - cycle092FloorPrice hUpper (hUpper + 1 / 10000000000) -
      1 / 100000 - 1 / 1000000000000 = 7181001779 / 3000000000000 := by
  norm_num [theta, cycle092FloorPrice, cycle092Ell, hUpper]

/-- The actual interval retains more than .00239 after the old floor losses. -/
theorem cycle092_floor_margin {h d : ℝ} (hu : h ≤ hUpper)
    (hd : d ≤ h + 1 / 10000000000) :
    239 / 100000 < theta - cycle092FloorPrice h d -
      1 / 100000 - 1 / 1000000000000 := by
  norm_num [theta, hUpper, cycle092FloorPrice, cycle092Ell] at *
  linarith

#print axioms cycle092_not_old_conductor_bound
#print axioms cycle092_coarse_geometry
#print axioms cycle092_floor_margin_exact
#print axioms cycle092_floor_margin
end QRH.Cycle090
