/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalAnalytic/ResidueNormalization.lean
Original SHA-256: 4960438ac0fd44382d02dd2f40a3fea8203b1a85e49c5276fd101b80d38e9eec
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.TunedCandidate
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison

/-!
# Actual double-residue normalization with variable probe geometry

This is an identity for the actual source multiplier, residue constant,
principalScalar and slotRatio. It identifies the changed signal shift before
any analytic bound is applied. No contour deformation is assumed or claimed.
-/

namespace LW56e2.Transport.PhysicalAnalytic
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison

def residueShift (x ell : ℝ) : ℝ := x / 3 + ell / 6 - 5 / 6

theorem residueShift_geometry (ell b : ℝ) :
    residueShift (TunedCandidate.lxAt ell b) ell = -2 / 3 - b / 6 := by
  dsimp [residueShift, TunedCandidate.lxAt]
  ring

theorem residueShift_tuned :
    residueShift TunedCandidate.lx TunedCandidate.ell =
      -2 / 3 - TunedCandidate.b / 6 :=
  residueShift_geometry TunedCandidate.ell TunedCandidate.b

theorem transported_source_power_identity {Z : ℝ} (hZ : 0 < Z)
    (x ell : ℝ) (s : ℂ) :
    ((Z ^ x : ℝ) : ℂ) ^ (1 / 3 : ℂ) * (Z : ℂ) ^ (s - 5 / 6) =
      (Z : ℂ) ^ (((-ell / 6 : ℝ) : ℂ)) *
        (Z : ℂ) ^ (s + (residueShift x ell : ℂ)) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le x (1 / 3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  dsimp [residueShift]
  push_cast
  ring

theorem normalized_source_double_residue_transported {κ ι : Type*}
    (x ell : ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H D : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hD : D 1 (1 / 6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z ^ x) Y Z χ s H D 1 (1 / 6)) /
        (sourceResidueConstant W0 W1 M *
          (Probe.principalScalar S Z ell (slotMass T w) : ℂ)) =
      (Z : ℂ) ^ (s + (residueShift x ell : ℂ)) *
        Complex.exp ((s - 5 / 6) ^ 2) * H 1 (1 / 6) / LFunction χ s *
        slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hD]
  have hp := transported_source_power_identity hZ x ell s
  have hz : (Z : ℂ) ^ (((-ell / 6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ) ^ (((-ell / 6 : ℝ) : ℂ)) *
          ((Z : ℂ) ^ (((-ell / 6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ) ^ (s + (residueShift x ell : ℂ)) *
          Complex.exp ((s - 5 / 6) ^ 2) * H 1 (1 / 6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring

end
end LW56e2.Transport.PhysicalAnalytic
