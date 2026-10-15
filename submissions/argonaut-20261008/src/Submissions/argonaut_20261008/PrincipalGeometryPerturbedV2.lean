import Submissions.argonaut_20261008.PrincipalBoundaryB0
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds

namespace OAI.SevenEighths.LocalPrincipalGeometryV2
noncomputable section
open scoped BigOperators
open ProbePrincipalRemainderBounds

abbrev rho : ℝ := Parameters.perturbedRho
abbrev E : ℝ := Parameters.perturbedTotalE
abbrev H : ℝ := Parameters.perturbedHeight
abbrev lx : ℝ := 17 / 48 - rho / 2
abbrev ly : ℝ := 23 / 48 - rho / 2

lemma geometry : 2 * lx + E = (7 / 8 : ℝ) := by
  norm_num [lx, E, rho, Parameters.perturbedTotalE, Parameters.perturbedRho]

lemma height_geometry : 1 - lx + E = H := by
  norm_num [lx, E, H, rho, Parameters.perturbedTotalE,
    Parameters.perturbedHeight, Parameters.perturbedRho]

lemma residue_exponent {x total : ℝ} (hg : 2 * x + total = (7 / 8 : ℝ)) :
    x / 3 + total / 6 = (7 / 48 : ℝ) := by linarith

/-- Generic identity, independent of any fixed old slot mass or row height. -/
lemma source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (x y total : ℝ) (hsum : ∑ j ∈ J, ell j = total)
    (hg : 2 * x + total = (7 / 8 : ℝ))
    (Z a ξ υ : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ x) (Z ^ y) Z a ξ υ * (∏ j ∈ J, (Z ^ ell j) ^ ξ) =
      Z ^ (a - 11 / 16 + (1 - x + total) * (ξ - 1 / 6) + y * (υ - 1)) := by
  have hp : (∏ j ∈ J, (Z ^ ell j) ^ ξ) = Z ^ (total * ξ) := by
    simp only [← Real.rpow_mul hZ.le]
    rw [← Real.rpow_sum_of_pos hZ, ← Finset.sum_mul, hsum]
  rw [hp, scalePower, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  nlinarith [residue_exponent hg]

lemma actual_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hsum : ∑ j ∈ J, ell j = E) (Z a ξ υ : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ lx) (Z ^ ly) Z a ξ υ * (∏ j ∈ J, (Z ^ ell j) ^ ξ) =
      Z ^ (a - 11 / 16 + H * (ξ - 1 / 6) + ly * (υ - 1)) := by
  simpa only [height_geometry] using
    source_scale_identity J ell lx ly E hsum geometry Z a ξ υ hZ

lemma actual_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hsum : ∑ j ∈ J, ell j = E) (Z a e : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ lx) (Z ^ ly) Z a (1 / 6 + e) (19 / 20) *
      (∏ j ∈ J, (Z ^ ell j) ^ (1 / 6 + e)) =
      Z ^ (a - 11 / 16 + H * e - ly / 20) := by
  rw [actual_scale_identity J ell hsum Z a (1 / 6 + e) (19 / 20) hZ]
  congr 1
  ring

lemma actual_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hsum : ∑ j ∈ J, ell j = E) (Z a : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ lx) (Z ^ ly) Z a (33 / 200) 1 *
      (∏ j ∈ J, (Z ^ ell j) ^ (33 / 200 : ℝ)) =
      Z ^ (a - 11 / 16 - H / 600) := by
  rw [actual_scale_identity J ell hsum Z a (33 / 200) 1 hZ]
  congr 1
  ring

/-- The pole remains z=1/6; total is only the principalScalar exponent. -/
lemma source_power_identity {Z x total : ℝ}
    (hZ : 0 < Z) (hg : 2 * x + total = (7 / 8 : ℝ)) (s : ℂ) :
    ((Z ^ x : ℝ) : ℂ) ^ (1 / 3 : ℂ) * (Z : ℂ) ^ (s - 5 / 6) =
      (Z : ℂ) ^ (((-total / 6 : ℝ) : ℂ)) * (Z : ℂ) ^ (s - 11 / 16) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le x (1 / 3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  have hexp := residue_exponent hg
  have heq : x / 3 - 5 / 6 = -total / 6 - (11 / 16 : ℝ) := by linarith
  have hc : ((x : ℂ) * (1 / 3) - 5 / 6) =
      (((-total / 6 : ℝ) : ℂ)) - 11 / 16 := by
    have heqC := congrArg (fun r : ℝ => (r : ℂ)) heq
    push_cast at heqC
    convert heqC using 1 <;> push_cast <;> ring
  calc
    (x : ℂ) * (1 / 3) + (s - 5 / 6) = s + ((x : ℂ) * (1 / 3) - 5 / 6) := by ring
    _ = _ := by rw [hc]; ring

lemma w_strict_exponent (β e : ℝ) (he : e ≤ 1 / 1000) :
    (β + e) - 11 / 16 + H * e - ly / 20 ≤ β - 11 / 16 - 17 / 48000 := by
  norm_num [H, ly, rho, Parameters.perturbedHeight, Parameters.perturbedRho] at ⊢
  linarith

lemma z_strict_exponent (β e : ℝ) (he : e ≤ 1 / 1000) :
    (β + e) - 11 / 16 - H / 600 ≤ β - 11 / 16 - 17 / 48000 := by
  norm_num [H, Parameters.perturbedHeight, Parameters.perturbedRho] at ⊢
  linarith

end
end OAI.SevenEighths.LocalPrincipalGeometryV2
