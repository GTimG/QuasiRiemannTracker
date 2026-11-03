import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry

/- The existing slot lengths and lowPhysicalScale at variable source powers.
   The total length and radial power are kept explicit. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.LowExtension
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbePhysical CompletedGauss

lemma lowLength_bounds (total : ℝ) {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤total) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤total ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤total-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma lowPhysicalScale_source (ξ υ : ℝ) (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^ξ/L) (Z^υ/L)=
      elementNorm C.generator*Z^((ξ+υ):ℝ)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^ξ*Z^υ=Z^((ξ+υ):ℝ) := by rw [←Real.rpow_add hZ]
  rw [←he]
  ring

lemma lowPhysicalScale_nominal_bound (ξ υ : ℝ) (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^ξ/L) (Z^υ/L)≤
      (elementNorm C.generator/c^2)*Z^((ξ+υ)-2*d:ℝ) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [lowPhysicalScale_source ξ υ C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^((ξ+υ):ℝ)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring


#print axioms lowLength_bounds
#print axioms lowPhysicalScale_source
#print axioms lowPhysicalScale_nominal_bound
end
end BelowSevenEighthsTight.LowExtension
