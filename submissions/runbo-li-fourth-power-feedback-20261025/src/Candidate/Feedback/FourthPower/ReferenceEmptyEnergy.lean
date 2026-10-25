/- Copyright (c) 2026 Sil. Apache-2.0.
The actual empty retained range is paid by the true approximation error.
Its length is never enlarged to one, preserving the extraction-ratio saving.
-/
import Candidate.Feedback.FourthPower.ReferenceOriginalEnergy

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.ReferenceEmptyEnergy
noncomputable section
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open ReferenceFactors ReferenceCrudeFactors ReferenceTailEnergy
open CenteredMomentNaturalPrimitive CenteredMomentOriginalReflectionApproximation
open CenteredMomentScaleSupremum
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]

/-- Uniform in all rows and all extraction choices. The only bound on the
remaining factors is their elementary polynomial volume bound. -/
theorem empty_reference (ε L K Ltail a b xi : ℝ)
    (hε : 0 ≤ ε) (hK : 0 < K) (ha : 0 < a) (hxi : 0 < xi) :
    ∃ n : ℕ, ∀ Wlong : ℝ → ℂ,
      Function.support Wlong ⊆ Icc a b → ContDiff ℝ ∞ Wlong →
      ∃ C : ℝ, 0 < C ∧ ∀ (Z R : ℝ), 1 ≤ Z → 0 ≤ R →
      ∀ (rows : Finset O) (χ : rows → Character),
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (χ i).residue ≠ 1) → (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ Z^K) →
      ∀ (U Xshort Height omega : ℝ) (X t : rows → ℝ) (Wshort : ℝ → ℂ)
        (d B : ℝ) (F : α → Factor),
      0 < Xshort → 0 ≤ Height → (∀ i, 0 < X i) →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) →
      (∀ i, 4*Z^(xi/2)*(U/X i) < 1) →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ Z^Ltail*X i) →
      (∀ i, ‖t i‖ ≤ Height) →
      0 ≤ d → 0 ≤ B → Function.support Wshort ⊆ Iic d →
      (∀ x, ‖Wshort x‖ ≤ B) → d*Xshort*(∏ i, (F i).length) ≤ Z^L →
      (∑ i : rows, ‖polynomial (χ i) false Wlong (X i) 0 (2*Real.pi*t i)*
        polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*
          ∏ j, (F j).value (χ i)‖^2) ≤
        C*(1+Height)^(2*n)*Z^(R+ε)*(Real.sqrt d*B*∏ j, (F j).amplitude)^2 := by
  obtain ⟨n,hn⟩ := ReferenceApproximation.original_approximation a b xi (L+1) K Ltail ha hxi hK
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨Ct,hCt,happrox⟩ := hn Wlong hs hW
  let κ : ℝ := 128^(Fintype.card α+1)
  refine ⟨128*(Ct*κ)^2,by dsimp [κ]; positivity,?_⟩
  intro Z R hZ hR rows χ hr hnonprincipal hmod
  intro U Xshort Height omega X t Wshort d B F hXshort hHeight hX hU hsmall hXcap ht
  intro hd hB hshort htest hvolume
  choose ψ G hprim hne hG hc he using fun i => happrox (χ i) (hnonprincipal i)
  let amp := Real.sqrt d*B*∏ j, (F j).amplitude
  let P (i : rows) := polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*∏ j, (F j).value (χ i)
  let e (i : rows) := polynomial (χ i) false Wlong (X i) 0 (2*Real.pi*t i)
  have hamp : 0 ≤ amp :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB)
      (Finset.prod_nonneg (fun i _ => (F i).amplitude_nonneg))
  have hP (i : rows) : ‖P i‖ ≤ κ*Z^L*amp := by
    exact (smooth_product_norm (χ i) Wshort d B Xshort omega hd hB hXshort htest hshort F).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvolume (by positivity)) hamp)
  have heBound (i : rows) : ‖e i‖ ≤ Ct*(1+Height)^n*Z^(-(L+1)) := by
    have hz := ReferenceRetainedGeometry.retainedOriginal_zero (χ i) (ψ i) Wlong
      (X i) U (Z^(xi/2)) (t i) (hX i) (by positivity) (hc i) (hU i) (hsmall i)
    have hh := he i (X i) (t i) Z (hX i) hZ (hmod i) (hXcap i)
    rw [hz,mul_zero,sub_zero] at hh
    apply hh.trans
    gcongr
    exact ht i
  have hh := powered_error_energy rows e P Z R ε L Ct κ Height amp n
    hZ hR hε hCt.le (by positivity) hHeight hamp hr heBound hP
  simpa only [e,P,amp,mul_assoc] using hh

end
end Candidate.Feedback.FourthPower.ReferenceEmptyEnergy
