/- Copyright (c) 2026 Sil. Apache-2.0.
Energy of the actual retained original polynomial. The baseline supplies its
exact weighted-series identity and index masks; the new sieve supplies the
common-profile energy. No analytic estimate is left as a premise.
-/
import Candidate.SilPrior.FourthPower.ReferenceProfileEnergy
import Candidate.SilPrior.FourthPower.ReferenceRetainedGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedComparisonEnergy

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.ReferenceRetainedEnergy
noncomputable section
open scoped Classical BigOperators ContDiff
open Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open CanonicalRowCompletion CanonicalQuadraticSieve
open ReferenceFactors ReferenceHeckeProducts ReferenceProfileEnergy ReferenceRetainedGeometry
open CenteredMomentNaturalPrimitive CenteredMomentOriginalReflectionApproximation
open CenteredMomentRetainedWeightedSource CenteredMomentRetainedComparisonEnergy
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOneReflectionScaleEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]

theorem retained_reference (ε L K a b : ℝ)
    (hε : 0 < ε) (hL : 0 < L) (hK : 0 < K) (ha : 0 < a) :
    ∃ n : ℕ, ∀ Wlong : ℝ → ℂ,
      Function.support Wlong ⊆ Icc a b → ContDiff ℝ ∞ Wlong →
      ∃ C : ℝ, 0 < C ∧ ∀ (Z R v y N T : ℝ),
      1 ≤ Z → 0 ≤ R → 1 ≤ N → 0 ≤ T →
      R+v ≤ L → v ≤ (4/5)*R → y ≤ R/2 → N ≤ Z^v → N ≤ Z^y*T →
      ∀ (η : Character) (m D : O) (rows : Finset O) (χ ψ : rows → Character),
      (∀ x I, Supported I → idealCoeff (χ x) I = fixedCoefficient η m D I*idealRowHom x.val I) →
      (∀ x I, ¬Supported I → idealCoeff (χ x) I = 0) →
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ Z^R) →
      (∀ i, (ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm ≤
        (χ i).modulus.absNorm) → (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ Z^K) →
      ∀ (U A Y Xshort Height omega : ℝ) (X t : rows → ℝ) (Wshort : ℝ → ℂ)
        (c d B : ℝ) (F : α → Factor),
      0 ≤ A → 1 ≤ Y → 0 < Xshort → 0 ≤ Height → (∀ i, 0 < X i) →
      (∀ i, ((χ i).modulus.absNorm : ℝ) ≤ U) → (∀ i, 4*A*(U/X i) ≤ Y) →
      (∀ i, ‖t i‖ ≤ Height) →
      0 ≤ d → 0 ≤ B → Function.support Wshort ⊆ Icc c d → ContDiff ℝ ∞ Wshort →
      (∀ (j : Fin 2) (x : ℝ), ‖scaleTest Wshort j x‖ ≤ B) →
      Y*(d*Xshort)*(∏ i, (F i).length) ≤ N →
      (∑ i : rows, ‖retainedOriginal (χ i) (ψ i) Wlong (X i) A (t i)*
        polynomial (χ i) false Wshort Xshort 0 (2*Real.pi*omega)*
          ∏ j, (F j).value (χ i)‖^2) ≤
        C*(1+Height)^(2*n)*(1+2*Real.log Y)*Z^(R+ε)*(3+T^(1/3 : ℝ))*
          (Real.sqrt d*B*∏ j, (F j).amplitude)^2 := by
  obtain ⟨C₀,hC₀,henergy⟩ := two_smooth_product (α:=α) (ε/2) L (by positivity) hL
  obtain ⟨B₀,hB₀,hAnn⟩ := bounded_scaleTests (fun z : ℝ => (annulus z : ℂ)) (1/4) 1
    annulus_complex_support annulus_complex_smooth
  obtain ⟨n,hn⟩ := actual_retained_fixed_profile_energy a b (ε/(2*K)) ha (by positivity) 2 0 le_rfl
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C₁,hC₁,hretained⟩ := hn Wlong hs hW
  refine ⟨C₁*C₀*B₀^2,mul_pos (mul_pos hC₁ hC₀) (sq_pos_of_pos hB₀),?_⟩
  intro Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ ψ hon hoff hr hc hmod
  intro U A Y Xshort Height omega X t Wshort c d B F hA hY hXshort hHeight hX hU hYcap ht
  intro hd hB hshort hshortsmooth htest hlen
  let E := C₀*Z^(R+ε/2)*(3+T^(1/3 : ℝ))*(B₀*(Real.sqrt d*B)*∏ j, (F j).amplitude)^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  have hp : 0 ≤ ∏ i, (F i).length := Finset.prod_nonneg (fun i _ => (F i).length_nonneg)
  have hcommon (freq : ℝ) (j k : Fin 2) (x : ℝ) (hx : x ∈ Icc 0 (Real.log Y))
      (z : ℝ) (hz : z ∈ Icc (Real.log Xshort) (Real.log Xshort)) :
      (∑ i : rows, ‖polynomial (χ i) false (scaleTest (fun z : ℝ => (annulus z : ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*freq)*
        polynomial (χ i) false (scaleTest Wshort k) (Real.exp z) 0 (2*Real.pi*omega)*
          ∏ j, (F j).value (χ i)‖^2) ≤ E*(1+‖freq‖)^(2*0) := by
    have hz' : Real.exp z = Xshort := by rw [le_antisymm hz.2 hz.1,Real.exp_log hXshort]
    have hx' : Real.exp x ≤ Y := (Real.exp_le_exp.mpr hx.2).trans_eq (Real.exp_log hYpos)
    have hlength : (1*Real.exp x)*(d*Real.exp z)*(∏ i, (F i).length) ≤ N := by
      rw [hz',one_mul]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx' (by positivity)) hp).trans hlen
    have hh := henergy Z R v y N T hZ hR hN hT hcap hv hy hmax href η m D rows χ hon hoff hr
      (scaleTest (fun z : ℝ => (annulus z : ℂ)) j) (scaleTest Wshort k)
      1 d B₀ B (Real.exp x) (Real.exp z) (-freq) omega F (by norm_num) hd hB₀.le hB
      (Real.exp_pos x) (Real.exp_pos z) (hAnn j) (htest k)
      (fun q hq => (scaleTest_support _ _ _ annulus_complex_support j hq).2)
      (fun q hq => (scaleTest_support Wshort c d hshort k hq).2) hlength
    rw [show 2*Real.pi*(-freq) = -2*Real.pi*freq by ring] at hh
    simpa only [E,Real.sqrt_one,one_mul,Nat.mul_zero,pow_zero,mul_one] using hh
  have hrad (i : rows) : (Ideal.absNorm (∏ P ∈ sourcePrimes (χ i) (ψ i), P) : ℝ) ≤ Z^K :=
    (radical_le_original (χ i) (ψ i) (hc i)).trans (hmod i)
  have hh := hretained χ ψ (fun i => ∏ j, (F j).value (χ i)) X (fun _ => A) t
    (fun _ => Real.log Xshort) (fun _ => 2*Real.pi*omega) Wshort c d 0 (Real.log Y)
    (Real.log Xshort) (Real.log Xshort) E Height (Z^K) hX hd hshort hshortsmooth
    (Real.log_nonneg hY) le_rfl (fun _ => ⟨le_rfl,le_rfl⟩)
    (fun i u hYu hu => retained_log_box (χ i) (ψ i) (X i) U A Y (hX i) hA
      (hc i) (hU i) (hYcap i) u hYu hu)
    hE hHeight ht (Real.one_le_rpow hZ hK.le) hrad hcommon
  simp only [Real.exp_log hXshort,sub_zero,sub_self,mul_zero,add_zero,mul_one] at hh
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hpow : (Z^K)^(ε/(2*K))*Z^(R+ε/2) = Z^(R+ε) := by
    rw [← Real.rpow_mul hz.le,← Real.rpow_add hz]
    congr 1
    field_simp
    ring
  apply hh.trans_eq
  dsimp only [E]
  calc
    _ = (C₁*C₀*B₀^2)*(1+Height)^(2*n)*(1+2*Real.log Y)*
        ((Z^K)^(ε/(2*K))*Z^(R+ε/2))*(3+T^(1/3 : ℝ))*
          (Real.sqrt d*B*∏ j, (F j).amplitude)^2 := by ring
    _ = _ := by rw [hpow]

end
end Candidate.SilPrior.FourthPower.ReferenceRetainedEnergy
