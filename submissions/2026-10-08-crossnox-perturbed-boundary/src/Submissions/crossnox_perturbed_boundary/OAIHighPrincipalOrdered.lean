/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalOrdered.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalUniform

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem ordered_remainders_scale_bound_on_perturbed_boundary {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc PrincipalSlotEstimate.perturbedBoundary 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480≤c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*(scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*(scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := full_vertical_scale_bound_on_perturbed_boundary η S hS hTail J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith,by linarith⟩ (by linarith)
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := residue_vertical_scale_bound_on_perturbed_boundary η S hS hTail J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith)];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith


end SevenEighths.ProbePrincipalRemainderBounds
end

end OAI
