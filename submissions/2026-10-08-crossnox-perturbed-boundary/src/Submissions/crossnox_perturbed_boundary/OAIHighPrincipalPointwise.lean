/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighPrincipalPointwise.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighPrincipalSharp

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem continued_source_sharp_pointwise_on_perturbed_boundary {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (hTail : PerturbedCorrectionTail S)
    (J : Finset ι) (c d B ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (hξ : ξ≤1) (W : ι→ℝ→ℝ)
    (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0<P j)
    (hthreshold : ∀j∈J,480≤c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j)
    (T : ι→Finset PrimeIdeal)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ)
    (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : PrincipalSlotEstimate.perturbedBoundary≤a)
    (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤C)
    (hR : ∀s : ℂ,a≤s.re→
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤
        C*(1+|s.im|^2)) (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖ ≤
    scalePower X Y Z a ξ υ*(C*perturbedSlotConstant J c d B ξ)*
      (∏j∈J,(P j)^ξ)*jointHeight t v u^2*
      ‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := window_sharp_bound_on_perturbed_boundary
    η S hTail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I)
    ((ξ:ℂ)+v*I) (by simpa using ha) (by simpa using hυ)
    (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime)
      ((a:ℂ)+t*I)‖≤C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,
      mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t,abs_nonneg v,abs_nonneg u]
  have hx : ‖(X:ℂ)^(1/2-((ξ:ℂ)+v*I))‖=X^(1/2-ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    congr 1
    simp
  have hz : ‖(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)‖=Z^(a+ξ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    congr 1
    simp
  have hy : ‖(Y:ℂ)^(((υ:ℂ)+u*I)-1)‖=Y^(υ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    congr 1
    simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) =
      (X:ℂ)^(1/2-((ξ:ℂ)+v*I))*(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)*
      (Y:ℂ)^(((υ:ℂ)+u*I)-1)*
      HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)*
      (globalClosedCorrection η S ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)*
        windowMultiplier η J T (fun j x=>(W j x:ℂ)) P
          ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I))*
      onLines W0 W1 a ξ υ ((t,v),u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile
    ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,hx,hz,hy]
  calc
    _≤X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (perturbedSlotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*
      ‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold scalePower; ring

section PerturbedPointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S) (hTail : PerturbedCorrectionTail S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0<P j) (hthreshold : ∀j∈J,480≤c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) (T : ι→Finset PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
  (ha : PrincipalSlotEstimate.perturbedBoundary≤a) (hυ : 19/20≤υ) (hzlo : 33/200≤ξ) (hC : 0≤C)
  (hR : ∀s : ℂ,a≤s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤C*(1+|s.im|^2))

include hTail hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR


lemma full_sharp_pointwise_on_perturbed_boundary (hυhi : υ≤2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
    (C*perturbedSlotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise_on_perturbed_boundary η S hS hTail J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := perturbed_slot_constant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _≤(scalePower X Y Z a ξ υ*(C*perturbedSlotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _≤(scalePower X Y Z a ξ υ*(C*perturbedSlotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma residue_sharp_pointwise_on_perturbed_boundary (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ≤
    (C*perturbedSlotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise_on_perturbed_boundary η S hS hTail J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0≤∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := perturbed_slot_constant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _≤(scalePower X Y Z a ξ 1*(C*perturbedSlotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _≤(scalePower X Y Z a ξ 1*(C*perturbedSlotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact height_le_joint_z _ _ _
    _=_ := by ring
end PerturbedPointwise

end SevenEighths.ProbePrincipalRemainderBounds
end

end OAI
