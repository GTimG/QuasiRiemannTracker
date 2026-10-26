/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Transport.GeometryFacts
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Transport.PrincipalRemainderTransport
import Candidate.Research.RecursiveAffine.Endpoint.Cycle63.Assembly.Transport.PrincipalSignal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.PrincipalRemainderBounds

noncomputable local instance endpointFixedLedger_Candidate_Cycle63_Assembly_Transport_PrincipalRemainderBounds : Cycle63.AffineLedger := Cycle153.Root.rootLedger

noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace Cycle153Endpoint.Transport.PrincipalRemainderBounds
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
open Cycle153Endpoint.Transport.PrincipalFiniteProduct Cycle153Endpoint.Transport.PrincipalFiniteProductX Cycle153Endpoint.Transport.PrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

def slotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3/2)*∏_j∈J,(1+1440*(480:ℝ)^(-(theta :ℝ)))*(128*d*B*c^(ξ-1))

lemma slotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B) : 0 ≤ slotConstant J c d B ξ := by
  have hd0 : 0 ≤ d := hc.le.trans hd
  unfold slotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=>by positivity)

theorem window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0<P j)
    (hthreshold : ∀j∈J,480 ≤ c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j)
    (T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (s w z : ℂ)
    (hs : theta  ≤ s.re) (hw : 19/20 ≤ w.re) (hz : z.re=ξ) (hzlo : 33/200 ≤ ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖ ≤
      slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=>W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hp : p∈A j) : c*P j ≤ (Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := Cycle153Endpoint.Transport.PrincipalFiniteProduct.combined_slot_bound_sharp η S hS J A
    (fun j p=>W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=>PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _ ≤ (3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(theta :ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=>by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (WeightedQRH.PrincipalRemainderBounds.active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [slotConstant,←mul_assoc,Finset.prod_mul_distrib]

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0<P j) (hthreshold : ∀j∈J,480 ≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) (T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
  (ha : theta  ≤ a) (hυ : 19/20 ≤ υ) (hzlo : 33/200 ≤ ξ) (hC : 0 ≤ C)
  (hR : ∀s : ℂ,a ≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖  ≤
    WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖ ≤ C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := WeightedQRH.PrincipalContours.height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t,abs_nonneg v,abs_nonneg u]
  have hx : ‖(X:ℂ)^(1/2-((ξ:ℂ)+v*I))‖=X^(1/2-ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX];congr 1;simp
  have hz : ‖(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)‖=Z^(a+ξ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ];congr 1;simp
  have hy : ‖(Y:ℂ)^(((υ:ℂ)+u*I)-1)‖=Y^(υ-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY];congr 1;simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) =
      (X:ℂ)^(1/2-((ξ:ℂ)+v*I))*(Z:ℂ)^(((a:ℂ)+t*I)+((ξ:ℂ)+v*I)-1)*
      (Y:ℂ)^(((υ:ℂ)+u*I)-1)*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)*
      (globalClosedCorrection η S ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)*
        windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I))*
      onLines W0 W1 a ξ υ ((t,v),u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile;ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,norm_mul,hx,hz,hy]
  calc
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)*(C*jointHeight t v u^2)*
      (slotConstant J c d B ξ*(∏j∈J,(P j)^ξ))*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
      gcongr
    _=_ := by unfold WeightedQRH.PrincipalRemainderBounds.scalePower;ring

lemma full_sharp_pointwise (hυhi : υ ≤ 2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖  ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := WeightedQRH.PrincipalContours.fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := WeightedQRH.PrincipalContours.fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (WeightedQRH.PrincipalContours.zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := WeightedQRH.PrincipalRemainderBounds.scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _ ≤ (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := WeightedQRH.PrincipalRemainderBounds.scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact WeightedQRH.PrincipalContours.height_le_joint_z _ _ _ | exact WeightedQRH.PrincipalContours.height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖  ≤
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := WeightedQRH.PrincipalContours.fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (WeightedQRH.PrincipalContours.zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := WeightedQRH.PrincipalRemainderBounds.scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _ ≤ (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _ ≤ (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact WeightedQRH.PrincipalContours.height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

section Uniform
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
  (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
  (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
  (a ξ : ℝ) (ha : a∈Icc (theta :ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
  (hξ : ξ∈Icc (33/200:ℝ) 1) (hξ1 : 6*ξ≠1)
include hc hd hB ha0 ha1 hW0 hW1 ha hβ hξ hξ1

theorem full_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    Integrable F heightMeasure ∧
      (∫p,‖F p‖ ∂heightMeasure) ≤ K/(|6*ξ-1| *|υ-1|)*
        (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (theta ) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := WeightedQRH.PrincipalContours.zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0 ≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := Cycle153Endpoint.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := WeightedQRH.PrincipalContours.continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=>LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hE : 0 ≤ E := mul_nonneg (WeightedQRH.PrincipalRemainderBounds.scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  calc
    _ ≤ ∫p : HeightSpace,A*E*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) ∂heightMeasure := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro p
      exact full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
    _=A*E*(∫p : HeightSpace,jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _ ≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/(|6*ξ-1| *|υ-1|)*E := by dsimp [A,K];simp only [div_eq_mul_inv,mul_inv_rev];ring
    _ ≤ (K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith [Cycle153Endpoint.Transport.theta_bounds]

theorem residue_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume) ≤ K/|6*ξ-1| *
        (WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (theta ) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := WeightedQRH.PrincipalContours.zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0 ≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := Cycle153Endpoint.Transport.PrincipalContours.continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha.1 hβ hξ.1 hξ1
  have hae : (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I)) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h;exact hq (by simpa using congrArg Complex.im h)
    rw [WeightedQRH.PrincipalFiniteProductX.continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hE : 0 ≤ E := mul_nonneg (WeightedQRH.PrincipalRemainderBounds.scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl,le_rfl⟩ .w 0
  simp only [sliceMap,pow_zero,div_one] at hp
  calc
    _ ≤ ∫q : ℝ×ℝ,A*E*(jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) ∂volume.prod volume := by
      apply integral_mono hi.norm (hp.1.const_mul (A*E))
      intro q
      exact residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
        hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
    _=A*E*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖ ∂volume.prod volume) := integral_const_mul _ _
    _ ≤ A*E*D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
    _=K/|6*ξ-1| *E := by dsimp [A,K];ring
    _ ≤ (K+1)/|6*ξ-1| *E := by gcongr;linarith [Cycle153Endpoint.Transport.theta_bounds]

theorem full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>verticalIntegral υ
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤
      K/(|6*ξ-1| *|υ-1|)*(WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0<k := pow_pos WeightedQRH.PrincipalRemainderBounds.normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [WeightedQRH.PrincipalRemainderBounds.vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
  calc
    _ ≤ k*(∫p : HeightSpace,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
    _ ≤ k*(K/(|6*ξ-1| *|υ-1|)*(WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))) :=
      mul_le_mul_of_nonneg_left hh.2 hk.le
    _=_ := by ring

theorem residue_vertical_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral ξ
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖ ≤
      K/|6*ξ-1| *(WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0<k := pow_pos WeightedQRH.PrincipalRemainderBounds.normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [WeightedQRH.PrincipalRemainderBounds.vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ (1+‖R‖)*(k*(∫q : ℝ×ℝ,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ∂volume.prod volume)) := by
      apply mul_le_mul (by dsimp [R];linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le) (by positivity) (by positivity)
    _ ≤ (1+‖R‖)*(k*(K/|6*ξ-1| *(WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)))) := by
      gcongr;exact hh.2
    _=_ := by ring
end Uniform

theorem ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (theta :ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e ≤ 5/6) :
    ∃C : ℝ,0<C ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤
      C/e*(WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖ ≤
      C*(WeightedQRH.PrincipalRemainderBounds.scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith [Cycle153Endpoint.Transport.theta_bounds],by linarith [Cycle153Endpoint.Transport.theta_bounds]⟩ (by linarith [Cycle153Endpoint.Transport.theta_bounds])
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith [Cycle153Endpoint.Transport.theta_bounds])];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (WeightedQRH.PrincipalRemainderBounds.scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A/(6*e*(1/20))=((10/3)*A)/e := by field_simp;ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (WeightedQRH.PrincipalRemainderBounds.scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith [Cycle153Endpoint.Transport.theta_bounds]

lemma source_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a ξ υ : ℝ) (hZ : 0<Z) :
    WeightedQRH.PrincipalRemainderBounds.scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(slotEll j))^ξ) =
    Z^(a-(4+b)/6+(h)*(ξ-1/6)+(ly)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(slotEll j))^ξ)=Z^((ell)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,WeightedQRH.PrincipalRemainderBounds.scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  rw [Cycle153Endpoint.Transport.row_endpoint, Cycle153Endpoint.Transport.b]; nlinarith [Cycle153Endpoint.Transport.length_sum]

lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a e : ℝ) (hZ : 0<Z) :
    WeightedQRH.PrincipalRemainderBounds.scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(slotEll j))^(1/6+e)) = Z^(a-(4+b)/6+(h)*e-ly/20) := by
  rw [source_scale_identity J slotEll hell Z a (1/6+e) (19/20) hZ]
  congr 1;rw [Cycle153Endpoint.Transport.row_endpoint, Cycle153Endpoint.Transport.b]; nlinarith [Cycle153Endpoint.Transport.length_sum]

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a : ℝ) (hZ : 0<Z) :
    WeightedQRH.PrincipalRemainderBounds.scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(slotEll j))^(33/200:ℝ)) = Z^(a-(4+b)/6-h/600) := by
  rw [source_scale_identity J slotEll hell Z a (33/200) 1 hZ]
  congr 1;rw [Cycle153Endpoint.Transport.row_endpoint, Cycle153Endpoint.Transport.b]; nlinarith [Cycle153Endpoint.Transport.length_sum]

theorem source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (theta :ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e ≤ 5/6) :
    ∃C : ℝ,0<C ∧ ∀(slotEll : ι→ℝ),(∑j∈J,slotEll j=ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0<Z→
    (∀j∈J,480 ≤ c*Z^(slotEll j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(slotEll j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(slotEll j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤
      C/e*Z^(a-(4+b)/6+(h)*e-ly/20)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖ ≤ C*Z^(a-(4+b)/6-h/600)) := by
  obtain ⟨C,hC,hbound⟩ := ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro slotEll hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=>Z^(slotEll j)) (fun _ _=>Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [source_w_scale_identity J slotEll hell Z a e hZ,source_z_scale_identity J slotEll hell Z a hZ] at hh
  exact hh

lemma source_w_strict_exponent (β e : ℝ) (he : e ≤ 1/1000) :
    (β+e)-(4+b)/6+(h)*e-ly/20 ≤ β-(4+b)/6-1/4000 := by nlinarith [Cycle153Endpoint.Transport.h_interval, Cycle153Endpoint.Transport.ly_coarse, Cycle153Endpoint.Transport.theta_bounds]

lemma source_z_strict_exponent (β e : ℝ) (he : e ≤ 1/1000) :
    (β+e)-(4+b)/6-h/600 ≤ β-(4+b)/6-1/4000 := by nlinarith [Cycle153Endpoint.Transport.h_interval, Cycle153Endpoint.Transport.ly_coarse, Cycle153Endpoint.Transport.theta_bounds]

theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e ≤ 1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (theta :ℝ) 2) :
    ∃C : ℝ,0<C ∧ ∀(slotEll : ι→ℝ),(∑j∈J,slotEll j=ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1 ≤ Z→
    (∀j∈J,480 ≤ c*Z^(slotEll j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(slotEll j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(slotEll j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>verticalIntegral (1/6+e)
      (fun z=>verticalIntegral (19/20) (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤
      C/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=>verticalIntegral (33/200) (fun z=>K0 s 1 z*LFunction π (6*z)))‖ ≤
      C*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by nlinarith [Cycle153Endpoint.Transport.h_interval, Cycle153Endpoint.Transport.ly_coarse, Cycle153Endpoint.Transport.theta_bounds]) he (by nlinarith [Cycle153Endpoint.Transport.h_interval, Cycle153Endpoint.Transport.ly_coarse, Cycle153Endpoint.Transport.theta_bounds])
  refine ⟨C,hC,?_⟩
  intro slotEll hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound slotEll hell W hW hsupp T hT Z (by nlinarith [Cycle153Endpoint.Transport.h_interval, Cycle153Endpoint.Transport.ly_coarse, Cycle153Endpoint.Transport.theta_bounds]) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end Cycle153Endpoint.Transport.PrincipalRemainderBounds

end
