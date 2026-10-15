/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B024
import Submissions.gao_cycle61_plane_20261013.Bundles.B032
import Submissions.gao_cycle61_plane_20261013.Bundles.B033
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalPhysicalRemainder
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RayPoolThresholds

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderBounds; sha256 8a05b6b032ecec354ab48f8e0c34c02bd5e769214db9d7846eb7498173042439 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                             
                                                 
                                                                    
noncomputable section

open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
namespace Cycle61.Transport.PrincipalRemainderBounds
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalRemainderBounds
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
open Cycle61.Transport.PrincipalFiniteProduct Cycle61.Transport.PrincipalFiniteProductX Cycle61.Transport.PrincipalContours
local notation "Id" => Ideal ActualEisensteinCubic.O

lemma active_prime_sum_bound (T : Finset PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B) (hP : 0<P)
    (hthreshold : 480 ≤ c*P) (hξ : ξ ≤ 1)
    (hW : ∀x,0 ≤ W x ∧ W x ≤ B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
       ≤ (128*d*B*c^(ξ-1))*P^ξ := by
  let A := T.filter (fun p=>W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : PrimeIdeal) (hp : p∈A) :
      c*P ≤ (Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ) ≤ d*P := by
    have h := hsupp (Finset.mem_filter.mp hp).2
    exact ⟨(le_div_iff₀ hP).mp h.1,(div_le_iff₀ hP).mp h.2⟩
  have he : (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))=
      ∑p∈A,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hw : W ((Ideal.absNorm p.val:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    simp [hw]
  have hcount : (A.card:ℝ) ≤ 128*(d*P) := by
    have h := DescentFiberCost.finite_ideal_count_real (A.image Subtype.val) (d*P)
      (by nlinarith) (by
        intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact (hA p hp).2)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  have hp (p : PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1) ≤ c^(ξ-1)*P^(ξ-1) := by
    rw [←Real.mul_rpow hc.le hP.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hP) (hA p hp).1 (by linarith [Cycle61.Transport.theta_bounds])
  rw [he]
  calc
    _ ≤ ∑_p∈A,B*(c^(ξ-1)*P^(ξ-1)) := Finset.sum_le_sum (fun p hpA=>
      mul_le_mul (hW _).2 (hp p hpA) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB)
    _=(A.card:ℝ)*(B*(c^(ξ-1)*P^(ξ-1))) := by simp
    _ ≤ (128*(d*P))*(B*(c^(ξ-1)*P^(ξ-1))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _=(128*d*B*c^(ξ-1))*P^ξ := by
      have heP : P*P^(ξ-1)=P^ξ := by
        calc
          _=P^(1:ℝ)*P^(ξ-1) := by rw [Real.rpow_one]
          _=P^ξ := by rw [←Real.rpow_add hP];congr 1;ring
      calc
        _=(128*d*B*c^(ξ-1))*(P*P^(ξ-1)) := by ring
        _=_ := by rw [heP]

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
    (T : ι→Finset PrimeIdeal) (s w z : ℂ)
    (hs : theta  ≤ s.re) (hw : 19/20 ≤ w.re) (hz : z.re=ξ) (hzlo : 33/200 ≤ ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖ ≤ 
      slotConstant J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=>W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : PrimeIdeal) (hp : p∈A j) : c*P j ≤ (Ideal.absNorm p.val:ℝ) :=
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
  have h := Cycle61.Transport.PrincipalFiniteProduct.combined_slot_bound_sharp η S hS J A
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
        exact mul_le_mul_of_nonneg_left (active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [slotConstant,←mul_assoc,Finset.prod_mul_distrib]

def scalePower (X Y Z a ξ υ : ℝ) : ℝ :=
  X^(1/2-ξ)*Z^(a+ξ-1)*Y^(υ-1)

lemma scalePower_nonneg {X Y Z a ξ υ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    0 ≤ scalePower X Y Z a ξ υ := by unfold scalePower;positivity

section Pointwise
variable {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
  (J : Finset ι) (c d B ξ : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
  (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B)
  (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
  (P : ι→ℝ) (hP : ∀j∈J,0<P j) (hthreshold : ∀j∈J,480 ≤ c*P j)
  (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) (T : ι→Finset PrimeIdeal)
  (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
  (ha : theta  ≤ a) (hυ : 19/20 ≤ υ) (hzlo : 33/200 ≤ ξ) (hC : 0 ≤ C)
  (hR : ∀s : ℂ,a ≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C*(1+|s.im|^2))

include hc hd hB hξ hW hsupp hP hthreshold hmod hX hY hZ ha hυ hzlo hC hR

lemma continued_source_sharp_pointwise (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)‖  ≤ 
    scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight t v u^2*‖onLines W0 W1 a ξ υ ((t,v),u)‖ := by
  have hslot := window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)‖ ≤ C*jointHeight t v u^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := Cycle61.Transport.PrincipalContours.height_le_joint_s t v u
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
    _=_ := by unfold scalePower;ring

lemma full_sharp_pointwise (hυhi : υ ≤ 2) (hυ1 : υ≠1) (hξ1 : 6*ξ≠1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖  ≤ 
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*
      (wAmplitude (∏q∈S,q) 2/|υ-1|)) *
      (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))*
      (jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := Cycle61.Transport.PrincipalContours.fixed_principal_z_bound (∏q∈S,q) 1 ξ p.1.2 ⟨hzlo,hξ⟩ hξ1
  have hlw := Cycle61.Transport.PrincipalContours.fixed_principal_w_bound (∏q∈S,q) (by norm_num : (1:ℝ)<2) ⟨hυ,hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (Cycle61.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏q∈S,q) 1) (abs_nonneg (6*ξ-1))
  have hAW := div_nonneg (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le (abs_nonneg (υ-1))
  have hmass : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
  have ht := (height_pos p.1.1).le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*height p.1.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*height p.2^3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _ ≤ (scalePower X Y Z a ξ υ*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight p.1.1 p.1.2 p.2^2*‖onLines W0 W1 a ξ υ p‖)*
      ((zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*jointHeight p.1.1 p.1.2 p.2^3)*
      ((wAmplitude (∏q∈S,q) 2/|υ-1|)*jointHeight p.1.1 p.1.2 p.2^3) := by
      have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=υ) hX.le hY.le hZ.le
      gcongr <;> first | positivity | exact Cycle61.Transport.PrincipalContours.height_le_joint_z _ _ _ | exact Cycle61.Transport.PrincipalContours.height_le_joint_w _ _ _
    _=_ := by ring

omit hυ in
lemma residue_sharp_pointwise (hξ1 : 6*ξ≠1) (q : ℝ×ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖  ≤ 
    (C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)) *
      (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ))*
      (jointHeight q.1 q.2 0^5*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one,ofReal_zero,zero_mul,add_zero] at h0
  have hlz := Cycle61.Transport.PrincipalContours.fixed_principal_z_bound (∏p∈S,p) 1 ξ q.2 ⟨hzlo,hξ⟩ hξ1
  have hAZ := div_nonneg (Cycle61.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏p∈S,p) 1) (abs_nonneg (6*ξ-1))
  have hmass : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hs := scalePower_nonneg (a:=a) (ξ:=ξ) (υ:=1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _ ≤ (scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*height q.2^3) := by
      gcongr ; first | positivity | exact h0 | exact hlz
    _ ≤ (scalePower X Y Z a ξ 1*(C*slotConstant J c d B ξ)*(∏j∈J,(P j)^ξ)*
      jointHeight q.1 q.2 0^2*‖onLines W0 W1 a ξ 1 ((q.1,q.2),0)‖)*
      ((zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr ; first | positivity | exact Cycle61.Transport.PrincipalContours.height_le_joint_z _ _ _
    _=_ := by ring
end Pointwise

lemma vertical_triple_eq_joint (F : ℂ→ℂ→ℂ→ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace=>F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>verticalIntegral υ (fun w=>F s w z))) =
    (((1/(2*Real.pi):ℝ):ℂ))^3*
      ∫p : HeightSpace,F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) ∂heightMeasure := by
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma vertical_pair_eq_joint (F : ℂ→ℂ→ℂ) (a ξ : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ=>F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>F s z)) =
    (((1/(2*Real.pi):ℝ):ℂ))^2*
      ∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume := by
  rw [integral_prod _ hi]
  simp only [verticalIntegral,integral_const_mul]
  ring

lemma normalizer_norm_pos : 0<‖(((1/(2*Real.pi):ℝ):ℂ))‖ := by
  apply norm_pos_iff.mpr
  exact_mod_cast (one_div_ne_zero (mul_ne_zero (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero))

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
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
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
        (scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏q∈S,q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (theta ) 2 (33/200) 1 (19/20) 2 (by norm_num) 8
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏q∈S,q) 1*wAmplitude (∏q∈S,q) 2*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := Cycle61.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏q∈S,q) 1
  have hWA := (wAmplitude_pos (∏q∈S,q) (by norm_num : (1:ℝ)<2)).le
  have hK : 0 ≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := Cycle61.Transport.PrincipalContours.continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := Cycle61.Transport.PrincipalContours.continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f:=fun p : HeightSpace=>
    LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))))).mul
    (EventuallyEq.rfl (f:=fun p : HeightSpace=>LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)))
  refine ⟨hi.congr hae',?_⟩
  refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏q∈S,q) 1/|6*ξ-1|)*(wAmplitude (∏q∈S,q) 2/|υ-1|)
  let E := scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hE : 0 ≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
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
    _ ≤ (K+1)/(|6*ξ-1| *|υ-1|)*E := by gcongr;linarith [Cycle61.Transport.theta_bounds]

theorem residue_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let F := fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
    Integrable F (volume.prod volume) ∧
      (∫q,‖F q‖ ∂volume.prod volume) ≤ K/|6*ξ-1| *
        (scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (theta ) 2 (33/200) 1 1 1 (by norm_num) 5 0
  let K := C*slotConstant J c d B ξ*zBoxAmplitude (∏p∈S,p) 1*D
  have hslot := slotConstant_nonneg J (ξ:=ξ) hc hd hB
  have hZA := Cycle61.Transport.PrincipalContours.zBoxAmplitude_nonneg (∏p∈S,p) 1
  have hK : 0 ≤ K := by dsimp [K];positivity
  refine ⟨K+1,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι→PrimeIdeal→ℂ := fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)
  have hi := Cycle61.Transport.PrincipalContours.continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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
    rw [Cycle61.Transport.PrincipalFiniteProductX.continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  refine ⟨hi.congr hae,?_⟩
  refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
  let A := C*slotConstant J c d B ξ*(zBoxAmplitude (∏p∈S,p) 1/|6*ξ-1|)
  let E := scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hE : 0 ≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
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
    _ ≤ (K+1)/|6*ξ-1| *E := by gcongr;linarith [Cycle61.Transport.theta_bounds]

theorem full_vertical_scale_bound (υ : ℝ) (hυ : υ∈Icc (19/20:ℝ) 2) (hυ1 : υ≠1) :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s=>verticalIntegral ξ (fun z=>verticalIntegral υ
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤ 
      K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := full_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 υ hυ hυ1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^3
  have hk : 0<k := pow_pos normalizer_norm_pos _
  refine ⟨k*K,mul_pos hk hK,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_triple_eq_joint _ a ξ υ hh.1,norm_mul,norm_pow]
  calc
    _ ≤ k*(∫p : HeightSpace,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le
    _ ≤ k*(K/(|6*ξ-1| *|υ-1|)*(scalePower X Y Z a ξ υ*(∏j∈J,(P j)^ξ))) :=
      mul_le_mul_of_nonneg_left hh.2 hk.le
    _=_ := by ring

theorem residue_vertical_scale_bound :
    ∃K : ℝ,0<K ∧ ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀P : ι→ℝ,
    (∀j∈J,0<P j) → (∀j∈J,480 ≤ c*P j) →
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral ξ
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖ ≤ 
      K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)) := by
  obtain ⟨K,hK,hbound⟩ := residue_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1/(2*Real.pi):ℝ):ℂ))‖^2
  have hk : 0<k := pow_pos normalizer_norm_pos _
  refine ⟨(1+‖R‖)*k*K,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hh := hbound W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hh
  rw [vertical_pair_eq_joint _ a ξ hh.1,norm_mul,norm_mul,norm_pow]
  calc
    _ ≤ (1+‖R‖)*(k*(∫q : ℝ×ℝ,‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I))
        (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ ∂volume.prod volume)) := by
      apply mul_le_mul (by dsimp [R];linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hk.le) (by positivity) (by positivity)
    _ ≤ (1+‖R‖)*(k*(K/|6*ξ-1| *(scalePower X Y Z a ξ 1*(∏j∈J,(P j)^ξ)))) := by
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
    (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀X Y Z : ℝ,0<X→0<Y→0<Z→
    let K0 := fun s=>sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤ 
      C/e*(scalePower X Y Z a (1/6+e) (19/20)*(∏j∈J,(P j)^(1/6+e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖ ≤ 
      C*(scalePower X Y Z a (33/200) 1*(∏j∈J,(P j)^(33/200:ℝ)))) := by
  obtain ⟨A,hA,hfirst⟩ := full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1/6+e) ha hβ ⟨by linarith [Cycle61.Transport.theta_bounds],by linarith [Cycle61.Transport.theta_bounds]⟩ (by linarith [Cycle61.Transport.theta_bounds])
    (19/20) (by norm_num) (by norm_num)
  obtain ⟨D,hD,hsecond⟩ := residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33/200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10/3)*A+100*D,by positivity,?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6*((1/6:ℝ)+e)-1|=6*e := by rw [abs_of_pos (by linarith [Cycle61.Transport.theta_bounds])];ring
  rw [hegap] at hf
  norm_num only [show |(19/20:ℝ)-1|=1/20 by norm_num] at hf
  norm_num only [show |6*(33/200:ℝ)-1|=1/100 by norm_num] at hg
  have hm (ξ : ℝ) : 0 ≤ ∏j∈J,(P j)^ξ := Finset.prod_nonneg (fun j hj=>Real.rpow_nonneg (hP j hj).le _)
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
    linarith [Cycle61.Transport.theta_bounds]

lemma source_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a ξ υ : ℝ) (hZ : 0<Z) :
    scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a ξ υ *
      (∏j∈J,(Z^(slotEll j))^ξ) =
    Z^(a-(4+b)/6+(h)*(ξ-1/6)+(ly)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(slotEll j))^ξ)=Z^((ell)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  rw [Cycle61.Transport.row_endpoint, Cycle61.Transport.b]; nlinarith [Cycle61.Transport.length_sum]

lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a e : ℝ) (hZ : 0<Z) :
    scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a (1/6+e) (19/20) *
      (∏j∈J,(Z^(slotEll j))^(1/6+e)) = Z^(a-(4+b)/6+(h)*e-ly/20) := by
  rw [source_scale_identity J slotEll hell Z a (1/6+e) (19/20) hZ]
  congr 1;rw [Cycle61.Transport.row_endpoint, Cycle61.Transport.b]; nlinarith [Cycle61.Transport.length_sum]

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (slotEll : ι→ℝ)
    (hell : ∑j∈J,slotEll j=ell) (Z a : ℝ) (hZ : 0<Z) :
    scalePower (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z a (33/200) 1 *
      (∏j∈J,(Z^(slotEll j))^(33/200:ℝ)) = Z^(a-(4+b)/6-h/600) := by
  rw [source_scale_identity J slotEll hell Z a (33/200) 1 hZ]
  congr 1;rw [Cycle61.Transport.row_endpoint, Cycle61.Transport.b]; nlinarith [Cycle61.Transport.length_sum]

theorem source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a e : ℝ) (ha : a∈Icc (theta :ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e ≤ 5/6) :
    ∃C : ℝ,0<C ∧ ∀(slotEll : ι→ℝ),(∑j∈J,slotEll j=ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
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
    (β+e)-(4+b)/6+(h)*e-ly/20 ≤ β-(4+b)/6-1/4000 := by nlinarith [Cycle61.Transport.h_interval, Cycle61.Transport.ly_coarse, Cycle61.Transport.theta_bounds]

lemma source_z_strict_exponent (β e : ℝ) (he : e ≤ 1/1000) :
    (β+e)-(4+b)/6-h/600 ≤ β-(4+b)/6-1/4000 := by nlinarith [Cycle61.Transport.h_interval, Cycle61.Transport.ly_coarse, Cycle61.Transport.theta_bounds]

theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e ≤ 1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Icc (theta :ℝ) 2) :
    ∃C : ℝ,0<C ∧ ∀(slotEll : ι→ℝ),(∑j∈J,slotEll j=ell) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0 ≤ W j x ∧ W j x ≤ B) →
    (∀j∈J,Function.support (W j)⊆Icc c d) → ∀T : ι→Finset PrimeIdeal,
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
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by nlinarith [Cycle61.Transport.h_interval, Cycle61.Transport.ly_coarse, Cycle61.Transport.theta_bounds]) he (by nlinarith [Cycle61.Transport.h_interval, Cycle61.Transport.ly_coarse, Cycle61.Transport.theta_bounds])
  refine ⟨C,hC,?_⟩
  intro slotEll hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound slotEll hell W hW hsupp T hT Z (by nlinarith [Cycle61.Transport.h_interval, Cycle61.Transport.ly_coarse, Cycle61.Transport.theta_bounds]) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end Cycle61.Transport.PrincipalRemainderBounds

end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderBounds -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderPhysical; sha256 a606236815466d886a9a8fb402966f4c8bb6c7e98bb7e41a15a3828833123d96 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                             
                                                             
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Cycle61.Transport.PrincipalPhysical
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
open Cycle61.Transport.PrincipalFiniteProduct Cycle61.Transport.PrincipalFiniteProductX Cycle61.Transport.PrincipalContours Cycle61.Transport.PrincipalTransport
local notation "Id" => Ideal HeckeFamily.O

lemma slotMultiplier_as_tuples {K : ℕ} (η : Character) (T : Fin K→Finset PrimeIdeal)
    (b : Fin K→PrimeIdeal→ℂ) (s w z : ℂ) :
    slotMultiplier η Finset.univ T b s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        slotMultiplier η Finset.univ (fun i=>{(P i).val}) (fun _ _=>1) s w z := by
  simp only [slotMultiplier,Finset.sum_singleton,one_mul]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (p : T i)=>b i p.val*localMultiplier η p.val s w z)]
  congr 1
  funext i
  exact (Finset.sum_coe_sort (T i) (fun p=>b i p*localMultiplier η p s w z)).symm

lemma principalPoolKernel_as_tuples {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (b : Fin K→PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    principalPoolKernel η S hS T b W0 W1 X Y Z s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z s w z := by
  unfold principalPoolKernel sourceMultiplier
  rw [slotMultiplier_as_tuples]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  ring

theorem principal_physical_pool_initial {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        principalPoolKernel η S hS T b W0 W1 X Y Z
          ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I) ∂heightMeasure := by
  let F (P : ∀i,T i) (t : HeightSpace) :=
    principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)
  have hF (P : ∀i,T i) : Integrable (F P) heightMeasure := by
    apply Cycle61.Transport.PrincipalContours.source_joint_integrable η S hS Finset.univ (fun i=>{(P i).val}) (fun _ _=>1)
      (by intro i hi p hp;simp only [Finset.mem_singleton] at hp;subst p;exact hT i _ (P i).property)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z 3 2 3 3 hX hY hZ
      (by first | (solve | norm_num) | (linarith [Cycle61.Transport.theta_bounds])) (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [principalPoolKernel_as_tuples η S hS T b W0 W1 X Y Z]
  rw [integral_finsetSum Finset.univ (fun P _=>(hF P).const_mul (∏i,b i (P i).val)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [principalRowIntegral_eq_sourceMultiplier η S hS (fun i=>(P i).val) (hdis P)
    (fun i=>hT i _ (P i).property) W0 W1 X Y Z,integral_const_mul]
  dsimp only [F,principalPoolKernel]
  ring

theorem principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : theta <a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e ≤ 11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact Cycle61.Transport.PrincipalTransport.source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

end Cycle61.Transport.PrincipalPhysical
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderPhysical -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderPhysicalBounds; sha256 66d6d3e52b04cfda176915704ead440187ef80f91f3b9207b85b6bca03aeff14 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                            
                                                          
                                                                      
noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace Cycle61.Transport.PrincipalPhysical
open OAI OAI.SevenEighths OAI.SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
open Cycle61.Transport.PrincipalFiniteProduct Cycle61.Transport.PrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e ≤ 1/1000)
    (ha : theta <HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e ≤ 2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀slotEll : Fin K→ℝ,(∑j,slotEll j)=ell → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0 ≤ W j x ∧ W j x ≤ B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1 ≤ Z → (∀j,480 ≤ c*Z^(slotEll j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(slotEll j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotEll j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(slotEll j)))‖ ≤ 
      C/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := Cycle61.Transport.PrincipalRemainderBounds.source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro slotEll hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith [Cycle61.Transport.theta_bounds]
  have hb := hbound slotEll hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := Cycle61.Transport.PrincipalPhysical.principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(slotEll j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(lx:ℝ)) (Z^(ly:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith [Cycle61.Transport.theta_bounds]) (by linarith [Cycle61.Transport.theta_bounds]) he (by linarith [Cycle61.Transport.theta_bounds])
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _ ≤ (2*C)/e*Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000)
  apply hn.trans
  have hCe : C ≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0 ≤ Z^(HeckeZeroSupremum.beta-(4+b)/6-1/4000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end Cycle61.Transport.PrincipalPhysical
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderPhysicalBounds -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderRayThresholds; sha256 71bbe104594738022270ef0a2b165c541d242f433f7dec3f3f14a469242cd962 -/
section
/- Ported from Cycle25.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                             
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Cycle61.Transport.PrincipalRaySlots
open OAI OAI.SevenEighths OAI.SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PrincipalSignalComparison ProbePrincipalResidueActual
open OAI.SevenEighths.ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

theorem power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0<c) (hd : c ≤ d) (hmin : 0<ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin ≤ ell j) :
    ∀ᶠZ : ℝ in atTop,
      1 ≤ Z ∧ 480 ≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(theta :ℝ)) ≤ 1 ∧
      (∀j,480 ≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)<c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin ≤ (P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(theta :ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by first | (solve | norm_num) | (linarith [Cycle61.Transport.theta_bounds]) : (0:ℝ)<theta )).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0<Z := by linarith [Cycle61.Transport.theta_bounds]
  have hmono (j : ι) : c*Z^ellMin ≤ c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

variable (M : Id) [NeZero M]
local instance : Finite (HeckeFamily.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
include hH

theorem power_ray_mass_and_normalizer {ι : Type*} [Fintype ι]
    (S : Finset Id) (W : ι→ℝ→ℝ) (c d : ℝ) (hc : 0<c) (hd : c ≤ d)
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hp : ∀j,tsupport (W j)⊆Set.Ioi 0) (hW0 : ∀j y,0 ≤ W j y) (hne : ∀j,W j≠0)
    (ell : ι→ℝ) (hell : ∀j,0<ell j) (eps : ℝ) (heps : 0<eps) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      (∀j,0<slotMass T (residueWeights W (fun j=>Z^(ell j))) j) ∧
      |(Probe.principalScalar Finset.univ Z (∑j,ell j)
        (slotMass T (residueWeights W (fun j=>Z^(ell j)))))⁻¹| ≤ Z^eps := by
  have hm : ∀ᶠZ : ℝ in atTop,∀j,0<slotMass
      (fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j)))
      (residueWeights W (fun j=>Z^(ell j))) j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop (hell j)).eventually
      (ray_pool_mass_eventually_positive M H hH S (W j) c d hc hd (hsupp j)
        (hW j) (hcompact j) (hp j) (hW0 j) (hne j))
  have hi := ProbeRayNormalization.ray_principalScalar_inverse_subpower M H hH Finset.univ S W
    (fun _=>c) (fun _=>d) ell (fun _ _=>hc) (fun _ _=>hd) (fun j _=>hsupp j)
    (fun j _=>hW j) (fun j _=>hcompact j) (fun j _=>hp j) (fun j _=>hW0 j) (fun j _=>hne j)
    (fun j _=>hell j) eps heps
  filter_upwards [hm,hi] with Z hmass hinv
  exact ⟨hmass,hinv⟩
end Cycle61.Transport.PrincipalRaySlots
end


end
/- END ORIGINAL Cycle61.Assembly.Transport.PrincipalRemainderRayThresholds -/
