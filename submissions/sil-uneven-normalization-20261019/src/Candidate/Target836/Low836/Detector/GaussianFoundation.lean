import Candidate.Target836.Low836.Detector.InverseEnergy
import Candidate.Target836.Low836.Detector.LowNominalGeometry
import Candidate.Target836.Low836.Detector.LowSlotScales
import Candidate.Target836.Low836.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralTuple
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import Candidate.Target836.Low836.Detector.LowCentralGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowGaussianDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowRemoteMass

/- Original module: Candidate.Target836.Low836.Detector.TupleBound. -/
section
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Detector/LowUnselectedMass, Detector/LowCentralTuple.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle63. -/
namespace OAI
noncomputable section
namespace SevenEighths.Target836ProbeLow
section
open scoped Classical
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}
lemma canonical_slot_inverse_three_halves : ∃C : ℝ,0< C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))≤ C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2:ℝ)) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=> I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-(3/2:ℝ)) := by
    rw [Finset.sum_image (fun P _ Q _ h=> hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=> elementNorm a.val^(-(3/2:ℝ)))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _
lemma lowUnselectedWeight_norm_identity {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖ =
      ∏i : J,elementNorm (a i).val^(-(3/2:ℝ))*‖W i.val (elementNorm (a i).val/P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  rw [elementNorm_finset_prod,Finset.prod_mul_distrib,Real.finsetProd_rpow Finset.univ
    (fun i : J=> elementNorm (a i).val) (fun i _=> by unfold elementNorm;positivity)]
theorem lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤ M) :
    ∃C : ℝ,0< C ∧ ∀(T : Fin K→Finset PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤ M)→
      (∑a : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P a‖)≤ C := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_three_halves
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=> canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-(3/2:ℝ))*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod₀ (fun i _=> Finset.sum_nonneg (fun a _=> mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ))*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ)))*M := (Finset.sum_mul ..).symm
        _≤ C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod₀ (fun _ _=> by positivity) (fun _ _=> le_max_right _ _)
    _≤ _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))
/-- The unselected prime norm supplies the exact power needed by the relaxed energy. -/
theorem lowUnselectedMass_decay (K : ℕ) (M a : ℝ) (hM : 0≤ M) (ha : 0< a) :
    ∃C : ℝ,0< C ∧ ∀(ell : Fin K→ℝ)(Z : ℝ),0< Z→
    ∀(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
    (∀i n,n∈canonicalSlotSupport (T i)→a*Z^(ell i)≤ elementNorm n)→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
    (∀i x,‖W i x‖≤ M)→
    (∑p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P p‖*
        elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ)))≤ C*Z^(-lowUnselectedLength ell J/2) := by
  obtain ⟨C,hC,hbound⟩ := lowUnselectedMass_bound K M hM
  let c := (min 1 a)^K
  have hc : 0< c := by dsimp [c];positivity
  refine ⟨C*c^(-(1/2:ℝ)),by positivity,?_⟩
  intro ell Z hZ T hT hlower J W P hW
  have hp (p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J) :
      elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ))≤ c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
    have hh := lowUnselectedProduct_norm_lower ell a Z ha hZ _ hlower J p
    have hb := Real.rpow_le_rpow_of_nonpos (show 0< c*Z^(lowUnselectedLength ell J) by positivity) hh (show -(1/2:ℝ)≤0 by norm_num)
    have hid : (c*Z^(lowUnselectedLength ell J))^(-(1/2:ℝ))=c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le]
      congr 2
      ring
    exact hb.trans_eq hid
  calc
    _≤∑p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P p‖*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
        Finset.sum_le_sum (fun p _=> mul_le_mul_of_nonneg_left (hp p) (norm_nonneg _))
    _=(∑p : LowUnselectedTuple (fun i=> canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=> canonicalSlotSupport (T i)) J W P p‖)*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) := (Finset.sum_mul ..).symm
    _≤ C*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
      mul_le_mul_of_nonneg_right (hbound T hT J W P hW) (by positivity)
    _=_ := by ring
end
section
open scoped Classical ContDiff
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
lemma low_compensated_sqrt_factor (q L : ℝ) (hq : 0≤ q) (hL : 0< L) :
    Real.sqrt (3*q/L)=Real.sqrt (3*q)*L^(-(1/2:ℝ)) := by
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg hL.le]
theorem low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Target836.Arithmetic.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0< ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0< X→
      Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(Target836.Arithmetic.x:ℝ)) (Z^(Target836.Arithmetic.y:ℝ)) X t*
          selectedSlotFactor W (fun i=> Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := lowUnselectedMass_decay K 1 a (by norm_num) ha
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0< q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0< C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=> canonicalSlotSupport (T i)
  let Yp := fun i=> Z^(ell i)
  have hz : 0< Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤ max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(Target836.Arithmetic.x:ℝ)) (Z^(Target836.Arithmetic.y:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+((Target836.Arithmetic.y/2))*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2)
  have hGV : G*V≤ Ci*(1+‖t‖)^degree*Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε+lowUnselectedLength ell J/2) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+((Target836.Arithmetic.y/2))*ε:ℝ)*Z^((lowUnselectedLength ell J+507*ε)/2)) := by ring
      _≤ _ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by nlinarith [Target836.Arithmetic.y_lt_half])
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(Target836.Arithmetic.x:ℝ)/L) (Z^(Target836.Arithmetic.y:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(Target836.Arithmetic.x:ℝ)/L) (Z^(Target836.Arithmetic.y:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(Target836.Arithmetic.x:ℝ)/L) (Z^(Target836.Arithmetic.y:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε+lowUnselectedLength ell J/2))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(Target836.Arithmetic.x:ℝ)/L) (Z^(Target836.Arithmetic.y:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤ lowGramFactor (calibrationForSet S hS) (Z^(Target836.Arithmetic.x:ℝ)/L) (Z^(Target836.Arithmetic.y:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤ V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(Target836.Arithmetic.x:ℝ)/L) (Z^(Target836.Arithmetic.y:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(Target836.Arithmetic.x:ℝ)/L) (Z^(Target836.Arithmetic.y:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε+lowUnselectedLength ell J/2)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=> hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hlo : ∀i n,n∈canonicalSlotSupport (T i)→a*Z^(ell i)≤ elementNorm n := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).1
  have hm := hmass ell Z hz T hT hlo J W Yp hW
  calc
    _≤ Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε+lowUnselectedLength ell J/2))*(Cu*Z^(-lowUnselectedLength ell J/2))) := by gcongr
    _=_ := by
      have he : Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε+lowUnselectedLength ell J/2)*Z^(-lowUnselectedLength ell J/2)=Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      dsimp [C0]
      linear_combination (Cg*Ci*Real.sqrt (3*q)*Cu*(1+‖t‖)^degree)*he
end
end SevenEighths.Target836ProbeLow
end
end OAI

#print axioms OAI.SevenEighths.Target836ProbeLow.canonical_slot_inverse_three_halves
#print axioms OAI.SevenEighths.Target836ProbeLow.lowUnselectedWeight_norm_identity
#print axioms OAI.SevenEighths.Target836ProbeLow.lowUnselectedMass_bound
#print axioms OAI.SevenEighths.Target836ProbeLow.lowUnselectedMass_decay
#print axioms OAI.SevenEighths.Target836ProbeLow.low_compensated_sqrt_factor
#print axioms OAI.SevenEighths.Target836ProbeLow.low_central_compensated_tuple
end

/- Original module: Candidate.Target836.Low836.Detector.GaussianFoundation. -/
section
/- Private .874836 LOW probe, adapted from credited accepted source; Apache-2.0. -/

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Detector/LowGaussianDyad, Detector/LowRemoteMass.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle63. -/
namespace OAI
noncomputable section
namespace SevenEighths.Target836ProbeLow
section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
def lowCommonDyad {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) : ℂ :=
  ∫t : ℝ,(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
    compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
      selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t
lemma lowCommonDyad_eq_family {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R : ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) :
    lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV=
    gaussianPhysicalFamilyIntegral η C W0 W1 (Finset.univ : Finset (∀i,slots i))
      (fun p=> compensationSubsetWeight η W Yp (fun i=>(p i).val) J)
      (fun p=> Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
      (fun p=> X/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=> Y/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=> W i.val)
      (fun p i=> elementNorm (p i.val).val/Yp i.val) V hV U R := rfl
lemma lowCommonDyad_norm_of_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slots : Fin K→Finset O) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (J : Finset (Fin K)) (X Y U R B : ℝ) (degree : ℕ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ))
    (hb : ∀t : ℝ,‖∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t‖≤ B*(1+‖t‖)^degree) :
    ‖lowCommonDyad η C W0 W1 slots W Yp J X Y U R V hV‖≤
      B*gaussianJointMoment V hV degree (U/R) := by
  let f := fun t : ℝ=>(∑p : ∀i,slots i,compensationSubsetWeight η W Yp (fun i=>(p i).val) J*
      compensationRowTest η C W0 W1 (fun i=>(p i).val) J X Y U t*
        selectedSlotFactor W Yp (fun i=>(p i).val) J t)*gaussianJointDensity V hV (U/R) t
  have hi := (JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV (U/R)) degree).const_mul B
  have hmajor (t : ℝ) : ‖f t‖≤ B*((1+‖t‖)^degree*‖gaussianJointDensity V hV (U/R) t‖) := by
    dsimp only [f]
    rw [norm_mul]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb t)
      (norm_nonneg (gaussianJointDensity V hV (U/R) t))
  have hh := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hmajor)
  simpa only [f,lowCommonDyad,gaussianJointMoment,integral_const_mul] using hh
theorem low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Target836.Arithmetic.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0< ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0< U→
      Z^(1+lowSelectedLength ell J-ε/2)≤ U→U≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
        W (fun i=> Z^(ell i)) J (Z^(Target836.Arithmetic.x:ℝ)) (Z^(Target836.Arithmetic.y:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^((Target836.Assembly.signal Target836.Arithmetic.theta)+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨degree,C,hC,he⟩ := low_central_compensated_tuple η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t
end
section
open scoped Classical
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
lemma canonicalSlot_count (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (H : ℝ) (hH : 1≤ H) (hnorm : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤ H) :
    ((canonicalSlotSupport T).card:ℝ)≤128*H := by
  have hh := DescentFiberCost.finite_ideal_count_real (lowPrimeIdealList T) H hH
    (fun I hI=>(lowPrimeIdealList_prime T I hI).ne_zero) (lowPrimeIdealList_norm T H hnorm)
  have he := Fintype.card_congr (canonicalSlotEquiv T hT)
  simp only [Fintype.card_coe] at he
  rw [lowPrimeIdealList,Finset.card_image_of_injective _ Subtype.val_injective,he] at hh
  exact hh
lemma canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ Target836.Arithmetic.ell) (b Z : ℝ) (hZ : 1≤ Z)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(Target836.Arithmetic.ell:ℝ) := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod₀ (fun i _=> Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)
lemma slotProduct_norm_ge_one {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    1≤ elementNorm (slotProduct p J) := by
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr (slotProduct_nonzero p hp J)))
lemma compensationSubsetWeight_norm_le_one {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) (Y : Fin K→ℝ)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    ‖compensationSubsetWeight η W Y p J‖≤1 := by
  rw [compensationSubsetWeight,norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) _).trans _
  · rw [compensationSubsetCoefficient,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (slotProduct_norm_pos p hp J).le _),norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos (slotProduct_norm_ge_one p hp J) (by norm_num))).trans (ProbeRow.targetMonoid_norm_le_one η _)
  · rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _=> norm_nonneg _) (fun i _=> hW i _)
lemma compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ Target836.Arithmetic.ell)
    (b Z : ℝ) (hZ : 1≤ Z) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=> Z^(Target836.Arithmetic.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=> Z^(Target836.Arithmetic.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=> W i.val)
      (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(Target836.Arithmetic.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(Target836.Arithmetic.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^((1-Target836.Arithmetic.ell):ℝ) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=> norm_nonneg _) (fun (i : SelectedSlot J) _=> hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=> hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤ elementNorm C.generator*Z^((1-Target836.Arithmetic.ell):ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(Target836.Arithmetic.ell:ℝ)*Z^((1-Target836.Arithmetic.ell):ℝ)) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num
end
end SevenEighths.Target836ProbeLow
end
end OAI

#print axioms OAI.SevenEighths.Target836ProbeLow.lowCommonDyad_eq_family
#print axioms OAI.SevenEighths.Target836ProbeLow.lowCommonDyad_norm_of_bound
#print axioms OAI.SevenEighths.Target836ProbeLow.low_central_gaussian_dyad
#print axioms OAI.SevenEighths.Target836ProbeLow.canonicalSlot_count
#print axioms OAI.SevenEighths.Target836ProbeLow.canonicalTuple_count
#print axioms OAI.SevenEighths.Target836ProbeLow.slotProduct_norm_ge_one
#print axioms OAI.SevenEighths.Target836ProbeLow.compensationSubsetWeight_norm_le_one
#print axioms OAI.SevenEighths.Target836ProbeLow.compensation_scale_mass_bound
end
