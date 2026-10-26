/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Low.Detector.InverseEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Low.Detector.LowNominalGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Low.Detector.LowSlotScales
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Low.Geometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowCentralTuple
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass

set_option autoImplicit false

/-! Adapted from OpenAI/math family003, pinned modules Detector/LowUnselectedMass, Detector/LowCentralTuple.
Apache-2.0 upstream attribution retained. Physical lengths and scalar budgets use Cycle61. -/
namespace OAI
noncomputable section
variable [QRH.LewkoStage1Return.Geometry.Parameters]
namespace SevenEighths.LewkoStage1ProbeLow
section
open scoped Classical
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}
lemma canonical_slot_inverse_three_halves : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))≤C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2:ℝ)) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=>I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-(3/2:ℝ)) := by
    rw [Finset.sum_image (fun P _ Q _ h=>hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=>elementNorm a.val^(-(3/2:ℝ)))
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
    (fun i : J=>elementNorm (a i).val) (fun i _=>by unfold elementNorm;positivity)]
theorem lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤M) :
    ∃C : ℝ,0<C ∧ ∀(T : Fin K→Finset PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤M)→
      (∑a : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P a‖)≤C := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_three_halves
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=>canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-(3/2:ℝ))*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod₀ (fun i _=>Finset.sum_nonneg (fun a _=>mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ))*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ)))*M := (Finset.sum_mul ..).symm
        _≤C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun _ _=>le_max_right _ _)
    _≤_ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))
/-- The unselected prime norm supplies the exact power needed by the relaxed energy. -/
theorem lowUnselectedMass_decay (K : ℕ) (M a : ℝ) (hM : 0≤M) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀(ell : Fin K→ℝ)(Z : ℝ),0<Z→
    ∀(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
    (∀i n,n∈canonicalSlotSupport (T i)→a*Z^(ell i)≤elementNorm n)→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
    (∀i x,‖W i x‖≤M)→
    (∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖*
        elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ)))≤C*Z^(-lowUnselectedLength ell J/2) := by
  obtain ⟨C,hC,hbound⟩ := lowUnselectedMass_bound K M hM
  let c := (min 1 a)^K
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨C*c^(-(1/2:ℝ)),by positivity,?_⟩
  intro ell Z hZ T hT hlower J W P hW
  have hp (p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ))≤c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
    have hh := lowUnselectedProduct_norm_lower ell a Z ha hZ _ hlower J p
    have hb := Real.rpow_le_rpow_of_nonpos (show 0<c*Z^(lowUnselectedLength ell J) by positivity) hh (show -(1/2:ℝ)≤0 by norm_num)
    have hid : (c*Z^(lowUnselectedLength ell J))^(-(1/2:ℝ))=c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le]
      congr 2
      ring
    exact hb.trans_eq hid
  calc
    _≤∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
        Finset.sum_le_sum (fun p _=>mul_le_mul_of_nonneg_left (hp p) (norm_nonneg _))
    _=(∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖)*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) := (Finset.sum_mul ..).symm
    _≤C*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
      mul_le_mul_of_nonneg_right (hbound T hT J W P hW) (by positivity)
    _=_ := by ring
end
section
open scoped Classical ContDiff
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
lemma low_compensated_sqrt_factor (q L : ℝ) (hq : 0≤q) (hL : 0<L) :
    Real.sqrt (3*q/L)=Real.sqrt (3*q)*L^(-(1/2:ℝ)) := by
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg hL.le]
theorem low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤QRH.LewkoStage1Return.Geometry.ell)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0<X→
      Z^(1+lowSelectedLength ell J-ε/2)≤X→X≤Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=>Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)) X t*
          selectedSlotFactor W (fun i=>Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+254*ε) := by
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := low_physical_inverse_normalized η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := lowUnselectedMass_decay K 1 a (by norm_num) ha
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0<q := calibration_elementNorm_pos _
  let C0 := Cg*Ci*Real.sqrt (3*q)*Cu
  have hC0 : 0<C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=>canonicalSlotSupport (T i)
  let Yp := fun i=>Z^(ell i)
  have hz : 0<Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤max 1 b*Z^(ell i) := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+((QRH.LewkoStage1Return.Geometry.y/2))*ε:ℝ)
  let V := Ci*(1+‖t‖)^degree*Z^((lowUnselectedLength ell J+507*ε)/2)
  have hGV : G*V≤Ci*(1+‖t‖)^degree*Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+254*ε+lowUnselectedLength ell J/2) := by
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+((QRH.LewkoStage1Return.Geometry.y/2))*ε:ℝ)*Z^((lowUnselectedLength ell J+507*ε)/2)) := by ring
      _≤_ := by
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by nlinarith [QRH.LewkoStage1Return.Geometry.y_lt_half])
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+254*ε+lowUnselectedLength ell J/2))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(-(1/2:ℝ))) := by
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤lowGramFactor (calibrationForSet S hS) (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(QRH.LewkoStage1Return.Geometry.x:ℝ)/L) (Z^(QRH.LewkoStage1Return.Geometry.y:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+254*ε+lowUnselectedLength ell J/2)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _=_ := by rw [low_compensated_sqrt_factor q L hq.le hL];ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=>hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hlo : ∀i n,n∈canonicalSlotSupport (T i)→a*Z^(ell i)≤elementNorm n := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).1
  have hm := hmass ell Z hz T hT hlo J W Yp hW
  calc
    _≤Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+254*ε+lowUnselectedLength ell J/2))*(Cu*Z^(-lowUnselectedLength ell J/2))) := by gcongr
    _=_ := by
      have he : Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+254*ε+lowUnselectedLength ell J/2)*Z^(-lowUnselectedLength ell J/2)=Z^((QRH.LewkoStage1Return.Geometry.signal QRH.LewkoStage1Return.Geometry.theta)+254*ε) := by
        rw [←Real.rpow_add hz]
        congr 1
        ring
      dsimp [C0]
      linear_combination (Cg*Ci*Real.sqrt (3*q)*Cu*(1+‖t‖)^degree)*he
end
end SevenEighths.LewkoStage1ProbeLow
end
end OAI
