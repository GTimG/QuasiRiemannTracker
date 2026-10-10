import ZetaZeroFree.Analytic.Energy.CompletedSource
import OAI.NumberTheory.DirichletL.Detector.LowSelectedBound
import OAI.NumberTheory.DirichletL.Detector.LowTupleGram
import OAI.NumberTheory.DirichletL.Detector.LowGramScale
import OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass

namespace ZetaZeroFree.Analytic.Energy
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

open ProbePhysical RayFourExpansion
local notation "Id" => Ideal Eis
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

/-- Detector coefficients inherit the new completed energy through the actual
periodic reflection mask, correction characters, and unit reindexing. -/
theorem selected_physical_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
    ∀(Z shift : ℝ),Z₀≤Z→|shift|≤ε→
    ∀(R : Finset Eis),(∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^M)→
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
    ∀(J : Finset (Fin K))(H : SelectedSlot J→ℝ),
      (∀i,1≤H i)→(∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i)→(∏i,H i)≤Z^z→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) (Z^(1+ZetaZeroFree.Analytic.Energy.z+shift)) t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^(M+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := original_completed_energy
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1:Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:ℝ)+1)*6*C
  have hC0 : 0<C0 := by have hh := lowCorrectionEnergy_nonneg;dsimp [C0];positivity
  refine ⟨degree,C0,Z₀,hC0,hZ₀,?_⟩
  intro Z shift hZ hshift R hR T hT hout hdis J H hH1 hH hprod W hW Y t σ
  let L := fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val)⊆T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀P∈lowPeriodPrimeList η S hS (T i.val),Supported P.val :=
    fun P hP=>hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=>Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij=>hdis (fun h=>hij (Subtype.ext h))))
  have hparents : ∀I∈lowIdealRows R,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^M :=
    fun I hI=>⟨lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  have hrow (χ : RayCharacter) (u : Eisˣ) :
      (∑I∈lowIdealRows R,‖lowActualIdealPolynomial L
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ZetaZeroFree.Analytic.Energy.z+shift))‖^2)≤
          C*(1+‖t‖)^degree*Z^(M+507*ε) := by
    convert he Z shift hZ hshift (lowIdealRows R) hparents hcard L H
      hlists (fun i=>lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=>lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=>lowPrimeIdealList_norm _ _ (fun P hP=>hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=>low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z^(1+ZetaZeroFree.Analytic.Energy.z+shift)) t σ R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ∈(Finset.univ:Finset RayCharacter))=>
    Finset.sum_le_sum (fun u (_ : u∈(Finset.univ:Finset Eisˣ))=>hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0≤(Fintype.card RayCharacter:ℝ) := Nat.cast_nonneg _
  have hzpos : 0≤Z^(M+507*ε) := Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0≤(1+|t|)^degree := by positivity
  calc
    _=(lowCorrectionEnergy*(Fintype.card RayCharacter:ℝ)*6*C)*(1+|t|)^degree*
        Z^(M+507*ε) := by ring
    _≤_ := by gcongr <;> linarith


/-- Integrated additive Gram paired with the actual new selected theta energy.
The row cap is imposed on the physical scale before Cauchy. -/
theorem selected_integral_actual_gram
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (K : ℕ) (Ck ε : ℝ)
    (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0<C ∧ 1<Z₀ ∧
    ∀ (Z shift X Y : ℝ) (_hX : 0<X) (_hY : 1≤Y), Z₀≤Z → |shift|≤ε →
      1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y →
      2*bCut*lowPhysicalScale (calibrationForSet S hS) X Y≤Ck*Z^M →
    ∀ (T : Fin K→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) → Pairwise (fun i j=>Disjoint (T i) (T j)) →
    ∀ (J : Finset (Fin K)) (H : SelectedSlot J→ℝ),
      (∀i,1≤H i) → (∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i) →
      (∏i,H i)≤Z^z →
    ∀ (W : Fin K→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ (P : Fin K→ℝ) (t : ℝ),
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) X Y
        (lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
          η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J)
          (Z^(Nstar+shift)) t) v‖ ≤
      C*(1+‖t‖)^degree*lowGramFactor (calibrationForSet S hS) X Y δ*
        Z^((M+507*ε)/2) := by
  obtain ⟨degree,Ce,Z₀,hCe,hZ₀,he⟩ := selected_physical_energy η S hS hbad K Ck ε hCk hε hε1
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  obtain ⟨Cg,hCg,hgram⟩ := lowSeparatedIntegral_actual_gram δ hδ hδ1 a1 b1 B ha1 hab1 hB
    W1 hW1c hW1 hW1s hWB aCut bCut haCut hbCut W0 a0 b0 ha0 hW0 hW0s S hS hbad
  let nr := (Fintype.card RayRing:ℝ)
  refine ⟨degree,Cg*(nr+1)*Real.sqrt Ce,Z₀,by dsimp [nr];positivity,hZ₀,?_⟩
  intro Z shift X Y hX hY hZ hshift hPscale hrow T hT hout hdis J H hH1 hH hprod W hW P t
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hz : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  let Q := lowPhysicalScale (calibrationForSet S hS) X Y
  have hQ : 0<Q := lowPhysicalScale_pos _ X Y hX hy
  let R := lowNumeratorRows aCut bCut haCut hbCut Q hQ
  let row := lowSelectedInverseRow Finset.univ
    (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
    η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) (Z^(Nstar+shift)) t
  have hR : ∀n∈R,n≠0 ∧ elementNorm n≤Ck*Z^M := by
    intro n hn
    exact ⟨lowNumeratorRows_nonzero aCut bCut haCut hbCut Q hQ n hn,
      (lowNumeratorRows_norm_bound aCut bCut haCut hbCut Q hQ n hn).trans hrow⟩
  have hs : 1+z+shift=Nstar+shift := by norm_num [z,Nstar]
  have hE (σ : RayRing) : (∑n∈R,‖row σ n‖^2)≤Ce*(1+‖t‖)^degree*Z^(M+507*ε) := by
    simpa only [hs] using he Z shift hZ hshift R hR T hT hout hdis J H hH1 hH hprod W hW P t σ
  have hp : Real.sqrt (Z^(M+507*ε))=Z^((M+507*ε)/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le]
    congr 1
    ring
  have ht : Real.sqrt ((1+‖t‖)^degree)≤(1+‖t‖)^degree :=
    Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg t))))
  have hEs (σ : RayRing) : Real.sqrt (∑n∈R,‖row σ n‖^2)≤
      Real.sqrt Ce*(1+‖t‖)^degree*Z^((M+507*ε)/2) := by
    apply (Real.sqrt_le_sqrt (hE σ)).trans
    rw [Real.sqrt_mul (mul_nonneg hCe.le (by positivity)),Real.sqrt_mul hCe.le,hp]
    gcongr
  have hg := hgram X Y hX hY row hPscale
  apply hg.trans
  change Cg*lowGramFactor _ X Y δ*(∑σ : RayRing,Real.sqrt (∑n∈R,‖row σ n‖^2))≤_
  calc
    _ ≤ Cg*lowGramFactor _ X Y δ*(∑σ : RayRing,
        Real.sqrt Ce*(1+‖t‖)^degree*Z^((M+507*ε)/2)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun σ _=>hEs σ)) (by unfold lowGramFactor;positivity)
    _ = Cg*nr*Real.sqrt Ce*(1+‖t‖)^degree*lowGramFactor _ X Y δ*Z^((M+507*ε)/2) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,nr]
      ring
    _ ≤ _ := by
      have hn : 0≤nr := Nat.cast_nonneg _
      unfold lowGramFactor
      gcongr
      linarith

lemma physical_scale_new (C : CalibrationData) (Z : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(13/33:ℝ)) (Z^(15/33:ℝ))=elementNorm C.generator*Z^M := by
  unfold lowPhysicalScale
  rw [mul_assoc,←Real.rpow_add hZ]
  norm_num [M]

lemma gram_factor_new (C : CalibrationData) (Z δ : ℝ) (hZ : 1≤Z)
    (hq : elementNorm C.generator≤Z^(2/33:ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) δ≤
      Real.sqrt (3*elementNorm C.generator)*Z^(20/99+(5/22)*δ:ℝ) := by
  let q := elementNorm C.generator
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := calibration_elementNorm_pos C
  have hq1 : 1≤q := calibration_elementNorm_ge_one C
  have hP : q*Z^(13/33:ℝ)≤Z^(15/33:ℝ) := calc
    _ ≤ Z^(2/33:ℝ)*Z^(13/33:ℝ) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by rw [←Real.rpow_add hz];norm_num
  have ht : (1:ℝ)*Z^(15/33:ℝ)≤q^2*(Z^(13/33:ℝ))^2 := by
    have hpow : (Z^(13/33:ℝ))^2=Z^((13/33:ℝ)*2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
      norm_num
    rw [one_mul,hpow]
    apply (Real.rpow_le_rpow_of_exponent_le hZ (show (15/33:ℝ)≤(13/33)*2 by norm_num)).trans
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq1)
  have hg := compensated_gram_scale_bound q (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) 1 δ
    hq0 (by positivity) (by positivity) (by norm_num) hδ hP ht
  simp only [div_one] at hg
  have hr : Z^(15/33:ℝ)/(q*Z^(13/33:ℝ))≤Z^(2/33:ℝ) := by
    have hh := div_le_div_of_nonneg_left (by positivity : 0≤Z^(15/33:ℝ))
      (by positivity : 0<Z^(13/33:ℝ)) (le_mul_of_one_le_left (by positivity) hq1)
    apply hh.trans_eq
    rw [←Real.rpow_sub hz]
    norm_num
  have hpower : Z^(13/33:ℝ)*(Z^(2/33:ℝ))^(1/6:ℝ)*(Z^(15/33:ℝ))^δ=
      Z^(40/99+(5/11)*δ:ℝ) := by
    rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
    congr 1
    ring
  have hb : (q*Z^(13/33:ℝ)*Z^(15/33:ℝ)/Z^(15/33:ℝ))*
      (1+((Z^(15/33:ℝ))^2/(q*Z^(13/33:ℝ)*Z^(15/33:ℝ)))^(1/6:ℝ)+
        ((Z^(15/33:ℝ))^2/(q*Z^(13/33:ℝ)*Z^(15/33:ℝ)))^2/Z^(15/33:ℝ))*(Z^(15/33:ℝ))^δ ≤
      (3*q)*Z^(40/99+(5/11)*δ:ℝ) := by
    apply hg.trans
    calc
      _ ≤ 3*(q*Z^(13/33:ℝ))*(Z^(2/33:ℝ))^(1/6:ℝ)*(Z^(15/33:ℝ))^δ := by gcongr
      _ = (3*q)*(Z^(13/33:ℝ)*(Z^(2/33:ℝ))^(1/6:ℝ)*(Z^(15/33:ℝ))^δ) := by ring
      _ = _ := by rw [hpower]
  apply (Real.sqrt_le_sqrt hb).trans_eq
  have hsqrt : Real.sqrt (Z^(40/99+(5/11)*δ:ℝ))=Z^(20/99+(5/22)*δ:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le]
    congr 1
    ring
  rw [Real.sqrt_mul (by positivity),hsqrt]

lemma gram_factor_new_div (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hLcap : L≤Z^(1/3:ℝ))
    (hq : elementNorm C.generator≤Z^(2/33:ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(20/99+(5/22)*δ:ℝ) := by
  let q := elementNorm C.generator
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := calibration_elementNorm_pos C
  have hq1 : 1≤q := calibration_elementNorm_ge_one C
  have hP : q*Z^(13/33:ℝ)≤Z^(15/33:ℝ) := calc
    _ ≤ Z^(2/33:ℝ)*Z^(13/33:ℝ) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by rw [←Real.rpow_add hz];norm_num
  have ht : L*Z^(15/33:ℝ)≤q^2*(Z^(13/33:ℝ))^2 := by
    have hpow : (Z^(13/33:ℝ))^2=Z^((13/33:ℝ)*2) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
      norm_num
    rw [hpow]
    apply (mul_le_mul_of_nonneg_right hLcap (by positivity)).trans
    rw [←Real.rpow_add hz]
    norm_num
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq1)
  have hg := compensated_gram_scale_bound q (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) L δ
    hq0 (by positivity) (by positivity) hL hδ hP ht
  have hr : Z^(15/33:ℝ)/(q*Z^(13/33:ℝ))≤Z^(2/33:ℝ) := by
    have hh := div_le_div_of_nonneg_left (by positivity : 0≤Z^(15/33:ℝ))
      (by positivity : 0<Z^(13/33:ℝ)) (le_mul_of_one_le_left (by positivity) hq1)
    apply hh.trans_eq
    rw [←Real.rpow_sub hz]
    norm_num
  have hpower : Z^(13/33:ℝ)*(Z^(2/33:ℝ))^(1/6:ℝ)*(Z^(15/33:ℝ))^δ=
      Z^(40/99+(5/11)*δ:ℝ) := by
    rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
    congr 1
    ring
  have hb : (q*(Z^(13/33:ℝ)/L)*(Z^(15/33:ℝ)/L)/(Z^(15/33:ℝ)/L))*
      (1+((Z^(15/33:ℝ)/L)^2/(q*(Z^(13/33:ℝ)/L)*(Z^(15/33:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(15/33:ℝ)/L)^2/(q*(Z^(13/33:ℝ)/L)*(Z^(15/33:ℝ)/L)))^2/(Z^(15/33:ℝ)/L))*(Z^(15/33:ℝ)/L)^δ ≤
      (3*q/L)*Z^(40/99+(5/11)*δ:ℝ) := by
    apply hg.trans
    calc
      _ ≤ 3*(q*Z^(13/33:ℝ)/L)*(Z^(2/33:ℝ))^(1/6:ℝ)*(Z^(15/33:ℝ))^δ := by gcongr
      _ = (3*q/L)*(Z^(13/33:ℝ)*(Z^(2/33:ℝ))^(1/6:ℝ)*(Z^(15/33:ℝ))^δ) := by ring
      _ = _ := by rw [hpower]
  apply (Real.sqrt_le_sqrt hb).trans_eq
  have hsqrt : Real.sqrt (Z^(40/99+(5/11)*δ:ℝ))=Z^(20/99+(5/22)*δ:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hz.le]
    congr 1
    ring
  rw [Real.sqrt_mul (by positivity),hsqrt]

lemma physical_scale_new_div (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L)=
      elementNorm C.generator*Z^M/L^2 := by
  unfold lowPhysicalScale
  have hp : Z^M=Z^(13/33:ℝ)*Z^(15/33:ℝ) := by
    rw [←Real.rpow_add hZ];norm_num [M]
  rw [hp]
  ring

lemma unmarked_row_cap (q Z L a : ℝ) (hq : 0≤q) (hZ : 1≤Z) (ha : 0<a)
    (hL : a*Z^z≤L) :
    q*Z^M/L^2≤(q/a^2)*(Z^(33/38:ℝ))^M := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  have hp : (a*Z^z)^2≤L^2 := pow_le_pow_left₀ (by positivity) hL 2
  calc
    _ ≤ q*Z^M/(a*Z^z)^2 := div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = (q/a^2)*Z^(M-2*z) := by
      have hp2 : (Z^z)^2=Z^(2*z) := by
        rw [←Real.rpow_mul_natCast hz.le];congr 1;ring
      rw [mul_pow,hp2,Real.rpow_sub hz]
      ring
    _ ≤ (q/a^2)*Z^((33/38)*M) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num [M,z])) (by positivity)
    _ = _ := by rw [←Real.rpow_mul hz.le]

lemma new_row_normalization (q Z g loss : ℝ) (hq : 0<q) (hZ : 0<Z) :
    (Real.sqrt (q*Z^M))⁻¹*Real.sqrt (3*q)*Z^g*Z^((M+loss)/2)=
      Real.sqrt 3*Z^(g+loss/2) := by
  have hp : Real.sqrt (Z^M)=Z^(M/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  have he : Z^((M+loss)/2)=Z^(M/2)*Z^(loss/2) := by
    rw [←Real.rpow_add hZ]
    congr 1
    ring
  rw [Real.sqrt_mul hq.le,Real.sqrt_mul (by norm_num : (0:ℝ)≤3),hp,he]
  have hsq : Real.sqrt q≠0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hzp : Z^(M/2)≠0 := ne_of_gt (Real.rpow_pos_of_pos hZ _)
  calc
    _ = Real.sqrt 3*(Z^g*Z^(loss/2)) := by field_simp
    _ = _ := by rw [←Real.rpow_add hZ]

/-- The marked physical slice at the new scales has exponent 20/99. -/
theorem selected_integral_normalized_new
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (K : ℕ) (ε : ℝ) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0<C ∧ 1<Z₀ ∧
    ∀ (Z shift : ℝ), Z₀≤Z → |shift|≤ε →
    ∀ (T : Fin K→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) → Pairwise (fun i j=>Disjoint (T i) (T j)) →
    ∀ (J : Finset (Fin K)) (H : SelectedSlot J→ℝ),
      (∀i,1≤H i) → (∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i) →
      (∏i,H i)≤Z^z →
    ∀ (W : Fin K→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ (P : Fin K→ℝ) (t : ℝ),
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))))⁻¹/(2*Real.pi)*
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))
        (lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
          η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J)
          (Z^(Nstar+shift)) t) v‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+507*ε/2+(5/22)*δ:ℝ) := by
  let Ccal := calibrationForSet S hS
  let q := elementNorm Ccal.generator
  have hq : 0<q := calibration_elementNorm_pos Ccal
  let Ck := 2*bCut*q
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,Ce,Z₁,hCe,hZ₁,he⟩ := selected_integral_actual_gram δ hδ hδ1 W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB aCut bCut haCut hbCut
    η S hS hbad K Ck ε hCk hε hε1
  obtain ⟨Z₂,hZ₂⟩ := Filter.eventually_atTop.mp ((tendsto_rpow_atTop (show 0<(2/33:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop q))
  let Z₀ := max Z₁ (max 1 Z₂)
  refine ⟨degree,Ce*Real.sqrt 3/(2*Real.pi),Z₀,by positivity,
    hZ₁.trans_le (le_max_left _ _),?_⟩
  intro Z shift hZ hshift T hT hout hdis J H hH1 hH hprod W hW P t
  have hz1 : 1≤Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hz1
  have hqcap : q≤Z^(2/33:ℝ) := hZ₂ Z ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hX : 0<Z^(13/33:ℝ) := by positivity
  have hY : 1≤Z^(15/33:ℝ) := Real.one_le_rpow hz1 (by norm_num)
  have hPscale : 1≤(Z^(15/33:ℝ))^2/lowPhysicalScale Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) := by
    have hqZ : 0<q*Z^M := by positivity
    rw [physical_scale_new Ccal Z hz]
    apply (le_div_iff₀ hqZ).mpr
    simp only [one_mul]
    calc
      q*Z^M ≤ Z^(2/33:ℝ)*Z^M := mul_le_mul_of_nonneg_right hqcap (by positivity)
      _ = (Z^(15/33:ℝ))^2 := by
        rw [←Real.rpow_add hz,←Real.rpow_natCast,←Real.rpow_mul hz.le]
        norm_num [M]
  have hrow : 2*bCut*lowPhysicalScale Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ))≤Ck*Z^M := by
    rw [physical_scale_new Ccal Z hz]
    dsimp [Ck,q]
    ring_nf
    exact le_refl _
  have hi := he Z shift (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) hX hY
    ((le_max_left _ _).trans hZ) hshift hPscale hrow T hT hout hdis J H hH1 hH hprod W hW P t
  have hg := gram_factor_new Ccal Z δ hz1 hqcap hδ.le
  have hQ : 0<lowPhysicalScale Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) :=
    lowPhysicalScale_pos _ _ _ hX (lt_of_lt_of_le zero_lt_one hY)
  apply (mul_le_mul_of_nonneg_left hi (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) (by positivity))
    (by positivity)).trans_eq
  rw [physical_scale_new Ccal Z hz]
  change (Real.sqrt (q*Z^M))⁻¹/(2*Real.pi)*
    (Ce*(1+‖t‖)^degree*(Real.sqrt (3*q)*Z^(20/99+(5/22)*δ:ℝ))*Z^((M+507*ε)/2))=_
  calc
    _ = (Ce/(2*Real.pi))*(1+‖t‖)^degree*
        ((Real.sqrt (q*Z^M))⁻¹*Real.sqrt (3*q)*Z^(20/99+(5/22)*δ:ℝ)*Z^((M+507*ε)/2)) := by ring
    _ = _ := by rw [new_row_normalization q Z _ (507*ε) hq hz];ring

/-- An arbitrary positive loss in the normalized marked physical slice. -/
theorem selected_integral_normalized_epsilon
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (K : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0<C ∧ 1<Z₀ ∧
    ∀ (Z shift : ℝ), Z₀≤Z → |shift|≤min (1/2) (ε/1000) →
    ∀ (T : Fin K→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) → Pairwise (fun i j=>Disjoint (T i) (T j)) →
    ∀ (J : Finset (Fin K)) (H : SelectedSlot J→ℝ),
      (∀i,1≤H i) → (∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i) →
      (∏i,H i)≤Z^z →
    ∀ (W : Fin K→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ (P : Fin K→ℝ) (t : ℝ),
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))))⁻¹/(2*Real.pi)*
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))
        (lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
          η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J)
          (Z^(Nstar+shift)) t) v‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+ε:ℝ) := by
  let τ := min (1/2) (ε/1000)
  have hτ : 0<τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hloss : 507*τ/2+(5/22)*τ≤ε := by
    have hh : τ≤ε/1000 := min_le_right _ _
    linarith
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := selected_integral_normalized_new τ hτ hτ1 W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB aCut bCut haCut hbCut
    η S hS hbad K τ hτ hτ1.le
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z shift hZ hshift T hT hout hdis J H hH1 hH hprod W hW P t
  apply (he Z shift hZ hshift T hT hout hdis J H hH1 hH hprod W hW P t).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_lt_of_le hZ₀ hZ)) (by linarith)

/-- A fixed dilation of the base only changes the completion width by a
logarithmic error; this accommodates fixed annular prime-cap constants. -/
lemma dilation_width_shift (D Z : ℝ) (hD : 0<D) (hZ : 1<Z) (hDZ : 1<D*Z) :
    Real.logb (D*Z) (Z^Nstar)-Nstar =
      -Nstar*(Real.log D/Real.log (D*Z)) := by
  have hz : 0<Z := lt_trans zero_lt_one hZ
  have hlog : Real.log (D*Z)≠0 := ne_of_gt (Real.log_pos hDZ)
  rw [Real.logb,Real.log_rpow hz,Real.log_mul (ne_of_gt hD) (ne_of_gt hz)]
  rw [Real.log_mul (ne_of_gt hD) (ne_of_gt hz)] at hlog
  field_simp [hlog]
  <;> ring

lemma eventually_dilation_completion (D τ : ℝ) (hD : 1≤D) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
      let shift := Real.logb (D*Z) (Z^Nstar)-Nstar
      |shift|≤τ ∧ (D*Z)^(Nstar+shift)=Z^Nstar := by
  have hD0 : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hn : 0<Nstar := by norm_num [Nstar]
  obtain ⟨Z₀,hZ₀,hlog⟩ := InverseTerminalWidths.constant_log_error D (τ/Nstar) hD0 (by positivity)
  filter_upwards [Filter.eventually_ge_atTop (max 2 Z₀)] with Z hZ
  have hz1 : 1<Z := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) ((le_max_left _ _).trans hZ)
  have hz : 0<Z := lt_trans zero_lt_one hz1
  have hDZ : 1<D*Z := hz1.trans_le (le_mul_of_one_le_left hz.le hD)
  have hwidth : 0≤Real.log D/Real.log (D*Z) := div_nonneg (Real.log_nonneg hD) (Real.log_pos hDZ).le
  have hw : Real.log D/Real.log (D*Z)≤τ/Nstar := hlog (D*Z)
    (((le_max_right _ _).trans hZ).trans (le_mul_of_one_le_left hz.le hD))
  refine ⟨hz1,?_,?_⟩
  · rw [dilation_width_shift D Z hD0 hz1 hDZ]
    rw [abs_mul,abs_neg,abs_of_pos hn,abs_of_nonneg hwidth]
    simpa only [mul_comm] using (le_div_iff₀ hn).mp hw
  · rw [show Nstar+(Real.logb (D*Z) (Z^Nstar)-Nstar)=Real.logb (D*Z) (Z^Nstar) by ring]
    exact Real.rpow_logb (mul_pos hD0 hz) (ne_of_gt hDZ) (Real.rpow_pos_of_pos hz _)

lemma prime_cap_dilation (b : ℝ) :
    ∃D : ℝ, 1≤D ∧ b≤D^z := by
  let D := (max 1 b)^(1/z)
  have hz : 0<z := by norm_num [z]
  have hd : 1≤D := Real.one_le_rpow (le_max_left _ _) (by positivity)
  refine ⟨D,hd,?_⟩
  dsimp [D]
  rw [←Real.rpow_mul (by positivity : 0≤max 1 b)]
  rw [show (1/z)*z=1 by field_simp,Real.rpow_one]
  exact le_max_right _ _

lemma eventually_dilation_completion_uniform (D τ : ℝ) (hD : 1≤D) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
      ∀ σ : ℝ, |σ|≤τ/2 →
      let shift := Real.logb (D*Z) (Z^(Nstar+σ))-Nstar
      |shift|≤τ ∧ (D*Z)^(Nstar+shift)=Z^(Nstar+σ) := by
  filter_upwards [eventually_dilation_completion D (τ/2) hD (by positivity)] with Z hcomp
  have hz : 0<Z := lt_trans zero_lt_one hcomp.1
  have hd : 0<D := lt_of_lt_of_le zero_lt_one hD
  have hdz : 1<D*Z := hcomp.1.trans_le (le_mul_of_one_le_left hz.le hD)
  have hlog : 0<Real.log (D*Z) := Real.log_pos hdz
  have hr0 : 0≤Real.log Z/Real.log (D*Z) := div_nonneg (Real.log_pos hcomp.1).le hlog.le
  have hr1 : Real.log Z/Real.log (D*Z)≤1 := by
    apply (div_le_one hlog).mpr
    exact Real.log_le_log hz (le_mul_of_one_le_left hz.le hD)
  refine ⟨hcomp.1,?_⟩
  intro σ hσ
  have he : Real.logb (D*Z) (Z^(Nstar+σ))-Nstar =
      (Real.logb (D*Z) (Z^Nstar)-Nstar)+σ*(Real.log Z/Real.log (D*Z)) := by
    rw [Real.logb,Real.logb,Real.log_rpow hz,Real.log_rpow hz]
    ring
  refine ⟨?_,?_⟩
  · rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg hr0]
    have hs : |σ| *(Real.log Z/Real.log (D*Z))≤τ/2 :=
      (mul_le_mul_of_nonneg_left hr1 (abs_nonneg σ)).trans (by simpa using hσ)
    linarith [hcomp.2.1]
  · rw [show Nstar+(Real.logb (D*Z) (Z^(Nstar+σ))-Nstar)=
        Real.logb (D*Z) (Z^(Nstar+σ)) by ring]
    exact Real.rpow_logb (mul_pos hd hz) (ne_of_gt hdz) (Real.rpow_pos_of_pos hz _)

/-- Fixed prime-annulus constants are absorbed by a proved base dilation. -/
theorem selected_integral_annular_epsilon
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (K : ℕ) (bcap ε : ℝ) (hε : 0<ε) :
    ∃ degree : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
    ∀ (T : Fin K→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) → Pairwise (fun i j=>Disjoint (T i) (T j)) →
    ∀ (J : Finset (Fin K)) (H : SelectedSlot J→ℝ),
      (∀i,1≤H i) → (∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i) →
      (∏i,H i)≤bcap*Z^z →
    ∀ (W : Fin K→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ (P : Fin K→ℝ) (t : ℝ),
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))))⁻¹/(2*Real.pi)*
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))
        (lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
          η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J)
          (Z^Nstar) t) v‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+ε:ℝ) := by
  let τ := min (1/2) (ε/1000)
  have hτ : 0<τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hloss : 507*τ/2+(5/22)*τ≤ε := by
    have hh : τ≤ε/1000 := min_le_right _ _
    linarith
  obtain ⟨D,hD,hb⟩ := prime_cap_dilation bcap
  have hd : 0<D := lt_of_lt_of_le zero_lt_one hD
  let Ccal := calibrationForSet S hS
  let q := elementNorm Ccal.generator
  have hq : 0<q := calibration_elementNorm_pos Ccal
  let Ck := 2*bCut*q
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,Ce,Z₁,hCe,hZ₁,he⟩ := selected_integral_actual_gram τ hτ hτ1 W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB aCut bCut haCut hbCut
    η S hS hbad K Ck τ hCk hτ hτ1.le
  let CD := Ce*D^((M+507*τ)/2)
  have hCD : 0<CD := by dsimp [CD];positivity
  refine ⟨degree,CD*Real.sqrt 3/(2*Real.pi),by positivity,?_⟩
  have hqc := (tendsto_rpow_atTop (show 0<(2/33:ℝ) by norm_num)).eventually (Filter.eventually_ge_atTop q)
  filter_upwards [eventually_dilation_completion D τ hD hτ,Filter.eventually_ge_atTop Z₁,hqc] with Z hcomp hZ hqcap
  refine ⟨hcomp.1,?_⟩
  intro T hT hout hdis J H hH1 hH hprod W hW P t
  have hz : 0<Z := lt_trans zero_lt_one hcomp.1
  have hZbase : Z₁≤D*Z := hZ.trans (le_mul_of_one_le_left hz.le hD)
  let shift := Real.logb (D*Z) (Z^Nstar)-Nstar
  have hshift : |shift|≤τ := hcomp.2.1
  have hscale : (D*Z)^(Nstar+shift)=Z^Nstar := hcomp.2.2
  have hprodD : (∏i,H i)≤(D*Z)^z := calc
    _ ≤ bcap*Z^z := hprod
    _ ≤ D^z*Z^z := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := (Real.mul_rpow hd.le hz.le).symm
  have hX : 0<Z^(13/33:ℝ) := by positivity
  have hY : 1≤Z^(15/33:ℝ) := Real.one_le_rpow hcomp.1.le (by norm_num)
  have hPscale : 1≤(Z^(15/33:ℝ))^2/lowPhysicalScale Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) := by
    rw [physical_scale_new Ccal Z hz]
    apply (le_div_iff₀ (by positivity : 0<q*Z^M)).mpr
    simp only [one_mul]
    calc
      q*Z^M ≤ Z^(2/33:ℝ)*Z^M := mul_le_mul_of_nonneg_right hqcap (by positivity)
      _ = (Z^(15/33:ℝ))^2 := by
        rw [←Real.rpow_add hz,←Real.rpow_natCast,←Real.rpow_mul hz.le]
        norm_num [M]
  have hrow : 2*bCut*lowPhysicalScale Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ))≤Ck*(D*Z)^M := by
    rw [physical_scale_new Ccal Z hz]
    calc
      _ = Ck*Z^M := by dsimp [Ck,q];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.le
        (le_mul_of_one_le_left hz.le hD) (by norm_num [M])) hCk.le
  have hi := he (D*Z) shift (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) hX hY hZbase hshift
    hPscale hrow T hT hout hdis J H hH1 hH hprodD W hW P t
  rw [hscale,Real.mul_rpow hd.le hz.le] at hi
  have hi' := hi
  rw [show Ce*(1+‖t‖)^degree*lowGramFactor Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) τ*
      (D^((M+507*τ)/2)*Z^((M+507*τ)/2))=
      CD*(1+‖t‖)^degree*lowGramFactor Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) τ*Z^((M+507*τ)/2) by dsimp [CD];ring] at hi'
  have hg := gram_factor_new Ccal Z τ hcomp.1.le hqcap hτ.le
  apply (mul_le_mul_of_nonneg_left hi' (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) (by positivity))
    (by positivity)).trans
  rw [physical_scale_new Ccal Z hz]
  change (Real.sqrt (q*Z^M))⁻¹/(2*Real.pi)*
    (CD*(1+‖t‖)^degree*(Real.sqrt (3*q)*Z^(20/99+(5/22)*τ:ℝ))*Z^((M+507*τ)/2))≤_
  calc
    _ = (CD/(2*Real.pi))*(1+‖t‖)^degree*
        ((Real.sqrt (q*Z^M))⁻¹*Real.sqrt (3*q)*Z^(20/99+(5/22)*τ:ℝ)*Z^((M+507*τ)/2)) := by ring
    _ = (CD*Real.sqrt 3/(2*Real.pi))*(1+‖t‖)^degree*Z^((20/99+(5/22)*τ)+507*τ/2) := by
      rw [new_row_normalization q Z _ (507*τ) hq hz];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hcomp.1.le (by linarith)) (by positivity)

/-- Uniform completion-width version for central Gaussian dyads. -/
theorem selected_integral_annular_shift_epsilon
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (K : ℕ) (bcap ε : ℝ) (hε : 0<ε) :
    ∃ degree : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
    ∀ (σ : ℝ), |σ|≤min (1/2) (ε/1000)/2 →
    ∀ (T : Fin K→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) → Pairwise (fun i j=>Disjoint (T i) (T j)) →
    ∀ (J : Finset (Fin K)) (H : SelectedSlot J→ℝ),
      (∀i,1≤H i) → (∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i) →
      (∏i,H i)≤bcap*Z^z →
    ∀ (W : Fin K→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ (P : Fin K→ℝ) (t : ℝ),
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))))⁻¹/(2*Real.pi)*
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) (Z^(13/33:ℝ)) (Z^(15/33:ℝ))
        (lowSelectedInverseRow Finset.univ
          (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W P t)
          η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J)
          (Z^(Nstar+σ)) t) v‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+ε:ℝ) := by
  let τ := min (1/2) (ε/1000)
  have hτ : 0<τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hloss : 507*τ/2+(5/22)*τ≤ε := by
    have hh : τ≤ε/1000 := min_le_right _ _
    linarith
  obtain ⟨D,hD,hb⟩ := prime_cap_dilation bcap
  have hd : 0<D := lt_of_lt_of_le zero_lt_one hD
  let Ccal := calibrationForSet S hS
  let q := elementNorm Ccal.generator
  have hq : 0<q := calibration_elementNorm_pos Ccal
  let Ck := 2*bCut*q
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,Ce,Z₁,hCe,hZ₁,he⟩ := selected_integral_actual_gram τ hτ hτ1 W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB aCut bCut haCut hbCut
    η S hS hbad K Ck τ hCk hτ hτ1.le
  let CD := Ce*D^((M+507*τ)/2)
  have hCD : 0<CD := by dsimp [CD];positivity
  refine ⟨degree,CD*Real.sqrt 3/(2*Real.pi),by positivity,?_⟩
  have hqc := (tendsto_rpow_atTop (show 0<(2/33:ℝ) by norm_num)).eventually (Filter.eventually_ge_atTop q)
  filter_upwards [eventually_dilation_completion_uniform D τ hD hτ,Filter.eventually_ge_atTop Z₁,hqc] with Z hcomp hZ hqcap
  refine ⟨hcomp.1,?_⟩
  intro σ hσ T hT hout hdis J H hH1 hH hprod W hW P t
  have hz : 0<Z := lt_trans zero_lt_one hcomp.1
  have hZbase : Z₁≤D*Z := hZ.trans (le_mul_of_one_le_left hz.le hD)
  let shift := Real.logb (D*Z) (Z^(Nstar+σ))-Nstar
  have hshift : |shift|≤τ := (hcomp.2 σ hσ).1
  have hscale : (D*Z)^(Nstar+shift)=Z^(Nstar+σ) := (hcomp.2 σ hσ).2
  have hprodD : (∏i,H i)≤(D*Z)^z := calc
    _ ≤ bcap*Z^z := hprod
    _ ≤ D^z*Z^z := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := (Real.mul_rpow hd.le hz.le).symm
  have hX : 0<Z^(13/33:ℝ) := by positivity
  have hY : 1≤Z^(15/33:ℝ) := Real.one_le_rpow hcomp.1.le (by norm_num)
  have hPscale : 1≤(Z^(15/33:ℝ))^2/lowPhysicalScale Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) := by
    rw [physical_scale_new Ccal Z hz]
    apply (le_div_iff₀ (by positivity : 0<q*Z^M)).mpr
    simp only [one_mul]
    calc
      q*Z^M ≤ Z^(2/33:ℝ)*Z^M := mul_le_mul_of_nonneg_right hqcap (by positivity)
      _ = (Z^(15/33:ℝ))^2 := by
        rw [←Real.rpow_add hz,←Real.rpow_natCast,←Real.rpow_mul hz.le]
        norm_num [M]
  have hrow : 2*bCut*lowPhysicalScale Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ))≤Ck*(D*Z)^M := by
    rw [physical_scale_new Ccal Z hz]
    calc
      _ = Ck*Z^M := by dsimp [Ck,q];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hz.le
        (le_mul_of_one_le_left hz.le hD) (by norm_num [M])) hCk.le
  have hi := he (D*Z) shift (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) hX hY hZbase hshift
    hPscale hrow T hT hout hdis J H hH1 hH hprodD W hW P t
  rw [hscale,Real.mul_rpow hd.le hz.le] at hi
  have hi' := hi
  rw [show Ce*(1+‖t‖)^degree*lowGramFactor Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) τ*
      (D^((M+507*τ)/2)*Z^((M+507*τ)/2))=
      CD*(1+‖t‖)^degree*lowGramFactor Ccal (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) τ*Z^((M+507*τ)/2) by dsimp [CD];ring] at hi'
  have hg := gram_factor_new Ccal Z τ hcomp.1.le hqcap hτ.le
  apply (mul_le_mul_of_nonneg_left hi' (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) (by positivity))
    (by positivity)).trans
  rw [physical_scale_new Ccal Z hz]
  change (Real.sqrt (q*Z^M))⁻¹/(2*Real.pi)*
    (CD*(1+‖t‖)^degree*(Real.sqrt (3*q)*Z^(20/99+(5/22)*τ:ℝ))*Z^((M+507*τ)/2))≤_
  calc
    _ = (CD/(2*Real.pi))*(1+‖t‖)^degree*
        ((Real.sqrt (q*Z^M))⁻¹*Real.sqrt (3*q)*Z^(20/99+(5/22)*τ:ℝ)*Z^((M+507*τ)/2)) := by ring
    _ = (CD*Real.sqrt 3/(2*Real.pi))*(1+‖t‖)^degree*Z^((20/99+(5/22)*τ)+507*τ/2) := by
      rw [new_row_normalization q Z _ (507*τ) hq hz];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hcomp.1.le (by linarith)) (by positivity)

/-- The actual marked compensation subset, with its scalar normalization. -/
theorem selected_compensated_marked_slice
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (K : ℕ) (bcap ε : ℝ) (hε : 0<ε) :
    ∃ degree : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
    ∀ (T : Fin K→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) → Pairwise (fun i j=>Disjoint (T i) (T j)) →
    ∀ (H : SelectedSlot (∅ : Finset (Fin K))→ℝ),
      (∀i,1≤H i) → (∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i) →
      (∏i,H i)≤bcap*Z^z →
    ∀ (W : Fin K→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ (P : Fin K→ℝ) (t : ℝ),
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W P (fun i=>(p i).val) ∅*
        compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) ∅
          (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) (Z^Nstar) t*
        selectedSlotFactor W P (fun i=>(p i).val) ∅ t‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+ε:ℝ) := by
  obtain ⟨degree,C,hC,he⟩ := selected_integral_annular_epsilon W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB
    (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) η S hS hbad K bcap ε hε
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis H hH1 hH hprod W hW P t
  let slots := fun i=>canonicalSlotSupport (T i)
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hs := compensation_tuple_low_polynomial η S hS hbad W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s slots hslots ∅ W P
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) (Z^Nstar) t (by positivity) (by positivity) (by positivity)
  simp [lowUnselectedWeight] at hs
  rw [hs,norm_mul]
  convert hZ.2 T hT hout hdis ∅ H hH1 hH hprod W hW P t using 1
  congr 1
  convert low_mellin_normalizer_norm
    (lowPhysicalScale (calibrationForSet S hS) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)))
    (lowPhysicalScale_pos _ _ _ (by positivity) (by positivity)) using 1
  congr 1
  simp [div_eq_mul_inv,mul_inv_rev]

/-- Marked compensated slice uniformly over the central Gaussian width. -/
theorem selected_compensated_marked_slice_shift
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (K : ℕ) (bcap ε : ℝ) (hε : 0<ε) :
    ∃ degree : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
    ∀ (σ : ℝ), |σ|≤min (1/2) (ε/1000)/2 →
    ∀ (T : Fin K→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) → Pairwise (fun i j=>Disjoint (T i) (T j)) →
    ∀ (H : SelectedSlot (∅ : Finset (Fin K))→ℝ),
      (∀i,1≤H i) → (∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i) →
      (∏i,H i)≤bcap*Z^z →
    ∀ (W : Fin K→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ (P : Fin K→ℝ) (t : ℝ),
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W P (fun i=>(p i).val) ∅*
        compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) ∅
          (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) (Z^(Nstar+σ)) t*
        selectedSlotFactor W P (fun i=>(p i).val) ∅ t‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+ε:ℝ) := by
  obtain ⟨degree,C,hC,he⟩ := selected_integral_annular_shift_epsilon W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB
    (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) η S hS hbad K bcap ε hε
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro σ hσ T hT hout hdis H hH1 hH hprod W hW P t
  let slots := fun i=>canonicalSlotSupport (T i)
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hs := compensation_tuple_low_polynomial η S hS hbad W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s slots hslots ∅ W P
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) (Z^(Nstar+σ)) t (by positivity) (by positivity) (by positivity)
  simp [lowUnselectedWeight] at hs
  rw [hs,norm_mul]
  convert hZ.2 σ hσ T hT hout hdis ∅ H hH1 hH hprod W hW P t using 1
  congr 1
  convert low_mellin_normalizer_norm
    (lowPhysicalScale (calibrationForSet S hS) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)))
    (lowPhysicalScale_pos _ _ _ (by positivity) (by positivity)) using 1
  congr 1
  simp [div_eq_mul_inv,mul_inv_rev]

lemma selected_zero_tuple_card :
    (Finset.univ : Finset (LowSelectedTuple
      (fun _ : Fin 0=>canonicalSlotSupport (∅ : Finset PrimeIdeal)) ∅)).card=1 := by
  rw [Finset.card_univ]
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨fun i=>Fin.elim0 i.val,?_⟩
  intro f
  funext i
  exact Fin.elim0 i.val

lemma selected_inverse_empty (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (U t : ℝ) :
    lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i : Fin 0=>Finset.empty) ∅
        (fun _=>fun _=>(1:ℂ)) (fun _=>(1:ℝ)) t)
      η S hS (lowSelectedIdeal (fun i : Fin 0=>Finset.empty) ∅) U t=
      lowMarkedInverseRow η S hS 1 U t := by
  funext σ m
  simp [lowSelectedInverseRow,lowSelectedWeight,lowSelectedIdeal,SelectedSlot,Fintype.prod_empty]

/-- The unmarked subtraction uses base Z^(33/38), so its completion scale is Z. -/
theorem unmarked_integral_rescaled_source
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (Ck ε : ℝ)
    (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0<C ∧ 1<Z₀ ∧
    ∀ (Z X Y : ℝ) (hX : 0<X) (hY : 1≤Y), 1≤Z → Z₀≤Z^(33/38:ℝ) →
      1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y →
      2*bCut*lowPhysicalScale (calibrationForSet S hS) X Y≤Ck*(Z^(33/38:ℝ))^M →
    ∀ t : ℝ,
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) X Y
        (lowMarkedInverseRow η S hS 1 Z t) v‖ ≤
      C*(1+‖t‖)^degree*lowGramFactor (calibrationForSet S hS) X Y δ*
        Z^((33/38)*((M+507*ε)/2):ℝ) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := selected_integral_actual_gram δ hδ hδ1 W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB aCut bCut haCut hbCut
    η S hS hbad 0 Ck ε hCk hε hε1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z X Y hX hY hZ1 hZ hPscale hrow t
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ1
  have hb : 1≤Z^(33/38:ℝ) := Real.one_le_rpow hZ1 (by norm_num)
  have hc : (Z^(33/38:ℝ))^Nstar=Z := by
    rw [←Real.rpow_mul hz.le]
    norm_num [Nstar]
  have hh := he (Z^(33/38:ℝ)) 0 X Y hX hY hZ (by simpa using hε.le) hPscale hrow
    (fun _ : Fin 0=>(∅ : Finset PrimeIdeal)) (by simp) (by simp) (by simp [Pairwise])
    ∅ (fun _=>1) (by simp) (by simp) (by simpa using Real.one_le_rpow hb (show 0≤z by norm_num [z]))
    (fun _=>fun _=>(1:ℂ)) (by simp) (fun _=>(1:ℝ)) t
  simp only [add_zero,hc] at hh
  rw [←Real.rpow_mul hz.le] at hh
  convert hh using 1
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  congr 1
  funext σ m
  letI : IsEmpty (SelectedSlot (∅ : Finset (Fin 0))) := ⟨fun i=>Fin.elim0 i.val⟩
  simp [lowSelectedInverseRow,lowSelectedWeight,lowSelectedIdeal,selected_zero_tuple_card]

/-- The unmarked central shift scales by 38/33 at the smaller source base. -/
theorem unmarked_integral_rescaled_shift_source
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (Ck ε : ℝ)
    (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0<C ∧ 1<Z₀ ∧
    ∀ (Z σ X Y : ℝ) (hX : 0<X) (hY : 1≤Y), 1≤Z → |σ|≤(33/38)*ε → Z₀≤Z^(33/38:ℝ) →
      1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y →
      2*bCut*lowPhysicalScale (calibrationForSet S hS) X Y≤Ck*(Z^(33/38:ℝ))^M →
    ∀ t : ℝ,
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) X Y
        (lowMarkedInverseRow η S hS 1 (Z^(1+σ)) t) v‖ ≤
      C*(1+‖t‖)^degree*lowGramFactor (calibrationForSet S hS) X Y δ*
        Z^((33/38)*((M+507*ε)/2):ℝ) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := selected_integral_actual_gram δ hδ hδ1 W0 W1
    a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB aCut bCut haCut hbCut
    η S hS hbad 0 Ck ε hCk hε hε1
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z σ X Y hX hY hZ1 hσ hZ hPscale hrow t
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ1
  have hb : 1≤Z^(33/38:ℝ) := Real.one_le_rpow hZ1 (by norm_num)
  have hc : (Z^(33/38:ℝ))^(Nstar+(38/33)*σ)=Z^(1+σ) := by
    rw [←Real.rpow_mul hz.le]
    congr 1
    norm_num [Nstar]
    ring
  have hσb : |(38/33:ℝ)*σ|≤ε := by
    rw [abs_mul,abs_of_pos (by norm_num : 0<(38/33:ℝ))]
    linarith
  have hh := he (Z^(33/38:ℝ)) ((38/33)*σ) X Y hX hY hZ hσb hPscale hrow
    (fun _ : Fin 0=>(∅ : Finset PrimeIdeal)) (by simp) (by simp) (by simp [Pairwise])
    ∅ (fun _=>1) (by simp) (by simp) (by simpa using Real.one_le_rpow hb (show 0≤z by norm_num [z]))
    (fun _=>fun _=>(1:ℂ)) (by simp) (fun _=>(1:ℝ)) t
  simp only [hc] at hh
  rw [←Real.rpow_mul hz.le] at hh
  convert hh using 1
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with v
  congr 1
  funext σ m
  letI : IsEmpty (SelectedSlot (∅ : Finset (Fin 0))) := ⟨fun i=>Fin.elim0 i.val⟩
  simp [lowSelectedInverseRow,lowSelectedWeight,lowSelectedIdeal,selected_zero_tuple_card]

lemma unmarked_normalization (q Z L g e : ℝ) (hq : 0<q) (hZ : 0<Z) (hL : 0<L) :
    L^(-(3/2:ℝ))*(Real.sqrt (q*Z^M/L^2))⁻¹*
      Real.sqrt (3*q/L)*Z^g*Z^e =
      Real.sqrt 3/L*Z^(g+e-M/2) := by
  have hsq : Real.sqrt (q*Z^M/L^2)=Real.sqrt (q*Z^M)/L := by
    rw [Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hL]
  have hsq3 : Real.sqrt (3*q/L)=Real.sqrt (3*q)/Real.sqrt L :=
    Real.sqrt_div (by positivity) _
  have hfactor : L^(-(3/2:ℝ))*L/(Real.sqrt L)=L⁻¹ := by
    calc
      _ = L^(-(3/2:ℝ))*L^(1:ℝ)/L^(1/2:ℝ) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
      _ = _ := by rw [←Real.rpow_add hL,←Real.rpow_sub hL];norm_num;exact Real.rpow_neg_one L
  rw [hsq,hsq3,inv_div]
  calc
    _ = (L^(-(3/2:ℝ))*L/(Real.sqrt L))*
        ((Real.sqrt (q*Z^M))⁻¹*Real.sqrt (3*q)*Z^g*Z^e) := by ring
    _ = L⁻¹*((Real.sqrt (q*Z^M))⁻¹*Real.sqrt (3*q)*Z^g*Z^((M+(2*e-M))/2)) := by
      rw [hfactor];congr 2;congr 1;ring
    _ = _ := by
      rw [new_row_normalization q Z g (2*e-M) hq hZ]
      rw [show g+(2*e-M)/2=g+e-M/2 by ring]
      ring

lemma unmarked_saving (ε δ : ℝ) :
    (20/99+(5/22)*δ)+(33/38)*((M+507*ε)/2)-M/2 =
      20/99-35/627+(33/38)*(507*ε/2)+(5/22)*δ := by
  norm_num [M]
  ring


/-- Actual unmarked physical row bound, including its compensating prime weight. -/
theorem unmarked_integral_normalized_new
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB : ∀x,‖W1 x‖≤B)
    (aCut bCut : ℝ) (haCut : 0<aCut) (hbCut : 0<bCut)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (a ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1) :
    ∃ degree : ℕ, ∃ C Z₀ : ℝ, 0<C ∧ 1<Z₀ ∧
    ∀ (Z σ L : ℝ), 1≤Z → Z₀≤Z^(33/38:ℝ) → |σ|≤(33/38)*ε →
      1≤L → a*Z^z≤L → L≤Z^(1/3:ℝ) →
      elementNorm (calibrationForSet S hS).generator≤Z^(2/33:ℝ) →
      1≤Z^(15/33:ℝ)/L →
      1≤(Z^(15/33:ℝ)/L)^2/
        lowPhysicalScale (calibrationForSet S hS) (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L) →
    ∀ t : ℝ,
      L^(-(3/2:ℝ))*(Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L)))⁻¹/(2*Real.pi)*
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff aCut bCut) (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L)
        (lowMarkedInverseRow η S hS 1 (Z^(1+σ)) t) v‖ ≤
      C*(1+‖t‖)^degree/L*
        Z^(20/99-35/627+(33/38)*(507*ε/2)+(5/22)*δ:ℝ) := by
  let Ccal := calibrationForSet S hS
  let q := elementNorm Ccal.generator
  have hq : 0<q := calibration_elementNorm_pos Ccal
  let Ck := 2*bCut*(q/a^2)
  have hCk : 0<Ck := by dsimp [Ck];positivity
  obtain ⟨degree,Ce,Z₀,hCe,hZ₀,he⟩ := unmarked_integral_rescaled_shift_source δ hδ hδ1
    W0 W1 a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB
    aCut bCut haCut hbCut η S hS hbad Ck ε hCk hε hε1
  refine ⟨degree,Ce*Real.sqrt 3/(2*Real.pi),Z₀,by positivity,hZ₀,?_⟩
  intro Z σ L hZ1 hZ hσ hL hLa hLcap hqcap hY hPscale t
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ1
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hrow : 2*bCut*lowPhysicalScale Ccal (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L)
      ≤Ck*(Z^(33/38:ℝ))^M := by
    rw [physical_scale_new_div Ccal Z L hz]
    calc
      _ ≤ 2*bCut*((q/a^2)*(Z^(33/38:ℝ))^M) :=
        mul_le_mul_of_nonneg_left (unmarked_row_cap q Z L a hq.le hZ1 ha hLa) (by positivity)
      _ = _ := by dsimp [Ck];ring
  have hi := he Z σ (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L) (by positivity) hY
    hZ1 hσ hZ hPscale hrow t
  have hg := gram_factor_new_div Ccal Z L δ hZ1 hL hLcap hqcap hδ.le
  apply (mul_le_mul_of_nonneg_left hi (by positivity)).trans
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) (by positivity))
    (by positivity)).trans_eq
  rw [physical_scale_new_div Ccal Z L hz]
  change L^(-(3/2:ℝ))*(Real.sqrt (q*Z^M/L^2))⁻¹/(2*Real.pi)*
    (Ce*(1+‖t‖)^degree*(Real.sqrt (3*q/L)*Z^(20/99+(5/22)*δ:ℝ))*
      Z^((33/38)*((M+507*ε)/2)))=_
  calc
    _ = (Ce/(2*Real.pi))*(1+‖t‖)^degree*
        (L^(-(3/2:ℝ))*(Real.sqrt (q*Z^M/L^2))⁻¹*
          Real.sqrt (3*q/L)*Z^(20/99+(5/22)*δ:ℝ)*Z^((33/38)*((M+507*ε)/2))) := by ring
    _ = _ := by rw [unmarked_normalization q Z L _ _ hq hz hl,unmarked_saving];ring


end
end ZetaZeroFree.Analytic.Energy
