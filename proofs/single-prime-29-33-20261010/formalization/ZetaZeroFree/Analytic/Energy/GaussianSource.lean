import ZetaZeroFree.Analytic.Energy.PhysicalSource
import ZetaZeroFree.Analytic.SourceData
import OAI.NumberTheory.DirichletL.Detector.LowGaussianSum

namespace ZetaZeroFree.Analytic.Energy
open scoped Classical BigOperators ContDiff SchwartzMap
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open ProbePhysical RayFourExpansion MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Id" => Ideal Eis

lemma one_slot_subset_cases (J : Finset (Fin 1)) : J=∅ ∨ J=Finset.univ := by
  by_cases h : (0 : Fin 1)∈J
  · right
    ext i
    fin_cases i
    simp [h]
  · left
    ext i
    fin_cases i
    simp [h]

lemma one_slot_tuple_count (b Z : ℝ) (hZ : 1≤Z)
    (T : Fin 1→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^z) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤128*max 1 b*Z^z := by
  rw [Fintype.card_pi]
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,Fintype.card_coe]
  apply (canonicalSlot_count (T 0) (hT 0) (max 1 b*Z^z)
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _)
      (Real.one_le_rpow hZ (by norm_num [z])))
    (fun P hP=>(hnorm 0 P hP).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))).trans_eq
  ring

lemma selected_inverse_univ {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (slots : Fin K→Finset Eis)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (U t : ℝ) :
    lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η slots Finset.univ W P t) η S hS
      (lowSelectedIdeal slots Finset.univ) U t = lowMarkedInverseRow η S hS 1 U t := by
  letI : IsEmpty (SelectedSlot (Finset.univ : Finset (Fin K))) :=
    ⟨fun i=>by simpa [SelectedSlot] using i.property⟩
  have hc : (Finset.univ : Finset (LowSelectedTuple slots Finset.univ)).card=1 := by
    rw [Finset.card_univ]
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨fun i=>isEmptyElim i,?_⟩
    intro f
    funext i
    exact isEmptyElim i
  funext σ m
  simp [lowSelectedInverseRow,lowSelectedWeight,lowSelectedIdeal,hc]

def oneSlotUnselectedEquiv (slots : Fin 1→Finset Eis) :
    LowUnselectedTuple slots Finset.univ ≃ ↥(slots 0) where
  toFun p := p ⟨0,Finset.mem_univ _⟩
  invFun a i := ⟨a.val,by
    have hi : i.val=(0 : Fin 1) := Subsingleton.elim _ _
    simpa [hi] using a.property⟩
  left_inv p := by
    funext i
    have hi : i=⟨(0 : Fin 1),Finset.mem_univ _⟩ := Subtype.ext (Subsingleton.elim _ _)
    subst i
    rfl
  right_inv a := rfl

lemma one_slot_unselected_product (slots : Fin 1→Finset Eis)
    (p : LowUnselectedTuple slots Finset.univ) :
    (∏i : (Finset.univ : Finset (Fin 1)),(p i).val)=(p ⟨0,Finset.mem_univ _⟩).val := by
  letI : Unique ↥(Finset.univ : Finset (Fin 1)) :=
    { default := ⟨0,Finset.mem_univ _⟩
      uniq := fun i=>Subtype.ext (Subsingleton.elim _ _) }
  simp
  congr 1

lemma one_slot_unselected_count (slots : Fin 1→Finset Eis) :
    Fintype.card (LowUnselectedTuple slots Finset.univ)=(slots 0).card := by
  rw [Fintype.card_congr (oneSlotUnselectedEquiv slots),Fintype.card_coe]

lemma unselected_weight_bound {K : ℕ} (slots : Fin K→Finset Eis)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K))
    (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) (P : Fin K→ℝ)
    (p : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P p‖≤elementNorm (∏i : J,(p i).val)^(-(3/2:ℝ)) := by
  have hl := lowUnselectedProduct_norm_pos slots hslots J p
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hl.le _),norm_prod]
  exact mul_le_of_le_one_right (by positivity)
    (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun i _=>hW i.val _))

lemma one_slot_unmarked_reciprocal_bound (a b Z : ℝ) (ha : 0<a) (hZ : 1≤Z)
    (T : Fin 1→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→a*Z^z≤(Ideal.absNorm P.val:ℝ) ∧
      (Ideal.absNorm P.val:ℝ)≤b*Z^z) :
    (∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) Finset.univ,
      (elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val))⁻¹)≤128*max 1 b/a := by
  let slots := fun i=>canonicalSlotSupport (T i)
  have hnormE (i : Fin 1) (n : Eis) (hn : n∈slots i) : a*Z^z≤elementNorm n := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).1
  have hterm (p : LowUnselectedTuple slots Finset.univ) :
      (elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val))⁻¹≤(a*Z^z)⁻¹ := by
    rw [one_slot_unselected_product]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) (hnormE 0 _ (p ⟨0,Finset.mem_univ _⟩).property)
  have hc := canonicalSlot_count (T 0) (hT 0) (max 1 b*Z^z)
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (by norm_num [z])))
    (fun P hP=>(hnorm 0 P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  calc
    _ ≤ ∑p : LowUnselectedTuple slots Finset.univ,(a*Z^z)⁻¹ :=
      Finset.sum_le_sum (fun p _=>hterm p)
    _ = ((canonicalSlotSupport (T 0)).card:ℝ)*(a*Z^z)⁻¹ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,one_slot_unselected_count,slots]
    _ ≤ (128*(max 1 b*Z^z))*(a*Z^z)⁻¹ := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by have hz : Z^z≠0 := ne_of_gt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hZ) _);field_simp

lemma new_compensation_scale_mass_bound (η : HeckeFamily.Character) (C : CalibrationData)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin 1→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^z)
    (J : Finset (Fin 1)) (W : Fin 1→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight η W (fun i=>Z^z) (fun i=>(p i).val) J)
      (fun p=>Z^(13/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^(15/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^z)≤
        (elementNorm C.generator*(128*max 1 b))*Z := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin 1) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=>Z^z) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^z)‖)*
        lowPhysicalScale C (Z^(13/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(15/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^M := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=>Z^z) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^z)‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _) (fun (i : SelectedSlot J) _=>hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [physical_scale_new_div C Z _ hz]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (one_slot_tuple_count b Z hZ T hT hnorm)
    (show 0≤elementNorm C.generator*Z^M by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b))*(Z^z*Z^M) := by ring
    _=_ := by rw [←Real.rpow_add hz];norm_num [z,M]

lemma eventually_new_physical_scales {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤1/6) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
      ∀(slots : Fin K→Finset Eis),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤Z^(13/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤Z^(15/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(5/22:ℝ) by norm_num)).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0<elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=>hn i _ (p i).property) J
  have hb := lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=>p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤Z^(13/33:ℝ) := by
    apply hb.trans
    calc
      _≤Z^(5/22:ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)];norm_num
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))


theorem new_remote_gaussian_dyads (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin 1→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^z)→
    ∀(J : Finset (Fin 1))(W : Fin 1→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength (fun _ : Fin 1=>z) J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^z) J (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(-1:ℝ) := by
  have hep : 0<ε/2 := by linarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((13/3:ℝ)/(ε/2))
  have hN' : (13/3:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b))
  have hq : 0<q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [eventually_new_physical_scales (fun _ : Fin 1=>z) (by intro i;norm_num [z]) (by simp [z];norm_num) b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤b*Z^z := by
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=>compensationSubsetWeight η W (fun i=>Z^z) (fun i=>(p i).val) J)
    (fun p=>Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=>Z^(13/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=>Z^(15/33:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=>W i.val) (fun p i=>elementNorm (p i.val).val/Z^z)
    (Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤C0*Z^(-1:ℝ) from by
      have hm := new_compensation_scale_mass_bound η (calibrationForSet S hS) b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤Cg*((q*(128*max 1 b))*Z)*(Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (low_remote_power Z (lowSelectedLength (fun _ : Fin 1=>z) J) ε N hZ.1.le
          (by have hb := lowLength_bounds (fun _ : Fin 1=>z) (by intro i;norm_num [z]) (by simp [z];norm_num) J;linarith) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

theorem new_unmarked_compensated_slice
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (a b τ : ℝ) (ha : 0<a) (hτ : 0<τ) (hτ1 : τ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWB : ∀x,‖W1 x‖≤B) :
    ∃ degree : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
    ∀ σ : ℝ, |σ|≤τ/4 →
    ∀ (T : Fin 1→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→a*Z^z≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^z) →
    ∀ (W : Fin 1→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ t : ℝ,
      ‖∑p : (∀i,canonicalSlotSupport (T i)),
        compensationSubsetWeight η W (fun _=>Z^z) (fun i=>(p i).val) Finset.univ*
        compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val)
          Finset.univ (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) (Z^(1+σ)) t*
        selectedSlotFactor W (fun _=>Z^z) (fun i=>(p i).val) Finset.univ t‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+1000*τ:ℝ) := by
  obtain ⟨degree,Ci,Z₀,hCi,hZ₀,he⟩ := unmarked_integral_normalized_new τ hτ hτ1
    W0 W1 a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB
    (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) η S hS hbad a τ ha hτ hτ1.le
  let Ccal := calibrationForSet S hS
  let q := elementNorm Ccal.generator
  have hq : 0<q := calibration_elementNorm_pos Ccal
  refine ⟨degree,Ci*(128*max 1 b/a),by positivity,?_⟩
  have hbbase := (tendsto_rpow_atTop (show 0<(33/38:ℝ) by norm_num)).eventually (Filter.eventually_ge_atTop Z₀)
  have hqevent := (tendsto_rpow_atTop (show 0<(2/33:ℝ) by norm_num)).eventually (Filter.eventually_ge_atTop q)
  have hbevent := (tendsto_rpow_atTop (show 0<(2/11:ℝ) by norm_num)).eventually (Filter.eventually_ge_atTop b)
  filter_upwards [hbbase,hqevent,hbevent,Filter.eventually_gt_atTop (1:ℝ)] with Z hbase hqcap hbcap hZ
  refine ⟨hZ,?_⟩
  intro σ hσ T hT hnorm W hW t
  have hz : 0<Z := lt_trans zero_lt_one hZ
  let slots := fun i=>canonicalSlotSupport (T i)
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hnormE (i : Fin 1) (n : Eis) (hn : n∈slots i) : a*Z^z≤elementNorm n ∧ elementNorm n≤b*Z^z := by
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hpol := compensation_tuple_low_polynomial η S hS hbad W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 hW0s slots hslots Finset.univ W (fun _=>Z^z)
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) (Z^(1+σ)) t (by positivity) (by positivity) (by positivity)
  rw [hpol]
  apply (norm_sum_le _ _).trans
  have hterm (p : LowUnselectedTuple slots Finset.univ) :
      ‖lowUnselectedWeight slots Finset.univ W (fun _=>Z^z) p*
        ((Real.sqrt (lowPhysicalScale Ccal
          (Z^(13/33:ℝ)/elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val))
          (Z^(15/33:ℝ)/elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
        ∫v : ℝ,lowSeparatedIntegrand Ccal W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (Z^(13/33:ℝ)/elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val))
          (Z^(15/33:ℝ)/elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val))
          (lowSelectedInverseRow Finset.univ
            (lowSelectedWeight η slots Finset.univ W (fun _=>Z^z) t)
            η S hS (lowSelectedIdeal slots Finset.univ) (Z^(1+σ)) t) v‖ ≤
      (Ci*(1+‖t‖)^degree*Z^(20/99+1000*τ:ℝ))*
        (elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val))⁻¹ := by
    let L := elementNorm (∏i : (Finset.univ : Finset (Fin 1)),(p i).val)
    have hl := lowUnselectedProduct_norm_pos slots hslots Finset.univ p
    have hl1 : 1≤L := by
      dsimp only [L]
      rw [one_slot_unselected_product]
      exact slotProduct_norm_ge_one (fun _ : Fin 1=>(p ⟨0,Finset.mem_univ _⟩).val)
        (fun _=>hslots 0 _ (p ⟨0,Finset.mem_univ _⟩).property) {0} |>.trans_eq (by simp [slotProduct])
    have hLa : a*Z^z≤L := by dsimp only [L];rw [one_slot_unselected_product];exact (hnormE 0 _ (p ⟨0,Finset.mem_univ _⟩).property).1
    have hLcap : L≤Z^(1/3:ℝ) := calc
      _ ≤ b*Z^z := by dsimp only [L];rw [one_slot_unselected_product];exact (hnormE 0 _ (p ⟨0,Finset.mem_univ _⟩).property).2
      _ ≤ Z^(2/11:ℝ)*Z^z := mul_le_mul_of_nonneg_right hbcap (by positivity)
      _ = _ := by rw [←Real.rpow_add hz];norm_num [z]
    have hY : 1≤Z^(15/33:ℝ)/L := (one_le_div hl).mpr
      (hLcap.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)))
    have hPscale : 1≤(Z^(15/33:ℝ)/L)^2/lowPhysicalScale Ccal (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L) := by
      rw [physical_scale_new_div Ccal Z L hz]
      have hratio : (Z^(15/33:ℝ)/L)^2/(q*Z^M/L^2)=(Z^(15/33:ℝ))^2/(q*Z^M) := by field_simp
      rw [hratio]
      apply (le_div_iff₀ (by positivity : 0<q*Z^M)).mpr
      simp only [one_mul]
      calc
        _ ≤ Z^(2/33:ℝ)*Z^M := mul_le_mul_of_nonneg_right hqcap (by positivity)
        _ = _ := by rw [←Real.rpow_add hz,←Real.rpow_mul_natCast hz.le];norm_num [M]
    have hi := he Z σ L hZ.le hbase (hσ.trans (by linarith)) hl1 hLa hLcap hqcap hY hPscale t
    rw [norm_mul,norm_mul,selected_inverse_univ,low_mellin_normalizer_norm _ (lowPhysicalScale_pos Ccal _ _ (div_pos (by positivity) hl) (div_pos (by positivity) hl))]
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (unselected_weight_bound slots hslots Finset.univ W hW (fun _=>Z^z) p)
        (by positivity)) (norm_nonneg _)).trans
    have hi' := hi
    rw [show L^(-(3/2:ℝ))*(Real.sqrt (lowPhysicalScale Ccal (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L)))⁻¹/(2*Real.pi)=
      L^(-(3/2:ℝ))*((Real.sqrt (lowPhysicalScale Ccal (Z^(13/33:ℝ)/L) (Z^(15/33:ℝ)/L)))⁻¹/(2*Real.pi)) by ring] at hi'
    apply hi'.trans
    calc
      _ = (Ci*(1+‖t‖)^degree*Z^(20/99-35/627+(33/38)*(507*τ/2)+(5/22)*τ:ℝ))*L⁻¹ := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  rw [←Finset.mul_sum]
  have hr := one_slot_unmarked_reciprocal_bound a b Z ha hZ.le T hT hnorm
  calc
    _ ≤ (Ci*(1+‖t‖)^degree*Z^(20/99+1000*τ:ℝ))*(128*max 1 b/a) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring


theorem new_central_compensated_tuple
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (a b τ : ℝ) (ha : 0<a) (hτ : 0<τ) (hτ1 : τ≤1/2)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0)
    (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWB : ∀x,‖W1 x‖≤B) :
    ∃ degree : ℕ, ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
    ∀ (T : Fin 1→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) →
      (∀i P,P∈T i→a*Z^z≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^z) →
    ∀ (J : Finset (Fin 1)) (σ : ℝ), |σ|≤τ/4 →
    ∀ (W : Fin 1→ℝ→ℂ), (∀i x,‖W i x‖≤1) → ∀ t : ℝ,
      ‖∑p : (∀i,canonicalSlotSupport (T i)),
        compensationSubsetWeight η W (fun _=>Z^z) (fun i=>(p i).val) J*
        compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val)
          J (Z^(13/33:ℝ)) (Z^(15/33:ℝ))
          (Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J+σ)) t*
        selectedSlotFactor W (fun _=>Z^z) (fun i=>(p i).val) J t‖ ≤
      C*(1+‖t‖)^degree*Z^(20/99+1000*τ:ℝ) := by
  obtain ⟨dm,Cm,hCm,hm⟩ := selected_compensated_marked_slice_shift W0 W1 a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB
    η S hS hbad 1 (max 1 b) (1000*τ) (by positivity)
  obtain ⟨du,Cu,hCu,hu⟩ := new_unmarked_compensated_slice η S hS hbad a b τ ha hτ
    (lt_of_le_of_lt hτ1 (by norm_num)) W0 W1 a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB
  refine ⟨dm+du,Cm+Cu,add_pos hCm hCu,?_⟩
  filter_upwards [hm,hu] with Z hmZ huZ
  refine ⟨hmZ.1,?_⟩
  intro T hT hout hnorm J σ hσ W hW t
  have hz : 0<Z := lt_trans zero_lt_one hmZ.1
  have hheight : 1≤1+‖t‖ := le_add_of_nonneg_right (norm_nonneg t)
  rcases one_slot_subset_cases J with rfl|rfl
  · have hdis : Pairwise (fun i j : Fin 1=>Disjoint (T i) (T j)) := by
      intro i j hne
      exact False.elim (hne (Subsingleton.elim _ _))
    let H : SelectedSlot (∅ : Finset (Fin 1))→ℝ := fun _=>max 1 b*Z^z
    have hH1 : ∀i,1≤H i := fun _=>one_le_mul_of_one_le_of_one_le
      (le_max_left _ _) (Real.one_le_rpow hmZ.1.le (by norm_num [z]))
    have hH : ∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i := fun i P hP=>
      (hnorm i.val P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    have hprod : (∏i,H i)≤max 1 b*Z^z := by
      letI : Unique (SelectedSlot (∅ : Finset (Fin 1))) :=
        { default := ⟨0,by simp [SelectedSlot]⟩
          uniq := fun i=>Subtype.ext (Subsingleton.elim _ _) }
      simp [H]
    have hσm : |σ|≤min (1/2) ((1000*τ)/1000)/2 := by
      rw [show (1000*τ)/1000=τ by ring,min_eq_right hτ1]
      linarith
    have hh := hmZ.2 σ hσm T hT hout hdis H hH1 hH hprod W hW (fun _=>Z^z) t
    have hs : 1+lowSelectedLength (fun _ : Fin 1=>z) ∅=Nstar := by
      simp [lowSelectedLength,Fin.sum_univ_succ,z,Nstar]
      norm_num
    rw [hs]
    apply hh.trans
    gcongr
    · linarith
    · exact Nat.le_add_right _ _
  · have hh := huZ.2 σ hσ T hT hnorm W hW t
    have hs : lowSelectedLength (fun _ : Fin 1=>z) Finset.univ=0 := by simp [lowSelectedLength]
    rw [hs,add_zero]
    apply hh.trans
    gcongr
    · linarith
    · exact Nat.le_add_left _ _


theorem new_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (a b τ : ℝ) (ha : 0<a) (hτ : 0<τ) (hτ1 : τ≤1/2)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB : 0≤B)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWB : ∀x,‖W1 x‖≤B) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin 1→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→
      (∀i P,P∈T i→a*Z^z≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^z)→
    ∀(J : Finset (Fin 1))(U : ℝ),0<U→
      Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J-τ/4)≤U→
      U≤Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J+τ/4)→
    ∀(W : Fin 1→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
        W (fun _=>Z^z) J (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) U
          (Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J)) V hV‖≤
        C*Z^(20/99+1000*τ)*gaussianJointMoment V hV degree
          (U/Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J)) := by
  obtain ⟨degree,C,hC,he⟩ := new_central_compensated_tuple η S hS hbad a b τ ha hτ hτ1
    W0 W1 a0 b0 a1 b1 B ha0 ha1 hab1 hB hW0 hW1 hW0s hW1s hWB
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hnorm J U hU hlo hhi W hW V hV
  let σ := lowCentralShift Z U (lowSelectedLength (fun _ : Fin 1=>z) J)
  have hscale : Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J+σ)=U := lowCentralShift_scale _ _ _ hZ.1 hU
  have hσ : |σ|≤τ/4 := by
    rw [←hscale,Real.rpow_le_rpow_left_iff hZ.1] at hlo hhi
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  apply lowCommonDyad_norm_of_bound
  intro t
  have hh := hZ.2 T hT hout hnorm J σ hσ W hW t
  rw [hscale] at hh
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh


theorem new_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1/2)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin 1→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→(∀i P,P∈T i→a*Z^z≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^z)→
    ∀(J : Finset (Fin 1))(W : Fin 1→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength (fun _ : Fin 1=>z) J) (ε/2) ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^z) J (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤C*Z^(20/99+1002*ε) := by
  obtain ⟨degree,C,hC,he⟩ := new_central_gaussian_dyad η S hS hbad
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hnorm J W hW
  let R := Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J)
  let f := fun j : ℕ=>if lowRemote Z (lowSelectedLength (fun _ : Fin 1=>z) J) (ε/2) ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
      W (fun i=>Z^z) J (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^(20/99+1000*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength (fun _ : Fin 1=>z) J) (ε/2) ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hnorm J ((2:ℝ)^j) (by positivity) (by simpa only [show (ε/2)/2=ε/4 by ring] using hlo) (by simpa only [show (ε/2)/2=ε/4 by ring] using hhi) W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤f j := by dsimp [f];split_ifs <;>positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^(20/99+1000*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^(20/99+1000*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^(20/99+1000*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^(20/99+1000*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^(20/99+1000*ε)*Z^((1+lowSelectedLength (fun _ : Fin 1=>z) J)*ε)) := by ring
        _≤_ := by
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := lowLength_bounds (fun _ : Fin 1=>z) (by intro i;norm_num [z]) (by simp [z];norm_num) J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

theorem new_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (a b ε : ℝ) (ha : 0<a) (hε : 0<ε) (hε1 : ε≤1/2)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧
    ∀(T : Fin 1→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→(∀i P,P∈T i→a*Z^z≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^z)→
    ∀(J : Finset (Fin 1))(W : Fin 1→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=>lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=>canonicalSlotSupport (T i))
          W (fun i=>Z^z) J (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength (fun _ : Fin 1=>z) J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤C*Z^(20/99+1002*ε) := by
  obtain ⟨Cc,hCc,hcentral⟩ := new_central_gaussian_dyads η S hS hbad
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := new_remote_gaussian_dyads S hS b (ε/2) (by positivity) V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hnorm J W hW
  have hc' := hc.2 T hT hout hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=>lowRemote Z (lowSelectedLength (fun _ : Fin 1=>z) J) (ε/2) ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤Z^(20/99+1002*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by linarith)
  calc
    _≤Cc*Z^(20/99+1002*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤Cc*Z^(20/99+1002*ε)+Cr*Z^(20/99+1002*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by ring

/-- The actual one-slot physical probe at the new three scale exponents. -/
theorem new_compensatedPhysicalProbe_bound
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (a b ε : ℝ) (ha : 0<a) (hε : 0<ε)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1)
    (W : Fin 1→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1)
    (Lwindow : Fin 1→ℝ) (hLwindow : ∀i,0≤Lwindow i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤Lwindow i) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop, 1<Z ∧
    ∀ (T : Fin 1→Finset PrimeIdeal), (∀i P,P∈T i→Supported P.val) →
      (∀i P,P∈T i→P.val∉S) →
      (∀i P,P∈T i→a*Z^z≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤b*Z^z) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=>canonicalSlotSupport (T i)) W (fun _=>Z^z)
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖ ≤ C*Z^(20/99+ε:ℝ) := by
  let τ := min (1/4) (ε/2000)
  have hτ : 0<τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ≤1/2 := (min_le_left _ _).trans (by norm_num)
  have hloss : 1002*τ≤ε := by have hh : τ≤ε/2000 := min_le_right _ _;linarith
  obtain ⟨V,hV,hm,hprobe⟩ := compensatedPhysicalProbe_common_gaussian W Lwindow hLwindow hwindow
  choose C hC he using fun A : Finset (Fin 1)=>new_all_gaussian_dyads η S hS hbad a b τ ha hτ hτ1
    (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1 hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin 1)).powerset,C A)+1
  have hC0 : 0<C0 := by
    have hh : 0≤∑A∈(Finset.univ : Finset (Fin 1)).powerset,C A := Finset.sum_nonneg (fun A _=>(hC A).le)
    dsimp only [C0]
    linarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.2 he] with Z hZ
  have hz1 : 1<Z := (hZ ∅).1
  refine ⟨hz1,?_⟩
  intro T hT hout hnorm
  have hz : 0<Z := lt_trans zero_lt_one hz1
  let slots := fun i=>canonicalSlotSupport (T i)
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=>canonicalSlotSupport_nonzero _ (hT i)
  have hcenter (A : Finset (Fin 1)) :
      Z*(∏i∈Finset.univ\A,Z^z)=Z^(1+lowSelectedLength (fun _ : Fin 1=>z) A) := by
    rw [←Real.rpow_sum_of_pos hz]
    unfold lowSelectedLength
    rw [Real.rpow_add hz,Real.rpow_one]
    congr 2
    exact (Finset.sum_coe_sort (Finset.univ\A) (fun _ : Fin 1=>z)).symm
  have hp := hprobe η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    slots hslots (fun _=>Z^z) (fun _=>by positivity)
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (by positivity) (by positivity) hz
  change compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1 slots W (fun _=>Z^z)
    (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z =
    ∑A∈(Finset.univ : Finset (Fin 1)).powerset,
      ∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 slots W (fun _=>Z^z) A
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^z) (V A) (hV A) at hp
  simp_rw [hcenter] at hp
  rw [hp]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin 1)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 slots W (fun _=>Z^z) A
        (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) ((2:ℝ)^j)
        (Z^(1+lowSelectedLength (fun _ : Fin 1=>z) A)) (V A) (hV A)‖≤C A*Z^(20/99+ε:ℝ) := by
    have hh := (hZ A).2 T hT hout hnorm A W hW
    apply hh.2.trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz1.le (by linarith)) (hC A).le
  apply (Finset.sum_le_sum (fun A _=>hterm A)).trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp only [C0];linarith) (by positivity)


theorem source_physicalProbe_bound {e : ℝ} (F : ZetaZeroFree.Analytic.SourceData e)
    (η : HeckeFamily.Character) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      1<Z ∧ ‖F.physicalProbe η Z‖≤C*Z^(20/99+ε:ℝ) := by
  have hWF (x : ℝ) : ‖F.W x‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded x).1]
    exact (F.bounded x).2
  have hw (i : Fin 1) (x : ℝ) : ‖(F.w x:ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded x).1]
    exact (F.bounded x).2
  have hwindow (i : Fin 1) (y : ℝ) (hy : (F.w (Real.exp y):ℂ)≠0) : |y|≤Real.log 2 := by
    have hne : F.w (Real.exp y)≠0 := by exact_mod_cast hy
    have hx := F.support (Function.mem_support.mpr hne)
    have hy0 : 0≤y := (Real.one_le_exp_iff.mp hx.1.le)
    rw [abs_of_nonneg hy0,←Real.log_exp y]
    exact Real.log_le_log (Real.exp_pos y) hx.2.le
  obtain ⟨C,hC,he⟩ := new_compensatedPhysicalProbe_bound η F.S F.maximal F.exclusions.bad
    1 2 ε (by norm_num) hε F.W F.W 1 2 1 2 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) F.complex_support F.complex_support F.W.smooth' F.W.smooth'
    hWF hWF (fun _ x=>(F.w x:ℂ)) hw (fun _=>Real.log 2)
    (fun _=>Real.log_nonneg (by norm_num)) hwindow
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  have hz : 0<Z := lt_trans zero_lt_one hZ.1
  have hT (i : Fin 1) (P : PrimeIdeal) (hP : P∈F.pools Z i) : Supported P.val :=
    ProbeRaySlots.pool_supported _ F.S F.exclusions 1 2 _ P hP
  have hout (i : Fin 1) (P : PrimeIdeal) (hP : P∈F.pools Z i) : P.val∉F.S :=
    ((ProbeRaySlots.mem_pool _ F.S 1 2 _ P).mp hP).2.2.2
  have hnorm (i : Fin 1) (P : PrimeIdeal) (hP : P∈F.pools Z i) :
      1*Z^z≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤2*Z^z := by
    have hp := ProbeRaySlots.pool_norm_bounds _ F.S (a:=1) (b:=2)
      (by norm_num) (by norm_num) (Real.rpow_pos_of_pos hz (5/33:ℝ)) P hP
    constructor
    · simpa [z,mul_one] using hp.1.le
    · simpa [z,mul_comm] using hp.2
  change ‖compensatedPhysicalProbe η (calibrationForSet F.S F.maximal) F.W F.W
    (fun i=>canonicalSlotSupport (F.pools Z i)) (fun _ x=>(F.w x:ℂ))
    (fun _=>Z^(5/33:ℝ)) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z‖≤_
  simpa only [z] using hZ.2 (F.pools Z) hT hout hnorm

theorem source_probe_bound {e : ℝ} (F : ZetaZeroFree.Analytic.SourceData e)
    (η : HeckeFamily.Character) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ Z : ℝ in Filter.atTop,
      1<Z ∧ F.normalizer Z≠0 ∧ ‖F.probe η Z‖≤C*Z^(20/99+ε:ℝ) := by
  let cs := PrincipalMellinResidues.sourceResidueConstant F.W F.W F.modulus
  obtain ⟨c,hc,hcsEq⟩ := ZetaZeroFree.Analytic.Principal.sourceResidueConstant_positive
    F.modulus F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
  have hcs : cs≠0 := by change PrincipalMellinResidues.sourceResidueConstant F.W F.W F.modulus≠0;rw [hcsEq];exact_mod_cast hc.ne'
  obtain ⟨C,hC,he⟩ := source_physicalProbe_bound F η (ε/2) (by positivity)
  have hn := ZetaZeroFree.Analytic.Principal.one_prime_normalizer_eventually F.modulus ⊤
    le_top F.S F.w 1 2 (by norm_num) (by norm_num) F.support F.smooth F.compact
    F.positive_support (fun y=>(F.bounded y).1) F.nonzero cs hcs (ε/2) (by positivity)
  refine ⟨C*‖cs⁻¹‖,mul_pos hC (norm_pos_iff.mpr (inv_ne_zero hcs)),?_⟩
  filter_upwards [he,hn] with Z heZ hnZ
  have hn' : F.normalizer Z≠0 ∧ ‖(F.normalizer Z)⁻¹‖≤‖cs⁻¹‖*Z^(ε/2) := by
    change F.normalizer Z≠0 ∧ ‖(F.normalizer Z)⁻¹‖≤‖cs⁻¹‖*Z^(ε/2) at hnZ
    exact hnZ
  refine ⟨heZ.1,hn'.1,?_⟩
  have hz : 0<Z := lt_trans zero_lt_one heZ.1
  rw [ZetaZeroFree.Analytic.SourceData.probe,div_eq_mul_inv,norm_mul]
  apply (mul_le_mul heZ.2 hn'.2 (norm_nonneg _) (by positivity)).trans_eq
  calc
    _ = (C*‖cs⁻¹‖)*(Z^(20/99+ε/2:ℝ)*Z^(ε/2)) := by ring
    _ = _ := by rw [←Real.rpow_add hz];congr 1;congr 1;ring


end
end ZetaZeroFree.Analytic.Energy
