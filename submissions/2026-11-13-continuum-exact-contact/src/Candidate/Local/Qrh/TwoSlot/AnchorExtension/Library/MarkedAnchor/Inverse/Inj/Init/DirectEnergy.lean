/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from hailey_collet_1252270103 `Record12518109Gain/Upstream/DeletionInverse.lean`
(`direct_prime_product`, `deleted_direct_slots_initial`; itself adapted from PR63
gao-balanced-marked-20261017) and openai_baseline `Dictionary/InverseMarkedReferenceTuples.lean`
(`sum_tuple_original`) (Apache-2.0), via `Inverse/Init/DirectEnergy.lean` and
`Inverse/Chain.lean`. Modified by Sil (2026-11-12): the INJECTIVE product `injDirectSlots`
(tuples of distinct primes, pools may overlap, no `PairwiseDisjoint`); the dictionary lands on the
injective tuple sum `∑ x ∈ tupInj L` of `Inj.source_energy_inj`; injective oracle
`GoodEnergyExistsInj`. Proofs otherwise unchanged. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Inj.Init.SourceEnergy
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Inj.Reduction
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.AdmImage

/-!
# Inverse.Inj.Init.DirectEnergy — top of the injective initialization chain; the injective chain

* `inj_direct_product`, `sum_tupInj_original`, **`deleted_inj_slots_initial`**: the injective
  dictionary `polynomial · injDirectSlots = ∑_{x ∈ tupInj L} … originalTotalPolynomial …`;
* **`direct_energy_of_oracle_inj`**: the injective inverse marked moment
  (`Chain.inverseMarkedSumInj`) from the injective oracle on `InitState Pmax Smax κ`;
* `AdmCoversInj` (covering without `PairwiseDisjoint`), `imageAdm'_coversInj`;
* **`oracleChain_of_covers`**, **`oracleChain_image`**, **`oracleChain_canonical`**:
  `Inj.OracleChain canonicalFamily imageAdm'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open DetectorDictionaryInverseRawConjugateGates
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open ConcreteTraceCRT InverseMoment InverseInitialProfile InverseInitialRawDictionary
open InverseInitialConjugateEnergy InverseInitialMarkedDictionary
open InverseInitialPhysicalSlots InverseInitialExcludedPeriod InverseInitialPoissonBridge
open InverseInitialEnergyCallerWindow
open IdealMobiusDivisorSum
open Qrh.MarkedAnchor.Interface.Contract
open Qrh.MarkedAnchor.Inverse
local notation "O" => HeckeFamily.O

/-! ## The injective dictionary -/

theorem inj_direct_product {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : O) (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (U : ℝ) (hU : 0<U) (ell : ι → ℝ) :
    injDirectSlots u L β (fun i => U^(ell i)) =
      ((U^(-(∑i,ell i)/2) : ℝ) : ℂ) *
        ∑p ∈ (Fintype.piFinset L).filter (fun x => Function.Injective x),
          (∏i,β i (p i))*idealRowHom u (∏i,p i) := by
  have hnorm (w : ℝ) : (Real.sqrt (U^w) : ℂ)⁻¹ = ((U^(-w/2) : ℝ) : ℂ) := by
    rw [←Complex.ofReal_inv]
    congr 1
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hU.le,←Real.rpow_neg hU.le]
    congr 1
    ring
  unfold injDirectSlots
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpL := Fintype.mem_piFinset.mp hp
  split_ifs with hinj
  · have hc (i : ι) : Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
        (L i) (β i) (U^(ell i)) (p i) = ((U^(-ell i/2) : ℝ) : ℂ) * β i (p i) := by
      unfold Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      rw [if_pos (hpL i), hnorm]
    simp only [hc]
    rw [map_prod, ← slot_normalization U hU ell, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  · simp

theorem sum_tupInj_original {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → Finset (Ideal O)) (f : (ι → Ideal O) → ℂ) :
    (∑q ∈ tupInj L, f (fun i => (q i).val)) =
      ∑q ∈ (Fintype.piFinset L).filter (fun x => Function.Injective x), f q := by
  rw [Finset.sum_filter, ← sum_tuple_original L, tupInj, Finset.sum_filter]

/-- **Injective dictionary.** The actual inverse polynomial times the injective product of
normalized prime slots is the injective tuple source of `Inj.source_energy_inj`. -/
theorem deleted_inj_slots_initial {ι : Type} [Fintype ι] [DecidableEq ι]
    (data : RowData) (u : NonzeroElement) (L : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (ell : ι → ℝ) (W : ℝ → ℂ)
    (U r bo : ℝ) (hU : 0<U) (hW : ∀x,W x≠0 → x≤bo)
    (hne : ∀i,∀P∈L i,idealCoeff (deletedBase data) P≠0) :
    polynomial ((data.character u).excludePrimes (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data))) true W (U^r) 0 0 *
      injDirectSlots u.val L β (fun i => U^(ell i)) =
    ∑x ∈ tupInj L, (∏i,β i (x i).val / idealCoeff (deletedBase data) (x i).val) *
      originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u.val := by
  let χ := (data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))
  let η := (idealCoeff (deletedBase data)).toMonoidHom
  have hprod (p : ι → Ideal O)
      (hp : p∈(Fintype.piFinset L).filter (fun x => Function.Injective x)) : η (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact hne i (p i) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hp).1 i)
  have he := indexed_mark_initial ((Fintype.piFinset L).filter (fun x => Function.Injective x))
    (fun p=>∏i,p i)
    (fun p=>(∏i,β i (p i))/η (∏i,p i)) η χ u.val (actual_deleted_row data u)
    W U r (∑i,ell i) 0 0 hU (idealsUpTo ⌈U^r*bo⌉₊)
    (finite_source_cover W (U^r) bo (Real.rpow_pos_of_pos hU _) hW)
  have hs : (∑p∈(Fintype.piFinset L).filter (fun x => Function.Injective x),
      ((∏i,β i (p i))/η (∏i,p i))*idealCoeff χ (∏i,p i)) =
      ∑p∈(Fintype.piFinset L).filter (fun x => Function.Injective x),
        (∏i,β i (p i))*idealRowHom u.val (∏i,p i) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [actual_deleted_row data u]
    change _ / η (∏i,p i) * (η (∏i,p i)*_) = _
    rw [←mul_assoc,div_mul_cancel₀ _ (hprod p hp)]
  rw [hs] at he
  rw [inj_direct_product _ _ _ _ hU,←mul_assoc,he]
  rw [sum_tupInj_original L (fun p=>(∏i,β i (p i)/idealCoeff (deletedBase data) (p i))*
    originalTotalPolynomial (originalSource U r bo) (∏i,p i) η (fun _=>1) W U r (∑i,ell i) u.val)]
  apply Finset.sum_congr rfl
  intro p _
  have ht : twistedProfile W 0 0 = W := by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht,originalTotal_supported_source _ _ _ (deletedBase_zero_unsupported data)]
  simp only [η,map_prod,Finset.prod_div_distrib]
  rfl

/-! ## The injective direct energy -/

theorem direct_energy_of_oracle_inj (W : ℝ → ℂ) (ao bo : ℝ) (hao : 0<ao)
    (hab : ao≤bo) (hsW : Function.support W⊆Icc ao bo) (hW : ContDiff ℝ ∞ W)
    (Adm : SlotAdm) (Pmax Smax κ eta : ℝ) (hP0 : 0 ≤ Pmax) (hS0 : 0 ≤ Smax)
    (hPS : Pmax+Smax ≤ 1) (heta : 0 < eta) (heta7 : 7*eta ≤ 1) (hκ : 9*eta ≤ κ)
    (K : ℕ)
    (horacle : ∀ (Wf : 𝓢(ℝ,ℂ)) (lf hf : ℝ), 0 < lf → lf ≤ hf →
      Function.support (Wf : ℝ → ℂ) ⊆ Icc lf hf →
      GoodEnergyExistsInj Adm (InitState Pmax Smax κ) eta 3 K Wf) :
    ∀ data : RowData, ∃ (degree : ℕ) (C U₀ : ℝ), 0<C ∧ 1<U₀ ∧
      ∀ U : ℝ, U₀≤U → ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι≤K →
      ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ),
        (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
        (∀i,∀P∈L i,((P.absNorm : ℝ)/U^(ell i))∈Icc (1 : ℝ) 2) →
        (∀i,∀P∈L i,‖β i P‖≤1) →
        (∀i,((deletedBase data).modulus.absNorm : ℝ)<U^(ell i)) →
      ∀ hv : ℝ, 0 ≤ hv → DirectAdm Adm data L ell β U hv →
      ∀r : ℝ, 0≤r → r≤Pmax → (∑i,ell i)≤Smax →
      ∀rows : Finset NonzeroElement, (∀u∈rows,‖eisEmbedding u.val‖^2≤U) → ∀θ : ℝ,
      (∑u∈rows,‖polynomial (data.character u) true (childLogTest W θ) (U^r) 0 0 *
          injDirectSlots u.val L β (fun i => U^(ell i))‖^2) ≤
        C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 := by
  have henergy := source_energy_inj W ao bo hao hab hsW hW
    Adm Pmax Smax κ 3 eta eta eta eta eta heta heta heta (by linarith) heta
    (by linarith) le_rfl heta K horacle
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩ := raw_conjugate_base_gates data
  obtain ⟨degree,C,U₀,hC,hU₀,henergy⟩ := henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩ := eventually_atTop.mp (marked_shift_eventually data eta heta)
  have hev : ∀ᶠ U : ℝ in atTop, (2:ℝ)^K ≤ U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  obtain ⟨Uscale,hscale⟩ := eventually_atTop.mp hev
  let divs := idealDivisors (∏P∈excluded data,P)
  refine ⟨degree,((divs.card : ℝ)+1)^2*C,max U₀ (max Ushift Uscale),by positivity,
    lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst dec hK L ell β hell hp hratio hβ hlarge hv hv0 hadm r hr hrP hSm rows
    hrows θ
  have hU0 : U₀≤U := (le_max_left _ _).trans hU
  have hUone : 1<U := hU₀.trans_le hU0
  have hUp : 0<U := zero_lt_one.trans hUone
  have hpow : (2:ℝ)^K ≤ U^eta := hscale U (((le_max_right _ _).trans (le_max_right _ _)).trans hU)
  have hS0' : 0 ≤ ∑i,ell i := Finset.sum_nonneg (fun i _ => hell i)
  have hg (i : ι) (P : Ideal O) (hP : P∈L i) :=
    Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.deleted_prime_gates data P
      (hp i P hP) ((hlarge i).trans_le
      (by simpa only [one_mul] using
        (le_div_iff₀ (Real.rpow_pos_of_pos hUp _)).mp (hratio i P hP).1))
  let coeff := fun i P => β i P / idealCoeff (deletedBase data) P
  have hc (i : ι) (P : Ideal O) (hP : P∈L i) : ‖coeff i P‖≤1 := by
    dsimp [coeff]
    rw [norm_div,(hg i P hP).2.2.1,div_one]
    exact hβ i P hP
  let marker : ℝ → ℂ := (Icc (1 : ℝ) 2).indicator (fun _=>1)
  have hm : Function.support marker⊆Icc (1 : ℝ) 2 := Set.support_indicator_subset
  have hlive (i : ι) (P : Ideal O) (hP : P∈L i) : marker ((P.absNorm : ℝ)/U^(ell i))≠0 := by
    simp [marker,hratio i P hP]
  let rawRows := rows.image (fun u=>u.val)
  have hrawRows (u : O) (hu : u∈rawRows) : ‖eisEmbedding u‖^2≤U^(1:ℝ) := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    rw [Real.rpow_one]
    exact hrows v hv
  have hsupport : ∀x,childLogTest W θ x≠0 → x≤bo := by
    intro x hx
    exact (hsW (by intro hz;exact hx (by simp [childLogTest,hz]))).2
  let mark := fun u : NonzeroElement => injDirectSlots u.val L β (fun i => U^(ell i))
  have hd := marked_fixed_deletion data rows (childLogTest W θ) (U^r) 0 0 bo
    (Real.rpow_pos_of_pos hUp _) hsupport mark
  have hjbound (j : Ideal O) (hj : j∈divs) :
      (∑u∈rows,‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true (childLogTest W θ)
        (U^r/(j.absNorm : ℝ)) 0 0 * mark u‖^2) ≤
        C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 := by
    have hjshift := (hshift U (((le_max_left _ _).trans (le_max_right _ _)).trans hU)).2 j hj r
    have hscaleU : U^(shiftedExponent data U r j) = U^r/(j.absNorm : ℝ) := hjshift.2.2
    have hGJ (J : Finset ι) : (∑i∈J,ell i) ≤ ∑i,ell i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hell i)
    have hGJ0 (J : Finset ι) : 0 ≤ ∑i∈J,ell i := Finset.sum_nonneg (fun i _ => hell i)
    have he := henergy U hU0 hpow hK L ell coeff hell hp
      (fun i P hP=>(hg i P hP).2.2.2) hratio hc
      (fun i P hP=>by rw [hqset];exact (hg i P hP).1)
      (fun _=>marker) (fun _=>hm) hlive
      (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
      hperiod (fun I hI=>raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
      hv hv0 hadm 1 (shiftedExponent data U r j) zero_le_one (by norm_num)
      (fun J => by have := hGJ J; have := hGJ0 J; linarith [hjshift.1])
      hP0 (hjshift.2.1.trans hrP) hSm le_rfl (by linarith [hjshift.2.1])
      rawRows hrawRows θ
    rw [Finset.sum_image (fun u _ v _ he=>Subtype.ext he)] at he
    rw [← hscaleU]
    convert he using 1
    · apply Finset.sum_congr rfl
      intro u _
      rw [deleted_inj_slots_initial data u L β ell (childLogTest W θ) U
        (shiftedExponent data U r j) bo hUp hsupport (fun i P hP=>(hg i P hP).2.1)]
    · rw [show (1:ℝ)+15*eta+eta+eta+eta = 1+18*eta by ring]
  apply hd.trans
  change (divs.card : ℝ) * (∑j∈divs,_) ≤ _
  calc
    _ ≤ (divs.card : ℝ) * ∑j∈divs,C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjbound) (by positivity)
    _ = (divs.card : ℝ)^2*C*(1+hv)^(2*degree)*U^(1+18*eta)*((1+‖θ‖)^degree)^2 := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := by gcongr <;> linarith

/-! ## The injective chain -/

/-- `AdmCovers'` without `PairwiseDisjoint` (pools may overlap). -/
def AdmCoversInj (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm) : Prop :=
  ∀ mesh : ℝ, 0 < mesh → ∀ cls : SlotClass, fam cls →
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (data : RowData)
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (Z hv : ℝ),
    0 ≤ hv → cls ι data L ell β Z hv → (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) →
    (∀ i, ∀ P ∈ L i, Prime P) →
    (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
    (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
    (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
    DirectAdm (Adm mesh cls) data L ell β Z hv

/-- The image filter covers all slot vectors (it does not require disjoint pools). -/
theorem imageAdm'_coversInj (fam : SlotClass → Prop) (hmono : ∀ cls, fam cls → HeightMono cls) :
    AdmCoversInj fam imageAdm' := by
  intro mesh _ cls hcls ι _ _ data L ell β Z hv hv0 hc hell hm hp hratio hβ hlarge J Dpool t
  dsimp only [imageAdm', imageAdm]
  refine ⟨cls,rfl,data,L,ell,β,J,t,
    hmono cls hcls ι data L ell β Z hv (hv+|t|) (le_add_of_nonneg_right (abs_nonneg t)) hc,
    hell,hm,hp,hratio,hβ,hlarge,rfl,?_,?_,fun _ => rfl,fun _ _ => rfl,
    le_add_of_nonneg_left hv0⟩
  · intro i
    simp
  · intro i P
    simp [InverseInitialCommonLists.poolList]

/-- **The injective chain** from a covering filter (pattern of `Chain.oracleChainSep'_of_covers`;
degree `2 degree`, `hvFactor_le`). -/
theorem oracleChain_of_covers (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm)
    (hcov : AdmCoversInj fam Adm) : OracleChain fam Adm := by
  intro Pmax Smax κ hP hS hκ hsum horacle ε hε
  set eta : ℝ := min (min (ε/18) (κ/9)) (1/7) with heta_def
  have heta : 0 < eta := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have h1 : eta ≤ ε/18 := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : eta ≤ κ/9 := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : eta ≤ 1/7 := min_le_right _ _
  obtain ⟨mesh,hmesh,hor⟩ := horacle eta heta
  refine ⟨mesh,hmesh,?_⟩
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  have hd := direct_energy_of_oracle_inj Φ ao bo hao hab hΦs hΦ (Adm mesh cls) Pmax Smax
    κ eta hP hS (by linarith) heta (by linarith) (by linarith) K
    (fun Wf lf hf hlf hlh hs => hor cls hcls K Wf lf hf hlf hlh hs)
  obtain ⟨degree,C,U₀,hC,hU₀,hb⟩ := hd data
  refine ⟨2*degree,C,U₀,hC,hU₀,fun Z hZ => ?_⟩
  intro ι _ _ hK L ell β hv hv0 hc hell hm hp hratio hβ hlarge M hM1 hM2 r hadm rows hrows θ
  have hM : M = 1 := le_antisymm hM2 hM1
  subst hM
  obtain ⟨hr0,hrP,_,hSS⟩ := hadm
  rw [mul_one] at hrP hSS
  have hZ1 : 1 ≤ Z := hU₀.le.trans hZ
  have hbound := hb Z hZ hK L ell β hell hp hratio hβ hlarge hv hv0
    (hcov mesh hmesh cls hcls data L ell β Z hv hv0 hc hell hm hp hratio hβ hlarge)
    r hr0 hrP hSS rows (fun u hu => by simpa using hrows u hu) θ
  unfold inverseMarkedSumInj
  refine hbound.trans ?_
  have hpowZ : Z^(1+18*eta) ≤ Z^(1+ε) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hZp : 0 ≤ Z^(1+18*eta) := Real.rpow_nonneg (zero_le_one.trans hZ1) _
  calc C*(1+hv)^(2*degree)*Z^(1+18*eta)*((1+‖θ‖)^degree)^2
      = C*Z^(1+18*eta)*((1+hv)^(2*degree)*((1+‖θ‖)^degree)^2) := by ring
    _ ≤ C*Z^(1+ε)*((1+‖θ‖+hv)^(2*degree))^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpowZ hC.le) (hvFactor_le θ hv hv0 degree)
          (by positivity) (mul_nonneg hC.le (hZp.trans hpowZ))

/-- **`Inj.OracleChain fam imageAdm'`** for every family of height-monotone classes; the
canonical instance `oracleChain_canonical` is used by the driver. -/
theorem oracleChain_image (fam : SlotClass → Prop) (hmono : ∀ cls, fam cls → HeightMono cls) :
    OracleChain fam imageAdm' :=
  oracleChain_of_covers fam imageAdm' (imageAdm'_coversInj fam hmono)

theorem oracleChain_canonical : OracleChain canonicalFamily imageAdm' :=
  oracleChain_image canonicalFamily canonicalFamily_heightMono

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.deleted_inj_slots_initial
#print axioms Qrh.MarkedAnchor.Inverse.Inj.direct_energy_of_oracle_inj
#print axioms Qrh.MarkedAnchor.Inverse.Inj.oracleChain_canonical
