/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Reduction
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Init.DirectEnergy
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.Cardinality
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionOverlapSlots

/-!
# Inverse.Chain — the oracle chain `OracleChain'` on overlapping pools

The contract `InverseRectAt` bounds the FULL product `∏ directSlot` on possibly OVERLAPPING pools.
The chain exit is therefore

* **full ⇐ injective**: `full_le_inj_energy` — HC
  `Collision.full_energy_cardinality` with `B = 1`, `L = 256` (`normalizedPrimeCoeff_bound/_energy`,
  `directPrimeSlot_sum_atoms`): the full moment is `≤ collisionGrowth(1,256,K)^K` times the
  maximum over all sub-embeddings `J ↪ ι` of the INJECTIVE (marked-squarefree) moment
  `injDirectSlots`. Source level: `UniformInverseRectSourceInj.toFull` (for slot classes closed
  under sub-embeddings, `EmbClosed`; `canonicalFamily_embClosed`).
* `OracleChainInj' fam Adm`: the injective chain (oracle on `InitState` ⇒ injective source on the
  parent rectangle); `oracleChain'_of_inj` turns it into `OracleChain'`. The injective chain with
  the injective oracle is `Inj.OracleChain` (`Inj/Reduction`, proved in `Inj/Init/DirectEnergy`).
* `oracleChainSep'_of_covers`: what the disjoint-list `Init/*` clone proves — the contract
  restricted to pairwise disjoint pools (`UniformInverseRectSourceSep`), for which the injective
  and the full product coincide.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-! ## Full ⇐ injective -/

/-- The injective (marked-squarefree) product of normalized prime slots: only tuples of
distinct primes. -/
def injDirectSlots (u : O) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ x ∈ Fintype.piFinset L, if Function.Injective x then
    ∏ i, CanonicalRowCompletion.idealRowHom u (x i) *
      Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
        (L i) (β i) (X i) (x i) else 0

/-- HC's `injectiveTuplePolynomial` over an atom set containing all pools is the tuple sum over
the pools. -/
theorem injTuple_atoms {I : Type} [Fintype I] (atoms : Finset (Ideal O))
    (L : I → Finset (Ideal O)) (hL : ∀ i, L i ⊆ atoms) (c : I → Ideal O → ℂ)
    (hc : ∀ i p, p ∉ L i → c i p = 0) :
    Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.injectiveTuplePolynomial
        (fun i (p : atoms) => c i p.val) =
      ∑ x ∈ Fintype.piFinset L, if Function.Injective x then ∏ i, c i (x i) else 0 := by
  unfold Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.injectiveTuplePolynomial
  have hinj (x : I → atoms) : Function.Injective x ↔ Function.Injective (fun j => (x j).val) :=
    ⟨fun h => Subtype.val_injective.comp h, fun h a b hab => h (congrArg Subtype.val hab)⟩
  refine Finset.sum_bij_ne_zero (fun x _ _ => fun j => (x j).val) ?_ ?_ ?_ ?_
  · intro x _ hx
    rw [Fintype.mem_piFinset]
    intro j
    by_contra hj
    apply hx
    split_ifs
    · exact Finset.prod_eq_zero (Finset.mem_univ j) (hc j _ hj)
    · rfl
  · intro x _ _ y _ _ hxy
    funext j
    exact Subtype.ext (congrFun hxy j)
  · intro y hy hy0
    have hmem := Fintype.mem_piFinset.mp hy
    refine ⟨fun j => ⟨y j, hL j (hmem j)⟩, Finset.mem_univ _, ?_, rfl⟩
    by_cases hyi : Function.Injective y
    · rw [if_pos hyi] at hy0
      rw [if_pos ((hinj _).mpr hyi)]
      exact hy0
    · rw [if_neg hyi] at hy0
      exact absurd rfl hy0
  · intro x _ _
    by_cases h : Function.Injective x
    · rw [if_pos h, if_pos ((hinj x).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hinj x).mpr h'))]

/-- **Full ⇐ injective.** The full product moment on possibly overlapping pools is bounded by
`collisionGrowth(1,256,K)^K` times a bound for the injective moments of all sub-embeddings. -/
theorem full_le_inj_energy {ι : Type} [Fintype ι] [DecidableEq ι] {Row : Type}
    (rows : Finset Row) (uu : Row → O) (D : Row → ℂ) (L : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (X : ι → ℝ) (E : ℝ) (hE : 0 ≤ E) (K : ℕ)
    (hK : Fintype.card ι ≤ K) (hX : ∀ i, 1 ≤ X i) (hβ : ∀ i, ∀ p ∈ L i, ‖β i p‖ ≤ 1)
    (hp : ∀ i, ∀ p ∈ L i, p ≠ 0) (hN : ∀ i, ∀ p ∈ L i, (p.absNorm : ℝ) ≤ 2 * X i)
    (hinj : ∀ (J : Type) [Fintype J] [DecidableEq J] (f : J ↪ ι),
      (∑ v ∈ rows, ‖D v * injDirectSlots (uu v) (fun j => L (f j)) (fun j => β (f j))
        (fun j => X (f j))‖^2) ≤ E) :
    (∑ v ∈ rows, ‖D v * ∏ i, directSlot (uu v) (L i) (β i) (X i)‖^2) ≤
      (QRH.Record1252270103Source.Collision.collisionGrowth 1 256 K)^K * E := by
  let atoms : Finset (Ideal O) := Finset.univ.biUnion L
  have hLa (i : ι) : L i ⊆ atoms := fun p hp' => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp'⟩
  let a : Row → ι → atoms → ℂ := fun v i p => CanonicalRowCompletion.idealRowHom (uu v) p.val *
    Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      (L i) (β i) (X i) p.val
  let w : ι → atoms → ℝ := fun i p =>
    ‖Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      (L i) (β i) (X i) p.val‖
  have hfull (v : Row) : (∏ i, directSlot (uu v) (L i) (β i) (X i)) = ∏ i, ∑ p : atoms, a v i p := by
    apply Finset.prod_congr rfl
    intro i _
    exact Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.directPrimeSlot_sum_atoms
      (uu v) (L i) atoms (β i) (X i) (hLa i)
  have hsum : (∑ v ∈ rows, ‖D v * ∏ i, directSlot (uu v) (L i) (β i) (X i)‖^2) =
      ∑ v ∈ rows, ‖D v * ∏ i, ∑ p : atoms, a v i p‖^2 :=
    Finset.sum_congr rfl (fun v _ => by rw [hfull v])
  rw [hsum]
  refine QRH.Record1252270103Source.Collision.full_energy_cardinality rows a w D 1 256 E le_rfl
    (by norm_num) hE (fun _ _ => norm_nonneg _)
    (fun i p => Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff_bound
      (L i) (β i) (X i) 1 (hX i) zero_le_one (hβ i) p.val) ?_ ?_ K hK ?_
  · intro i
    dsimp only [w]
    rw [Finset.sum_coe_sort atoms (fun p => ‖Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      (L i) (β i) (X i) p‖^2)]
    exact Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff_energy
      atoms (L i) (β i) (X i) 1 (hX i) zero_le_one (hβ i) (hp i) (hN i)
  · intro v _ i p
    dsimp only [a, w]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (CanonicalRowCompletion.idealRowHom_norm _ _)
  · intro J _ f
    refine le_of_eq_of_le ?_ (hinj J f)
    apply Finset.sum_congr rfl
    intro v _
    congr 3
    exact injTuple_atoms atoms (fun j => L (f j)) (fun j => hLa (f j))
      (fun j p => CanonicalRowCompletion.idealRowHom (uu v) p *
        Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
          (L (f j)) (β (f j)) (X (f j)) p)
      (fun j p hpj => by
        simp [Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff, hpj])

/-! ## The injective contract and its source-level exit -/

/-- `inverseMarkedSum` with the injective product. -/
def inverseMarkedSumInj (data : RowData) (Φ : ℝ → ℂ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ)
    (rows : Finset NonzeroElement) (Z r θ : ℝ) : ℝ :=
  ∑ u ∈ rows, ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
    injDirectSlots u.val L β (fun i => Z^(ell i))‖^2

/-- `InverseRectAt` with the injective product (pools may overlap). -/
def InverseRectAtInj (cls : SlotClass) (ρ : AnchorRect) (Φ : ℝ → ℂ) (K : ℕ)
    (mesh Mmin Mmax ε Z : ℝ) (data : RowData) (degree : ℕ) (C : ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
  ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (hv : ℝ), 0 ≤ hv →
    cls ι data L ell β Z hv →
    (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) → (∀ i, ∀ P ∈ L i, Prime P) →
    (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
    (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
    (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ r : ℝ, ρ.Admissible r (∑ i, ell i) M →
  ∀ rows : Finset NonzeroElement,
    (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z^M) → ∀ θ : ℝ,
    inverseMarkedSumInj data Φ L ell β rows Z r θ ≤ C*Z^(M+ε)*((1+‖θ‖+hv)^degree)^2

/-- `InverseRectSource` with the injective product (same quantifier order, degree per datum). -/
def InverseRectSourceInj (fam : SlotClass → Prop) (ρ : AnchorRect) (mesh ε : ℝ) : Prop :=
  ∀ K : ℕ, ∀ cls : SlotClass, fam cls →
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support Φ ⊆ Icc ao bo →
    ContDiff ℝ ∞ Φ →
  ∀ data : RowData, ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → InverseRectAtInj cls ρ Φ K mesh 1 1 ε Z data degree C

def UniformInverseRectSourceInj (fam : SlotClass → Prop) (ρ : AnchorRect) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧ InverseRectSourceInj fam ρ mesh ε

/-- A slot class closed under sub-embeddings of the slot type. -/
def EmbClosed (cls : SlotClass) : Prop :=
  ∀ {ι J : Type} (f : J ↪ ι) (data : RowData) (L : ι → Finset (Ideal O)) (ell : ι → ℝ)
    (β : ι → Ideal O → ℂ) (Z hv : ℝ), cls ι data L ell β Z hv →
    cls J data (fun j => L (f j)) (fun j => ell (f j)) (fun j => β (f j)) Z hv

theorem canonicalSlotsRay_embClosed (W : ℝ → ℂ) (σ : ℝ) (rayM : Ideal O) [NeZero rayM]
    (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) :
    EmbClosed (canonicalSlotsRay W σ rayM G hH) := by
  intro ι J f data L ell β Z hv h
  obtain ⟨θ, v, hvb, hc⟩ := h
  exact ⟨θ, fun j => v (f j), fun j => hvb (f j), fun j => hc (f j)⟩

theorem canonicalFamily_embClosed (cls : SlotClass) (h : canonicalFamily cls) : EmbClosed cls := by
  obtain ⟨W, _, _, rayM, _, G, hH, rfl⟩ := h
  exact canonicalSlotsRay_embClosed W _ rayM G hH

/-- **Chain exit:** the injective source gives the full (overlapping-pool) source, for
classes closed under sub-embeddings; the constant is multiplied by `collisionGrowth(1,256,K)^K`. -/
theorem InverseRectSourceInj.toFull {fam : SlotClass → Prop} {ρ : AnchorRect} {mesh ε : ℝ}
    (hemb : ∀ cls, fam cls → EmbClosed cls) (h : InverseRectSourceInj fam ρ mesh ε) :
    InverseRectSource fam ρ mesh ε := by
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree, C, Z₀, hC, hZ₀, hb⟩ := h K cls hcls Φ ao bo hao hab hΦs hΦ data
  refine ⟨degree, (QRH.Record1252270103Source.Collision.collisionGrowth 1 256 K)^K * C, Z₀,
    mul_pos (pow_pos (zero_lt_one.trans_le
      (QRH.Record1252270103Source.Collision.collisionGrowth_one_le 1 256 K)) K) hC, hZ₀,
    fun Z hZ => ?_⟩
  intro ι _ _ hK L ell β hv hv0 hc hell hm hp hratio hβ hlarge M hM1 hM2 r hadm rows hrows θ
  have hZ1 : 1 < Z := hZ₀.trans_le hZ
  have hZp : 0 < Z := zero_lt_one.trans hZ1
  set E : ℝ := C*Z^(M+ε)*((1+‖θ‖+hv)^degree)^2 with hEdef
  have hE : 0 ≤ E := by positivity
  have hcalc := full_le_inj_energy rows (fun u => u.val)
    (fun u => polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0)
    L β (fun i => Z^(ell i)) E hE K hK (fun i => Real.one_le_rpow hZ1.le (hell i)) hβ
    (fun i p hp' => (hp i p hp').ne_zero)
    (fun i p hp' => (div_le_iff₀ (Real.rpow_pos_of_pos hZp _)).mp (hratio i p hp').2) ?_
  · unfold inverseMarkedSum
    refine hcalc.trans (le_of_eq ?_)
    rw [hEdef]; ring
  · intro J _ _ f
    have hJK : Fintype.card J ≤ K := (Fintype.card_le_of_injective f f.injective).trans hK
    have hsum : (∑ j, ell (f j)) ≤ ∑ i, ell i := by
      rw [← Finset.sum_map Finset.univ f ell]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hell i)
    have hadm' : ρ.Admissible r (∑ j, ell (f j)) M :=
      AnchorRect.admissible_downward hadm hadm.1 le_rfl
        (Finset.sum_nonneg (fun j _ => hell (f j))) hsum
    exact hb Z hZ hJK (fun j => L (f j)) (fun j => ell (f j)) (fun j => β (f j)) hv hv0
      (hemb cls hcls f data L ell β Z hv hc) (fun j => hell (f j)) (fun j => hm (f j))
      (fun j => hp (f j)) (fun j => hratio (f j)) (fun j => hβ (f j)) (fun j => hlarge (f j))
      M hM1 hM2 r hadm' rows hrows θ

theorem UniformInverseRectSourceInj.toFull {fam : SlotClass → Prop} {ρ : AnchorRect}
    (hemb : ∀ cls, fam cls → EmbClosed cls) (h : UniformInverseRectSourceInj fam ρ) :
    UniformInverseRectSource fam ρ := by
  intro ε hε
  obtain ⟨mesh, hmesh, hs⟩ := h ε hε
  exact ⟨mesh, hmesh, hs.toFull hemb⟩

/-! ## The oracle chain on overlapping pools -/

/-- The injective oracle chain: the canonical oracle on the initial states of the parent
rectangle gives the INJECTIVE source on that rectangle (pools may overlap). -/
def OracleChainInj' (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm) : Prop :=
  ∀ Pmax Smax κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 < κ → Pmax+Smax+κ < 1 →
    OracleOn' Adm fam (InitState Pmax Smax κ) →
    UniformInverseRectSourceInj fam ⟨Pmax, Smax⟩

/-- `OracleChain'` from the injective chain and `full_le_inj_energy`. -/
theorem oracleChain'_of_inj (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm)
    (hemb : ∀ cls, fam cls → EmbClosed cls) (h : OracleChainInj' fam Adm) :
    OracleChain' fam Adm :=
  fun Pmax Smax κ hP hS hκ hsum horacle =>
    (h Pmax Smax κ hP hS hκ hsum horacle).toFull hemb

/-! ## The separated (disjoint-pool) chain -/

/-- `InverseRectAt` restricted to pairwise disjoint pools. -/
def InverseRectAtSep (cls : SlotClass) (ρ : AnchorRect) (Φ : ℝ → ℂ) (K : ℕ)
    (mesh Mmin Mmax ε Z : ℝ) (data : RowData) (degree : ℕ) (C : ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
  ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (hv : ℝ), 0 ≤ hv →
    cls ι data L ell β Z hv →
    (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) → (∀ i, ∀ P ∈ L i, Prime P) →
    (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
    (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
    (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
    (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ r : ℝ, ρ.Admissible r (∑ i, ell i) M →
  ∀ rows : Finset NonzeroElement,
    (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z^M) → ∀ θ : ℝ,
    inverseMarkedSum data Φ L ell β rows Z r θ ≤ C*Z^(M+ε)*((1+‖θ‖+hv)^degree)^2

def UniformInverseRectSourceSep (fam : SlotClass → Prop) (ρ : AnchorRect) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
  ∀ K : ℕ, ∀ cls : SlotClass, fam cls →
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support Φ ⊆ Icc ao bo →
    ContDiff ℝ ∞ Φ →
  ∀ data : RowData, ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → InverseRectAtSep cls ρ Φ K mesh 1 1 ε Z data degree C

/-- `Adm mesh cls` admits the dictionary images of all `cls`-slot vectors of mesh `≤ mesh`
with pairwise disjoint pools. -/
def AdmCovers' (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm) : Prop :=
  ∀ mesh : ℝ, 0 < mesh → ∀ cls : SlotClass, fam cls →
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (data : RowData)
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (Z hv : ℝ),
    0 ≤ hv → cls ι data L ell β Z hv → (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) →
    (∀ i, ∀ P ∈ L i, Prime P) → (((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint L) →
    (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
    (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
    (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
    DirectAdm (Adm mesh cls) data L ell β Z hv

/-- The height factor of the direct (oracle) bound, `(1+hv)^(2d) ((1+‖θ‖)^d)^2`, is below the
contract's height factor `((1+‖θ‖+hv)^(2d))^2` at degree `2d`. -/
theorem hvFactor_le (θ hv : ℝ) (hv0 : 0 ≤ hv) (d : ℕ) :
    (1+hv)^(2*d)*((1+‖θ‖)^d)^2 ≤ ((1+‖θ‖+hv)^(2*d))^2 := by
  have h1 : (1+hv)^(2*d) ≤ (1+‖θ‖+hv)^(2*d) :=
    pow_le_pow_left₀ (by linarith) (by linarith [norm_nonneg θ]) _
  have h2 : ((1+‖θ‖)^d)^2 ≤ ((1+‖θ‖+hv)^d)^2 := by
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+‖θ‖)
      (by linarith : 1+‖θ‖ ≤ 1+‖θ‖+hv) d
    exact pow_le_pow_left₀ (by positivity) this 2
  calc _ ≤ (1+‖θ‖+hv)^(2*d)*((1+‖θ‖+hv)^d)^2 := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = ((1+‖θ‖+hv)^(2*d))^2 := by ring

/-- The disjoint-list `Init/*` clone: the oracle gives the separated source (degree per datum;
the height-aware oracle gives degree `2 degree`). -/
theorem oracleChainSep'_of_covers (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm)
    (hcov : AdmCovers' fam Adm) (Pmax Smax κ : ℝ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hκ : 0 < κ)
    (hsum : Pmax+Smax+κ < 1) (horacle : OracleOn' Adm fam (InitState Pmax Smax κ)) :
    UniformInverseRectSourceSep fam ⟨Pmax, Smax⟩ := by
  intro ε hε
  set eta : ℝ := min (min (ε/18) (κ/9)) (1/7) with heta_def
  have heta : 0 < eta := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have h1 : eta ≤ ε/18 := (min_le_left _ _).trans (min_le_left _ _)
  have h2 : eta ≤ κ/9 := (min_le_left _ _).trans (min_le_right _ _)
  have h3 : eta ≤ 1/7 := min_le_right _ _
  obtain ⟨mesh,hmesh,hor⟩ := horacle eta heta
  refine ⟨mesh,hmesh,?_⟩
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  have hd := direct_energy_of_oracle Φ ao bo hao hab hΦs hΦ (Adm mesh cls) Pmax Smax
    κ eta hP hS (by linarith) heta (by linarith) (by linarith) K
    (fun Wf lf hf hlf hlh hs => hor cls hcls K Wf lf hf hlf hlh hs)
  obtain ⟨degree,C,U₀,hC,hU₀,hb⟩ := hd data
  refine ⟨2*degree,C,U₀,hC,hU₀,fun Z hZ => ?_⟩
  intro ι _ _ hK L ell β hv hv0 hc hell hm hp hdis hratio hβ hlarge M hM1 hM2 r hadm rows hrows θ
  have hM : M = 1 := le_antisymm hM2 hM1
  subst hM
  obtain ⟨hr0,hrP,_,hSS⟩ := hadm
  rw [mul_one] at hrP hSS
  have hZ1 : 1 ≤ Z := hU₀.le.trans hZ
  have hbound := hb Z hZ hK L ell β hell hp hdis hratio hβ hlarge hv hv0
    (hcov mesh hmesh cls hcls data L ell β Z hv hv0 hc hell hm hp hdis hratio hβ hlarge)
    r hr0 hrP hSS rows (fun u hu => by simpa using hrows u hu) θ
  unfold inverseMarkedSum
  refine hbound.trans ?_
  have hpowZ : Z^(1+18*eta) ≤ Z^(1+ε) := Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hZp : 0 ≤ Z^(1+18*eta) := Real.rpow_nonneg (zero_le_one.trans hZ1) _
  calc C*(1+hv)^(2*degree)*Z^(1+18*eta)*((1+‖θ‖)^degree)^2
      = C*Z^(1+18*eta)*((1+hv)^(2*degree)*((1+‖θ‖)^degree)^2) := by ring
    _ ≤ C*Z^(1+ε)*((1+‖θ‖+hv)^(2*degree))^2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpowZ hC.le) (hvFactor_le θ hv hv0 degree)
          (by positivity) (mul_nonneg hC.le (hZp.trans hpowZ))

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.full_le_inj_energy
#print axioms Qrh.MarkedAnchor.Inverse.UniformInverseRectSourceInj.toFull
#print axioms Qrh.MarkedAnchor.Inverse.oracleChain'_of_inj
#print axioms Qrh.MarkedAnchor.Inverse.oracleChainSep'_of_covers
