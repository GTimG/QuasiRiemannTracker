/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Coloring
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Reduction

/-!
# Inverse.Inj.Oracle — the injective canonical-energy oracle

The parent lists may overlap, so the oracle bounds the column energy of the
INJECTIVE mark (`primeMarkInj`) and has no `PairwiseDisjoint lists` hypothesis.

* `finiteCanonicalMarkedRowInj`, `normalizedColumnEnergyInj`: baseline `finiteCanonicalMarkedRow`
  / `normalizedColumnEnergy` with `primeMarkInj`.
* `rowInj_coloring`, **`normalizedColumnEnergyInj_le`**: the injective column energy is
  `≤ (|S|^|S|)^2` times a uniform bound for the energies of all pairwise disjoint sub-lists
  (HC coloring, `Inj.Coloring`).
* `GoodRankMomentsInj`, `GoodPoolRankMomentsInj`, `GoodEnergyExistsInj` (= `GoodEnergyExists`
  with the injective energy, no disjointness), `mono_good/mono_adm/union/of_withNonneg`.
* Native branch: `goodEnergyExistsInj_of_canonical` (baseline `CanonicalEnergyExists` on the
  colored disjoint sub-lists, cost `(K^K)^2`), `goodEnergyExistsInj_lowLive`.
* `OracleOnInj'`, `oracleOnInj'_lowLive`, `oracleOnInj'_initState`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped Classical BigOperators SchwartzMap
open Set
open OAI OAI.SevenEighths OAI.SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
open CanonicalCoefficientClass FirstPassCubeLabels SecondPassArithmetic
open Qrh.MarkedAnchor.Inverse
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => ActualEisensteinCubic.O

section Rows
variable {ι σ : Type} [DecidableEq ι]
variable (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
variable (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- The canonical marked row with the injective mark. -/
def finiteCanonicalMarkedRowInj (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedChildRow p hp hcop hg pool Ψ m
    (fun U => primeMarkInj slots lists a U * W (primeProductNorm p U / X)) f k

/-- The normalized column energy with the injective mark. -/
def normalizedColumnEnergyInj (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m (primaryGenerator f) k
        slots lists a W X‖^2

theorem fixedChildRow_mark_sum {T : Type*} (s : Finset T) (pool : Finset ι) (Ψ : O →* ℂ)
    (m : O) (M : T → Finset ι → ℂ) (w : Finset ι → ℂ) (f k : O) :
    fixedChildRow p hp hcop hg pool Ψ m (fun U => (∑ c ∈ s, M c U) * w U) f k =
      ∑ c ∈ s, fixedChildRow p hp hcop hg pool Ψ m (fun U => M c U * w U) f k := by
  unfold fixedChildRow secondChildColumn
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  dsimp only
  rw [Finset.sum_mul, Finset.mul_sum]

theorem fixedChildRow_mark_smul (r : ℂ) (pool : Finset ι) (Ψ : O →* ℂ)
    (m : O) (H : Finset ι → ℂ) (f k : O) :
    r * fixedChildRow p hp hcop hg pool Ψ m H f k =
      fixedChildRow p hp hcop hg pool Ψ m (fun U => r * H U) f k := by
  unfold fixedChildRow secondChildColumn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun N _ => ?_)
  ring

theorem rowInj_coloring [Fintype ι] (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    ((Fintype.card slots ^ (Fintype.card ι - Fintype.card slots) : ℕ) : ℂ) *
        finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ col : ι → slots, finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots
        (coloredLists slots lists col) a W X := by
  unfold finiteCanonicalMarkedRowInj finiteCanonicalMarkedRow
  rw [fixedChildRow_mark_smul, ← fixedChildRow_mark_sum]
  congr 1
  funext U
  rw [coloring_mark]
  ring

/-- **Injective column energy from disjoint sub-lists** (coloring, cost `(|S|^|S|)^2`). -/
theorem normalizedColumnEnergyInj_le [Fintype ι] (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O → ℝ)
    (W : ℝ → ℂ) (X Z F E : ℝ) (hD : ∀ f ∈ labels, 0 ≤ D f) (hE : 0 ≤ E)
    (h : ∀ lists' : σ → Finset ι, (∀ i, lists' i ⊆ lists i) →
      (slots : Set σ).PairwiseDisjoint lists' →
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists' a labels rows D W X Z F ≤ E) :
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F ≤
      ((slots.card ^ slots.card : ℕ) : ℝ)^2 * E := by
  rcases slots.eq_empty_or_nonempty with hS | hS
  · subst hS
    have he := h lists (fun _ => subset_rfl) (by simp)
    refine le_of_eq_of_le ?_ (he.trans_eq (by simp))
    unfold normalizedColumnEnergyInj normalizedColumnEnergy finiteCanonicalMarkedRowInj
      finiteCanonicalMarkedRow
    simp only [primeMarkInj_empty, primeMark_empty]
  have hpos : 0 < Fintype.card slots := Fintype.card_pos_iff.mpr ⟨⟨_, hS.choose_spec⟩⟩
  set n : ℕ := Fintype.card slots with hn
  set c : ℕ := n ^ (Fintype.card ι - n) with hc
  set N : ℕ := Fintype.card (ι → slots) with hN
  have hcpos : 0 < c := Nat.pow_pos hpos
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hNc : (N : ℝ) ≤ (n ^ n : ℕ) * c := by
    have : N ≤ n ^ n * c := by
      rw [hN, Fintype.card_fun, hc, ← pow_add, ← hn]
      exact Nat.pow_le_pow_right hpos (by omega)
    exact_mod_cast this
  have hcard : slots.card = n := by rw [hn, Fintype.card_coe]
  let v : (ι → slots) → Ideal O → O → ℂ := fun col f k =>
    ((Z^(-F/2) : ℝ) : ℂ) * finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
      slots (coloredLists slots lists col) a W X
  have hrow (f : Ideal O) (k : O) :
      ‖((Z^(-F/2) : ℝ) : ℂ) * finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m
          (primaryGenerator f) k slots lists a W X‖^2 ≤
        (N : ℝ) / (c : ℝ)^2 * ∑ col, ‖v col f k‖^2 := by
    have he := rowInj_coloring p hp hcop hg pool Ψ m (primaryGenerator f) k slots lists a W X
    have hc0 : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hx : ((Z^(-F/2) : ℝ) : ℂ) * finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ m
          (primaryGenerator f) k slots lists a W X = ((c : ℂ))⁻¹ * ∑ col, v col f k := by
      dsimp only [v]
      rw [← Finset.mul_sum, ← he]
      symm
      rw [mul_left_comm, inv_mul_cancel_left₀ hc0]
    rw [hx, norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    have hcs := norm_sum_sq_le_card (fun col => v col f k)
    rw [← hN] at hcs
    calc ((c : ℝ))⁻¹ ^ 2 * ‖∑ col, v col f k‖ ^ 2
        ≤ ((c : ℝ))⁻¹ ^ 2 * ((N : ℝ) * ∑ col, ‖v col f k‖^2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = _ := by field_simp
  have hcol (col : ι → slots) : (∑ f ∈ labels, D f * ∑ k ∈ rows, ‖v col f k‖^2) ≤ E :=
    h (coloredLists slots lists col) (coloredLists_subset slots lists col)
      (colored_disjoint slots lists col)
  unfold normalizedColumnEnergyInj
  calc _ ≤ ∑ f ∈ labels, D f * ∑ k ∈ rows, (N : ℝ) / (c : ℝ)^2 * ∑ col, ‖v col f k‖^2 :=
        Finset.sum_le_sum (fun f hf => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun k _ => hrow f k)) (hD f hf))
    _ = ∑ f ∈ labels, ∑ k ∈ rows, ∑ col, (N : ℝ) / (c : ℝ)^2 * (D f * ‖v col f k‖^2) := by
        refine Finset.sum_congr rfl (fun f _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun col _ => ?_)
        ring
    _ = ∑ f ∈ labels, ∑ col, ∑ k ∈ rows, (N : ℝ) / (c : ℝ)^2 * (D f * ‖v col f k‖^2) :=
        Finset.sum_congr rfl (fun f _ => Finset.sum_comm)
    _ = ∑ col, ∑ f ∈ labels, ∑ k ∈ rows, (N : ℝ) / (c : ℝ)^2 * (D f * ‖v col f k‖^2) :=
        Finset.sum_comm
    _ = (N : ℝ) / (c : ℝ)^2 * ∑ col, ∑ f ∈ labels, D f * ∑ k ∈ rows, ‖v col f k‖^2 := by
        simp only [Finset.mul_sum]
    _ ≤ (N : ℝ) / (c : ℝ)^2 * ∑ _col : ι → slots, E :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun col _ => hcol col)) (by positivity)
    _ = ((N : ℝ) / (c : ℝ))^2 * E := by
        rw [Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul]
        field_simp
    _ ≤ _ := by
        rw [hcard]
        apply mul_le_mul_of_nonneg_right _ hE
        apply pow_le_pow_left₀ (by positivity)
        rw [div_le_iff₀ hcR]
        exact hNc

end Rows

/-! ## The injective oracle -/

section Rank
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
variable (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
variable (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- `GoodRankMoments` with the injective column energy. -/
def GoodRankMomentsInj (Good : StatePred) (pool : Finset ι) (base : O →* ℂ) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : σ → ℝ) (W : 𝓢(ℝ,ℂ)) (Z eps A hv : ℝ)
    (K degree : ℕ) : Prop :=
  ∀ (Ψ : O →* ℂ), IsBaseRayTwist base Ψ → ∀ (m : O), m ≠ 0 → ∀ N V M Qwidth : ℝ,
    0 ≤ N → 0 ≤ V → 0 ≤ M → 0 ≤ Qwidth →
    ‖ConcreteTraceCRT.eisEmbedding m‖^2 = Z^Qwidth →
    ∀ (subslots : Finset σ), subslots ⊆ slots →
      Good N V M Qwidth (Real.logb Z (∏ i ∈ subslots, H i)) →
    ∀ labels : Finset (Ideal O),
      (∀ I ∈ labels, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Z^V) → ∀ s : ℝ,
    normalizedColumnEnergyInj p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z
        (N+V) ≤
      A*Z^(N+V+eps)*(1+‖s‖+hv)^(2*degree)

omit [DecidableEq σ] in
theorem goodRankMomentsInj_mono {G G' : StatePred} (hG : ∀ N V M Q z, G' N V M Q z → G N V M Q z)
    (pool : Finset ι) (base : O →* ℂ) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (H : σ → ℝ) (W : 𝓢(ℝ,ℂ)) (Z eps A A' hv : ℝ) (K degree degree' : ℕ)
    (hZ : 1 ≤ Z) (hv0 : 0 ≤ hv) (hA0 : 0 ≤ A) (hA : A ≤ A') (hd : degree ≤ degree')
    (h : GoodRankMomentsInj p hp hcop hg G pool base slots lists a H W Z eps A hv K degree) :
    GoodRankMomentsInj p hp hcop hg G' pool base slots lists a H W Z eps A' hv K degree' := by
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG' labels hlab s
  refine (h Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss (hG _ _ _ _ _ hG') labels hlab s).trans ?_
  have hZp : 0 ≤ Z^(N+V+eps) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hs1 : (1:ℝ) ≤ 1+‖s‖+hv := by linarith [norm_nonneg s]
  have hpow : (1+‖s‖+hv)^(2*degree) ≤ (1+‖s‖+hv)^(2*degree') :=
    pow_le_pow_right₀ hs1 (by omega)
  have hp0 : 0 ≤ (1+‖s‖+hv)^(2*degree) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right hA hZp) hpow hp0
    (mul_nonneg (hA0.trans hA) hZp)

omit [DecidableEq σ] in
theorem goodRankMomentsInj_union {G₁ G₂ : StatePred}
    (pool : Finset ι) (base : O →* ℂ) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (H : σ → ℝ) (W : 𝓢(ℝ,ℂ)) (Z eps A₁ A₂ hv : ℝ) (K d₁ d₂ : ℕ)
    (hZ : 1 ≤ Z) (hv0 : 0 ≤ hv) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h₁ : GoodRankMomentsInj p hp hcop hg G₁ pool base slots lists a H W Z eps A₁ hv K d₁)
    (h₂ : GoodRankMomentsInj p hp hcop hg G₂ pool base slots lists a H W Z eps A₂ hv K d₂) :
    GoodRankMomentsInj p hp hcop hg (fun N V M Q z => G₁ N V M Q z ∨ G₂ N V M Q z) pool base
      slots lists a H W Z eps (A₁+A₂) hv K (max d₁ d₂) := by
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  rcases hG with hG | hG
  · exact goodRankMomentsInj_mono p hp hcop hg (G := G₁) (G' := G₁) (fun _ _ _ _ _ h => h) pool
      base slots lists a H W Z eps A₁ (A₁+A₂) hv K d₁ (max d₁ d₂) hZ hv0 hA₁ (by linarith)
      (le_max_left _ _) h₁ Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  · exact goodRankMomentsInj_mono p hp hcop hg (G := G₂) (G' := G₂) (fun _ _ _ _ _ h => h) pool
      base slots lists a H W Z eps A₂ (A₁+A₂) hv K d₂ (max d₁ d₂) hZ hv0 hA₂ (by linarith)
      (le_max_right _ _) h₂ Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s

end Rank

/-- `GoodRankMomentsInj` on the complete outside-squarefree pool. -/
def GoodPoolRankMomentsInj (q D : ℕ) {σ : Type} [DecidableEq σ] (Good : StatePred)
    (slots : Finset σ) (lists : σ → Finset (PoolIdx q D)) (a : σ → PoolIdx q D → ℂ)
    (H : σ → ℝ) (base : O →* ℂ) (W : 𝓢(ℝ,ℂ)) (Z eps A hv : ℝ) (K degree : ℕ) : Prop :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D;
  let hF := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q);
  letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance;
  GoodRankMomentsInj (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Good Finset.univ base slots lists a H W Z eps A hv K degree

/-- **The injective oracle** (`GoodEnergyExists` with the injective column energy; the lists may
overlap). Quantifier order as `GoodEnergyExists` (`∃ B, ∀ q ≠ 0, ∃ degree C Z₀`). -/
def GoodEnergyExistsInj (Adm : SlotAdm) (Good : StatePred) (eps L : ℝ) (K : ℕ) (W : 𝓢(ℝ,ℂ)) :
    Prop :=
  ∃ B : ℝ, 1 ≤ B ∧
    ∀ q : ℕ, q ≠ 0 → ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → ∀ D : ℕ, B*Z^L ≤ D →
    ∀ {σ : Type} [DecidableEq σ] (slots : Finset σ), slots.card ≤ K →
    ∀ (lists : σ → Finset (PoolIdx q D)) (H : σ → ℝ) (a : σ → PoolIdx q D → ℂ),
      (∀ i ∈ slots, 1 ≤ H i) → (∀ i ∈ slots, ∀ P ∈ lists i, (Ideal.absNorm P.val : ℝ) ≤ H i) →
      (∀ i ∈ slots, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) →
    ∀ hv : ℝ, 0 ≤ hv → Adm q D σ slots lists H a Z hv →
    ∀ base : O →* ℂ, (∀ u, ‖base u‖ ≤ 1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
        base →
      GoodPoolRankMomentsInj q D Good slots lists a H base W Z eps C hv K degree

theorem natPow_self_pos (K : ℕ) : 0 < K ^ K := by
  rcases Nat.eq_zero_or_pos K with rfl | h
  · simp
  · exact Nat.pow_pos h

theorem natPow_self_le {n K : ℕ} (h : n ≤ K) : n ^ n ≤ K ^ K := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]; exact natPow_self_pos K
  · exact (Nat.pow_le_pow_left h n).trans (Nat.pow_le_pow_right (hn.trans_le h) h)

/-- The native injective oracle: the baseline existence on the colored disjoint sub-lists. -/
theorem goodEnergyExistsInj_of_canonical (Adm : SlotAdm) {Mcap Fcap c eps L : ℝ}
    {K : ℕ} {W : 𝓢(ℝ,ℂ)} (h : CanonicalEnergyExists Mcap Fcap c eps L K W) :
    GoodEnergyExistsInj Adm (nativeGood Mcap Fcap c) eps L K W := by
  obtain ⟨degree,B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨C,Z₀,hC,hZ₀,h⟩ := h q hq
  have hKK : (0:ℝ) < ((K ^ K : ℕ) : ℝ)^2 := by
    have := natPow_self_pos K
    positivity
  refine ⟨degree,((K ^ K : ℕ) : ℝ)^2 * C,Z₀,mul_pos hKK hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hH hP ha hv hv0 _ base hb hper
  have hZ1 : 1 < Z := hZ₀.trans_le hZ
  dsimp only [GoodPoolRankMomentsInj]
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q)
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hFa i]; infer_instance
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  have hprod1 : 1 ≤ ∏ i ∈ ss, H i := one_le_prod_of_one_le ss H (fun i hi => hH i (hss hi))
  have hprodpos : 0 < ∏ i ∈ ss, H i := zero_lt_one.trans_le hprod1
  have hw0 : 0 ≤ Real.logb Z (∏ i ∈ ss, H i) := Real.logb_nonneg hZ1 hprod1
  have hwle : (∏ i ∈ ss, H i) ≤ Z^(Real.logb Z (∏ i ∈ ss, H i)) := by
    rw [Real.rpow_logb (zero_lt_one.trans hZ1) hZ1.ne' hprodpos]
  have hE : 0 ≤ C*Z^(N+V+eps)*(1+‖s‖)^(2*degree) := by
    have := Real.rpow_nonneg (zero_le_one.trans hZ1.le) (N+V+eps)
    positivity
  have hcol := normalizedColumnEnergyInj_le (poolPrimary F) (poolPrimary_ne_zero F hFa)
    (poolPrimary_coprime F hFa) (poolPrimary_good F hFa) Finset.univ Ψ m ss lists a labels
    (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z (N+V)
    _ (fun f _ => by unfold secondLabelWeight; positivity) hE ?_
  · refine hcol.trans ?_
    have hcard : ss.card ≤ K := (Finset.card_le_card hss).trans hslots
    have hle : ((ss.card ^ ss.card : ℕ) : ℝ)^2 ≤ ((K ^ K : ℕ) : ℝ)^2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast natPow_self_le hcard
    have hZp : 0 ≤ Z^(N+V+eps) := Real.rpow_nonneg (zero_le_one.trans hZ1.le) (N+V+eps)
    calc _ ≤ ((K ^ K : ℕ) : ℝ)^2 * (C*Z^(N+V+eps)*(1+‖s‖)^(2*degree)) :=
          mul_le_mul_of_nonneg_right hle hE
      _ ≤ ((K ^ K : ℕ) : ℝ)^2 * (C*Z^(N+V+eps)*(1+‖s‖+hv)^(2*degree)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (heightPow_row_le s hv hv0 _)
            (mul_nonneg hC.le hZp)) (by positivity)
      _ = _ := by ring
  · intro lists' hsub hdis
    have hmom := h Z hZ D hD ss ((Finset.card_le_card hss).trans hslots) lists' H a
      hdis (fun i hi => hH i (hss hi))
      (fun i hi Q hQ => hP i (hss hi) Q (hsub i hQ)) (fun i hi Q hQ => ha i (hss hi) Q (hsub i hQ))
      _ hw0 hwle base hb hper
    dsimp only [CompletePoolRankMoments] at hmom
    exact hmom Ψ hΨ m hm N V M Q hN hV hM hQ hG.1 hG.2.1 hG.2.2 hnorm ss (Finset.Subset.refl _)
      labels hlab s

theorem goodEnergyExistsInj_native (Adm : SlotAdm) (Mcap Fcap c eps : ℝ) (hM : 0 ≤ Mcap)
    (hF : 0 ≤ Fcap) (hc : 0 < c) (heps : 0 < eps) (K : ℕ) (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ)
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsW : Function.support (W : ℝ → ℂ) ⊆ Set.Icc lo hi) :
    GoodEnergyExistsInj Adm (nativeGood Mcap Fcap c) eps (Fcap+1) K W :=
  goodEnergyExistsInj_of_canonical Adm
    (canonical_marked_energy_exists Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW)

theorem GoodEnergyExistsInj.mono_good {Adm : SlotAdm} {G G' : StatePred} {eps L : ℝ} {K : ℕ}
    {W : 𝓢(ℝ,ℂ)} (hG : ∀ N V M Q z, G' N V M Q z → G N V M Q z)
    (h : GoodEnergyExistsInj Adm G eps L K W) : GoodEnergyExistsInj Adm G' eps L K W := by
  obtain ⟨B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨degree,C,Z₀,hC,hZ₀,h⟩ := h q hq
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  have hmom := h Z hZ D hD slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  dsimp only [GoodPoolRankMomentsInj] at hmom ⊢
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q)
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hFa i]; infer_instance
  exact goodRankMomentsInj_mono (poolPrimary F) (poolPrimary_ne_zero F hFa)
    (poolPrimary_coprime F hFa) (poolPrimary_good F hFa) hG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hZ₀.le.trans hZ) hv0 hC.le le_rfl le_rfl hmom

theorem GoodEnergyExistsInj.mono_adm {Adm Adm' : SlotAdm} {G : StatePred} {eps L : ℝ} {K : ℕ}
    {W : 𝓢(ℝ,ℂ)}
    (hA : ∀ q D σ [DecidableEq σ] slots lists H a Z hv, Adm' q D σ slots lists H a Z hv →
      Adm q D σ slots lists H a Z hv)
    (h : GoodEnergyExistsInj Adm G eps L K W) : GoodEnergyExistsInj Adm' G eps L K W := by
  obtain ⟨B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨degree,C,Z₀,hC,hZ₀,h⟩ := h q hq
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  exact h Z hZ D hD slots hslots lists H a hH hP ha hv hv0 (hA q D σ slots lists H a Z hv hadm)
    base hb hper

theorem GoodEnergyExistsInj.union {Adm : SlotAdm} {G₁ G₂ : StatePred} {eps L₁ L₂ : ℝ}
    {K : ℕ} {W : 𝓢(ℝ,ℂ)} (h₁ : GoodEnergyExistsInj Adm G₁ eps L₁ K W)
    (h₂ : GoodEnergyExistsInj Adm G₂ eps L₂ K W) :
    GoodEnergyExistsInj Adm (fun N V M Q z => G₁ N V M Q z ∨ G₂ N V M Q z) eps (max L₁ L₂)
      K W := by
  obtain ⟨B₁,hB₁,h₁⟩ := h₁
  obtain ⟨B₂,hB₂,h₂⟩ := h₂
  refine ⟨max B₁ B₂,hB₁.trans (le_max_left _ _),fun q hq => ?_⟩
  obtain ⟨d₁,C₁,Z₁,hC₁,hZ₁,h₁⟩ := h₁ q hq
  obtain ⟨d₂,C₂,Z₂,hC₂,hZ₂,h₂⟩ := h₂ q hq
  refine ⟨max d₁ d₂,C₁+C₂,max Z₁ Z₂,add_pos hC₁ hC₂,lt_max_of_lt_left hZ₁,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  have hZ1 : 1 ≤ Z := hZ₁.le.trans ((le_max_left _ _).trans hZ)
  have hDi (Bi Li : ℝ) (hBi : Bi ≤ max B₁ B₂) (hLi : Li ≤ max L₁ L₂) (hB0 : 0 ≤ Bi) :
      Bi*Z^Li ≤ D := by
    refine le_trans ?_ hD
    exact mul_le_mul hBi (Real.rpow_le_rpow_of_exponent_le hZ1 hLi)
      (Real.rpow_nonneg (zero_le_one.trans hZ1) _) (hB0.trans hBi)
  have m₁ := h₁ Z ((le_max_left _ _).trans hZ) D
    (hDi B₁ L₁ (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hB₁))
    slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  have m₂ := h₂ Z ((le_max_right _ _).trans hZ) D
    (hDi B₂ L₂ (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hB₂))
    slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  dsimp only [GoodPoolRankMomentsInj] at m₁ m₂ ⊢
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q)
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hFa i]; infer_instance
  exact goodRankMomentsInj_union (poolPrimary F) (poolPrimary_ne_zero F hFa)
    (poolPrimary_coprime F hFa) (poolPrimary_good F hFa) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hZ1 hv0 hC₁.le hC₂.le m₁ m₂

theorem GoodEnergyExistsInj.of_withNonneg {Adm : SlotAdm} {G : StatePred} {eps L : ℝ}
    {K : ℕ} {W : 𝓢(ℝ,ℂ)} (h : GoodEnergyExistsInj Adm (withNonneg G) eps L K W) :
    GoodEnergyExistsInj Adm G eps L K W := by
  obtain ⟨B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨degree,C,Z₀,hC,hZ₀,h⟩ := h q hq
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  have hmom := h Z hZ D hD slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  dsimp only [GoodPoolRankMomentsInj] at hmom ⊢
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  exact hmom Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss ⟨hN,hV,hQ,hG⟩ labels hlab s

/-- The `u = 0` branch (few live marks), injective oracle. -/
theorem goodEnergyExistsInj_lowLive (Adm : SlotAdm) (Pmax Smax κ u₀ eps : ℝ) (hκ : 0 ≤ κ)
    (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hgate : Pmax+Smax+u₀+3*κ < 1)
    (hgate₂ : 2*Pmax+2*Smax+6*u₀+5*κ < 3) (heps : 0 < eps) (K : ℕ)
    (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hsW : Function.support (W : ℝ → ℂ) ⊆ Set.Icc lo hi) :
    GoodEnergyExistsInj Adm (withNonneg (LowLive Pmax Smax κ u₀)) eps 3 K W := by
  have hc : 0 < lowReserve Pmax Smax κ u₀ :=
    lt_min (by linarith) (by linarith)
  have h := goodEnergyExistsInj_native Adm 2 2 _ eps (by norm_num) (by norm_num) hc heps K W lo
    hi hlo hhi hsW
  rw [show (2:ℝ)+1 = 3 by norm_num] at h
  refine h.mono_good ?_
  rintro N V M Q z ⟨_,_,hQ,hl⟩
  exact lowLive_native Pmax Smax κ u₀ hκ hP hS hgate N V M Q z hQ hl

/-! ## The injective oracle per slot class -/

/-- `OracleOn'` with the injective oracle. -/
def OracleOnInj' (Adm : ℝ → SlotClass → SlotAdm) (fam : SlotClass → Prop) (Good : StatePred) :
    Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ mesh : ℝ, 0 < mesh ∧
    ∀ cls : SlotClass, fam cls →
    ∀ (K : ℕ) (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ), 0 < lo → lo ≤ hi →
      Function.support (W : ℝ → ℂ) ⊆ Icc lo hi →
      GoodEnergyExistsInj (Adm mesh cls) Good eps 3 K W

theorem OracleOnInj'.mono_good {Adm : ℝ → SlotClass → SlotAdm} {fam : SlotClass → Prop}
    {G G' : StatePred} (hG : ∀ N V M Q z, G' N V M Q z → G N V M Q z)
    (h : OracleOnInj' Adm fam G) : OracleOnInj' Adm fam G' := by
  intro eps heps
  obtain ⟨mesh,hmesh,h⟩ := h eps heps
  exact ⟨mesh,hmesh,fun cls hcls K W lo hi hlo hlh hs =>
    (h cls hcls K W lo hi hlo hlh hs).mono_good hG⟩

theorem oracleOnInj'_lowLive (Adm : ℝ → SlotClass → SlotAdm) (fam : SlotClass → Prop)
    (Pmax Smax κ u : ℝ) (hκ : 0 ≤ κ)
    (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hgate₁ : Pmax+Smax+u+3*κ < 1)
    (hgate₂ : 2*Pmax+2*Smax+6*u+5*κ < 3) :
    OracleOnInj' Adm fam (LowLive Pmax Smax κ u) := by
  intro eps heps
  refine ⟨1,one_pos,fun cls _ K W lo hi hlo hlh hs => ?_⟩
  exact GoodEnergyExistsInj.of_withNonneg
    (goodEnergyExistsInj_lowLive (Adm 1 cls) Pmax Smax κ u eps hκ hP hS hgate₁ hgate₂ heps K W
      lo hi hlo (hlo.le.trans hlh) hs)

theorem oracleOnInj'_initState (Adm : ℝ → SlotClass → SlotAdm) (fam : SlotClass → Prop)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ cls q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' cls q D σ slots lists H a Z hv → Adm mesh cls q D σ slots lists H a Z hv)
    (Pmax Smax κ u : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax)
    (hgate₁ : Pmax+Smax+u+3*κ < 1) (hgate₂ : 2*Pmax+2*Smax+6*u+5*κ < 3)
    (hhigh : OracleOnInj' Adm fam (HighLive Pmax Smax κ u)) :
    OracleOnInj' Adm fam (InitState Pmax Smax κ) := by
  intro eps heps
  obtain ⟨mesh,hmesh,hh⟩ := hhigh eps heps
  obtain ⟨mesh₁,hmesh₁,hl⟩ :=
    oracleOnInj'_lowLive Adm fam Pmax Smax κ u hκ hP hS hgate₁ hgate₂ eps heps
  refine ⟨min mesh mesh₁,lt_min hmesh hmesh₁,fun cls hcls K W lo hi hlo hlh hs => ?_⟩
  have h₁' := (hl cls hcls K W lo hi hlo hlh hs).mono_adm (Adm' := Adm (min mesh mesh₁) cls)
    (fun q D σ _ slots lists H a Z hv h =>
      hAdm mesh₁ _ (min_le_right _ _) cls q D σ slots lists H a Z hv h)
  have h₂' := (hh cls hcls K W lo hi hlo hlh hs).mono_adm (Adm' := Adm (min mesh mesh₁) cls)
    (fun q D σ _ slots lists H a Z hv h =>
      hAdm mesh _ (min_le_left _ _) cls q D σ slots lists H a Z hv h)
  have hu := h₁'.union h₂'
  rw [max_self] at hu
  refine hu.mono_good ?_
  intro N V M Q z hI
  exact initState_split Pmax Smax κ u N V M Q z hI

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.normalizedColumnEnergyInj_le
#print axioms Qrh.MarkedAnchor.Inverse.Inj.goodEnergyExistsInj_lowLive
#print axioms Qrh.MarkedAnchor.Inverse.Inj.oracleOnInj'_initState
