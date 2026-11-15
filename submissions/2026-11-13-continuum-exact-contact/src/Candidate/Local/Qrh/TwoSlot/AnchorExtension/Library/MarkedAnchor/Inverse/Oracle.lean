/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistence
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.InitGeometry

/-!
# Inverse.Oracle

The canonical-energy oracle. The baseline's `CanonicalEnergyExists`
(Descent/CanonicalEnergyExistenceData.lean) bounds the canonical energy of every state
`(N,V,M,Q,z)` satisfying the native `CanonicalMargins`, with `∃degree B, ∀q≠0, ∃C Z₀, ∀Z≥Z₀,
∀D≥B Z^L, ∀slots …`. Here
* the margins are replaced by an arbitrary state predicate `Good`;
* the state predicate is evaluated at the ACTUAL width `logb Z (∏_{subslots} H)` of the slot
  subcollection whose energy is bounded (the baseline allows any subcollection at the width of
  all slots, which is harmless natively but not for anchor rectangles);
* an admissibility filter `Adm` on the canonical slot data is added (slot class and mesh of the
  physical parent through the dictionary; `allAdm` is the native case).

* `GoodRankMoments`, `GoodPoolRankMoments`, `GoodEnergyExists` (the oracle).
* `goodEnergyExists_of_canonical`, `goodEnergyExists_native`: the native oracle (baseline
  `canonical_marked_energy_exists`, applied to the subcollection itself).
* `GoodEnergyExists.mono_good/.mono_adm/.union`.
* `InitState Pmax Smax κ`, `LowLive`, `HighLive`, `lowLive_native`, `goodEnergyExists_lowLive`
  (the `u = 0` branch: live width `≤ u₀` is native as soon as `Pmax+Smax+u₀+3κ < 1` and
  `2Pmax+2Smax+6u₀+5κ < 3`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths OAI.SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
open CanonicalCoefficientClass FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

/-- A geometry predicate on canonical states `(N, V, M, Q, w)`, `w` the live slot width. -/
abbrev StatePred : Type := ℝ → ℝ → ℝ → ℝ → ℝ → Prop

/-- The native states: caps and `CanonicalMargins`. -/
def nativeGood (Mcap Fcap c : ℝ) : StatePred := fun N V M Q z =>
  M ≤ Mcap ∧ N+V ≤ Fcap ∧ CanonicalMargins (N+V) M Q z c

/-! ## Height factors

The oracle bound is height-aware: `A Z^(N+V+eps) (1+‖s‖+hv)^(2 degree)`, `hv ≥ 0` the slot-height
bound of the admitted slot data. Native (height-free) bounds embed by
`heightPow_row_le`; consumers split the factor by `heightPow_split`. -/

theorem heightPow_row_le (s hv : ℝ) (hv0 : 0 ≤ hv) (n : ℕ) :
    (1+‖s‖)^n ≤ (1+‖s‖+hv)^n :=
  pow_le_pow_left₀ (by positivity) (by linarith) n

theorem heightPow_split (s hv : ℝ) (hv0 : 0 ≤ hv) (n : ℕ) :
    (1+‖s‖+hv)^n ≤ (1+hv)^n*(1+‖s‖)^n := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by nlinarith [norm_nonneg s]) n

theorem hvPow_mono {hv : ℝ} (hv0 : 0 ≤ hv) {a b : ℕ} (h : a ≤ b) : (1+hv)^a ≤ (1+hv)^b :=
  pow_le_pow_right₀ (by linarith) h

theorem one_le_hvPow {hv : ℝ} (hv0 : 0 ≤ hv) (n : ℕ) : 1 ≤ (1+hv)^n :=
  one_le_pow₀ (by linarith)

/-- Raising the height exponent of a bound `C (1+hv)^a Y X`. -/
theorem hvFactor_mono {C hv Y X : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y) (hX : 0 ≤ X) (hv0 : 0 ≤ hv)
    {a b : ℕ} (h : a ≤ b) : C*(1+hv)^a*Y*X ≤ C*(1+hv)^b*Y*X := by
  have := hvPow_mono hv0 h
  have h0 : 0 ≤ (1+hv)^a := by positivity
  gcongr

section Rank
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
variable (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
variable (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- `CanonicalRankMoments` with the native margins and caps replaced by `Good`, evaluated at the
actual width `logb Z (∏_{subslots} H)` of the subcollection. Height-aware: the bound
carries `(1+‖s‖+hv)^(2 degree)`, `hv` the slot-height bound of the admitted data. -/
def GoodRankMoments (Good : StatePred) (pool : Finset ι) (base : O →* ℂ) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : σ → ℝ) (W : 𝓢(ℝ,ℂ)) (Z eps A hv : ℝ)
    (K degree : ℕ) : Prop :=
  ∀ (Ψ : O →* ℂ), IsBaseRayTwist base Ψ → ∀ (m : O), m ≠ 0 → ∀ N V M Qwidth : ℝ,
    0 ≤ N → 0 ≤ V → 0 ≤ M → 0 ≤ Qwidth →
    ‖ConcreteTraceCRT.eisEmbedding m‖^2 = Z^Qwidth →
    ∀ (subslots : Finset σ), subslots ⊆ slots →
      Good N V M Qwidth (Real.logb Z (∏ i ∈ subslots, H i)) →
    ∀ labels : Finset (Ideal O),
      (∀ I ∈ labels, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Z^V) → ∀ s : ℝ,
    normalizedColumnEnergy p hp hcop hg pool Ψ m subslots lists a labels
      (nonzeroChildFrequencyBall 1 (Z^M)) (secondLabelWeight K) (childLogTest W s) (Z^N) Z
        (N+V) ≤
      A*Z^(N+V+eps)*(1+‖s‖+hv)^(2*degree)

omit [DecidableEq σ] in
theorem goodRankMoments_mono {G G' : StatePred} (hG : ∀ N V M Q z, G' N V M Q z → G N V M Q z)
    (pool : Finset ι) (base : O →* ℂ) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (H : σ → ℝ) (W : 𝓢(ℝ,ℂ)) (Z eps A A' hv : ℝ) (K degree degree' : ℕ)
    (hZ : 1 ≤ Z) (hv0 : 0 ≤ hv) (hA0 : 0 ≤ A) (hA : A ≤ A') (hd : degree ≤ degree')
    (h : GoodRankMoments p hp hcop hg G pool base slots lists a H W Z eps A hv K degree) :
    GoodRankMoments p hp hcop hg G' pool base slots lists a H W Z eps A' hv K degree' := by
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG' labels hlab s
  refine (h Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss (hG _ _ _ _ _ hG') labels hlab s).trans ?_
  have hZp : 0 ≤ Z^(N+V+eps) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  have hs1 : (1:ℝ) ≤ 1+‖s‖+hv := by linarith [norm_nonneg s]
  have hpow : (1+‖s‖+hv)^(2*degree) ≤ (1+‖s‖+hv)^(2*degree') :=
    pow_le_pow_right₀ hs1 (by omega)
  have hp0 : 0 ≤ (1+‖s‖+hv)^(2*degree) := by positivity
  calc A*Z^(N+V+eps)*(1+‖s‖+hv)^(2*degree) ≤ A'*Z^(N+V+eps)*(1+‖s‖+hv)^(2*degree') := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hA hZp) hpow hp0
        exact mul_nonneg (hA0.trans hA) hZp

omit [DecidableEq σ] in
theorem goodRankMoments_union {G₁ G₂ : StatePred}
    (pool : Finset ι) (base : O →* ℂ) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (H : σ → ℝ) (W : 𝓢(ℝ,ℂ)) (Z eps A₁ A₂ hv : ℝ) (K d₁ d₂ : ℕ)
    (hZ : 1 ≤ Z) (hv0 : 0 ≤ hv) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (h₁ : GoodRankMoments p hp hcop hg G₁ pool base slots lists a H W Z eps A₁ hv K d₁)
    (h₂ : GoodRankMoments p hp hcop hg G₂ pool base slots lists a H W Z eps A₂ hv K d₂) :
    GoodRankMoments p hp hcop hg (fun N V M Q z => G₁ N V M Q z ∨ G₂ N V M Q z) pool base
      slots lists a H W Z eps (A₁+A₂) hv K (max d₁ d₂) := by
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  rcases hG with hG | hG
  · exact goodRankMoments_mono p hp hcop hg (G := G₁) (G' := G₁) (fun _ _ _ _ _ h => h) pool
      base slots lists a H W Z eps A₁ (A₁+A₂) hv K d₁ (max d₁ d₂) hZ hv0 hA₁ (by linarith)
      (le_max_left _ _) h₁ Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  · exact goodRankMoments_mono p hp hcop hg (G := G₂) (G' := G₂) (fun _ _ _ _ _ h => h) pool
      base slots lists a H W Z eps A₂ (A₁+A₂) hv K d₂ (max d₁ d₂) hZ hv0 hA₂ (by linarith)
      (le_max_right _ _) h₂ Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s

end Rank

/-- The canonical pool index type at modulus `q` and pool bound `D`. -/
abbrev PoolIdx (q D : ℕ) : Type :=
  primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)

/-- `GoodRankMoments` on the complete outside-squarefree pool (as `CompletePoolRankMoments`). -/
def GoodPoolRankMoments (q D : ℕ) {σ : Type} [DecidableEq σ] (Good : StatePred)
    (slots : Finset σ) (lists : σ → Finset (PoolIdx q D)) (a : σ → PoolIdx q D → ℂ)
    (H : σ → ℝ) (base : O →* ℂ) (W : 𝓢(ℝ,ℂ)) (Z eps A hv : ℝ) (K degree : ℕ) : Prop :=
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D;
  let hF := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q);
  letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance;
  GoodRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Good Finset.univ base slots lists a H W Z eps A hv K degree

/-- Admissibility filter on canonical slot data `(slots, lists, H, a)` at scale `Z` and slot
height bound `hv` (last argument). -/
abbrev SlotAdm : Type 1 :=
  (q D : ℕ) → (σ : Type) → [DecidableEq σ] → Finset σ → (σ → Finset (PoolIdx q D)) →
    (σ → ℝ) → (σ → PoolIdx q D → ℂ) → ℝ → ℝ → Prop

/-- The trivial filter (native; ignores the height). -/
def allAdm : SlotAdm := fun _ _ _ _ _ _ _ _ _ _ => True

/-- The canonical-energy oracle on the states `Good` (at actual subcollection widths), for
slot data passing `Adm`. Quantifier order: `∃ B ≥ 1, ∀ q ≠ 0, ∃ degree C Z₀`
(the degree may depend on the modulus `q`, which is fixed by the parent datum); the baseline
`CanonicalEnergyExists` (`∃ degree B ∀ q`) implies it. Height-aware: the slot height
bound `hv ≥ 0` is chosen with the slot data (after `Z`, `degree`, `C`), the filter sees it, and
the bound pays `(1+‖s‖+hv)^(2 degree)`. -/
def GoodEnergyExists (Adm : SlotAdm) (Good : StatePred) (eps L : ℝ) (K : ℕ) (W : 𝓢(ℝ,ℂ)) :
    Prop :=
  ∃ B : ℝ, 1 ≤ B ∧
    ∀ q : ℕ, q ≠ 0 → ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → ∀ D : ℕ, B*Z^L ≤ D →
    ∀ {σ : Type} [DecidableEq σ] (slots : Finset σ), slots.card ≤ K →
    ∀ (lists : σ → Finset (PoolIdx q D)) (H : σ → ℝ) (a : σ → PoolIdx q D → ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i ∈ slots, 1 ≤ H i) → (∀ i ∈ slots, ∀ P ∈ lists i, (Ideal.absNorm P.val : ℝ) ≤ H i) →
      (∀ i ∈ slots, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) →
    ∀ hv : ℝ, 0 ≤ hv → Adm q D σ slots lists H a Z hv →
    ∀ base : O →* ℂ, (∀ u, ‖base u‖ ≤ 1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q)
        base →
      GoodPoolRankMoments q D Good slots lists a H base W Z eps C hv K degree

theorem one_le_prod_of_one_le {σ : Type} (s : Finset σ) (H : σ → ℝ) (hH : ∀ i ∈ s, 1 ≤ H i) :
    1 ≤ ∏ i ∈ s, H i := by
  have h : (∏ _i ∈ s, (1:ℝ)) ≤ ∏ i ∈ s, H i := by
    gcongr with i hi
    exact hH i hi
  simpa using h

/-- The native oracle at actual widths: the baseline existence applied to the subcollection. -/
theorem goodEnergyExists_of_canonical (Adm : SlotAdm) {Mcap Fcap c eps L : ℝ}
    {K : ℕ} {W : 𝓢(ℝ,ℂ)} (h : CanonicalEnergyExists Mcap Fcap c eps L K W) :
    GoodEnergyExists Adm (nativeGood Mcap Fcap c) eps L K W := by
  obtain ⟨degree,B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨C,Z₀,hC,hZ₀,h⟩ := h q hq
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha hv hv0 _ base hb hper
  have hZ1 : 1 < Z := hZ₀.trans_le hZ
  dsimp only [GoodPoolRankMoments]
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
  have hmom := h Z hZ D hD ss ((Finset.card_le_card hss).trans hslots) lists H a
    (hdis.subset (Finset.coe_subset.mpr hss)) (fun i hi => hH i (hss hi))
    (fun i hi => hP i (hss hi)) (fun i hi => ha i (hss hi)) _ hw0 hwle base hb hper
  dsimp only [CompletePoolRankMoments] at hmom
  refine (hmom Ψ hΨ m hm N V M Q hN hV hM hQ hG.1 hG.2.1 hG.2.2 hnorm ss (Finset.Subset.refl _)
    labels hlab s).trans ?_
  have hZp : 0 ≤ Z^(N+V+eps) := Real.rpow_nonneg (zero_lt_one.trans hZ1).le _
  exact mul_le_mul_of_nonneg_left (heightPow_row_le s hv hv0 _) (mul_nonneg hC.le hZp)

/-- The native oracle (baseline `canonical_marked_energy_exists`). -/
theorem goodEnergyExists_native (Adm : SlotAdm) (Mcap Fcap c eps : ℝ) (hM : 0 ≤ Mcap)
    (hF : 0 ≤ Fcap) (hc : 0 < c) (heps : 0 < eps) (K : ℕ) (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ)
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hsW : Function.support (W : ℝ → ℂ) ⊆ Set.Icc lo hi) :
    GoodEnergyExists Adm (nativeGood Mcap Fcap c) eps (Fcap+1) K W :=
  goodEnergyExists_of_canonical Adm
    (canonical_marked_energy_exists Mcap Fcap c eps hM hF hc heps K W lo hi hlo hhi hsW)

theorem GoodEnergyExists.mono_good {Adm : SlotAdm} {G G' : StatePred} {eps L : ℝ} {K : ℕ}
    {W : 𝓢(ℝ,ℂ)} (hG : ∀ N V M Q z, G' N V M Q z → G N V M Q z)
    (h : GoodEnergyExists Adm G eps L K W) : GoodEnergyExists Adm G' eps L K W := by
  obtain ⟨B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨degree,C,Z₀,hC,hZ₀,h⟩ := h q hq
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  have hmom := h Z hZ D hD slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  dsimp only [GoodPoolRankMoments] at hmom ⊢
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q)
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hFa i]; infer_instance
  exact goodRankMoments_mono (poolPrimary F) (poolPrimary_ne_zero F hFa)
    (poolPrimary_coprime F hFa) (poolPrimary_good F hFa) hG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hZ₀.le.trans hZ) hv0 hC.le le_rfl le_rfl hmom

theorem GoodEnergyExists.mono_adm {Adm Adm' : SlotAdm} {G : StatePred} {eps L : ℝ} {K : ℕ}
    {W : 𝓢(ℝ,ℂ)}
    (hA : ∀ q D σ [DecidableEq σ] slots lists H a Z hv, Adm' q D σ slots lists H a Z hv →
      Adm q D σ slots lists H a Z hv)
    (h : GoodEnergyExists Adm G eps L K W) : GoodEnergyExists Adm' G eps L K W := by
  obtain ⟨B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨degree,C,Z₀,hC,hZ₀,h⟩ := h q hq
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  exact h Z hZ D hD slots hslots lists H a hdis hH hP ha hv hv0
    (hA q D σ slots lists H a Z hv hadm) base hb hper

/-- Gluing two oracles: the union of the state sets, with the larger pool exponent. -/
theorem GoodEnergyExists.union {Adm : SlotAdm} {G₁ G₂ : StatePred} {eps L₁ L₂ : ℝ}
    {K : ℕ} {W : 𝓢(ℝ,ℂ)} (h₁ : GoodEnergyExists Adm G₁ eps L₁ K W)
    (h₂ : GoodEnergyExists Adm G₂ eps L₂ K W) :
    GoodEnergyExists Adm (fun N V M Q z => G₁ N V M Q z ∨ G₂ N V M Q z) eps (max L₁ L₂)
      K W := by
  obtain ⟨B₁,hB₁,h₁⟩ := h₁
  obtain ⟨B₂,hB₂,h₂⟩ := h₂
  refine ⟨max B₁ B₂,hB₁.trans (le_max_left _ _),fun q hq => ?_⟩
  obtain ⟨d₁,C₁,Z₁,hC₁,hZ₁,h₁⟩ := h₁ q hq
  obtain ⟨d₂,C₂,Z₂,hC₂,hZ₂,h₂⟩ := h₂ q hq
  refine ⟨max d₁ d₂,C₁+C₂,max Z₁ Z₂,add_pos hC₁ hC₂,lt_max_of_lt_left hZ₁,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  have hZ1 : 1 ≤ Z := hZ₁.le.trans ((le_max_left _ _).trans hZ)
  have hDi (Bi Li : ℝ) (hBi : Bi ≤ max B₁ B₂) (hLi : Li ≤ max L₁ L₂) (hB0 : 0 ≤ Bi) :
      Bi*Z^Li ≤ D := by
    refine le_trans ?_ hD
    exact mul_le_mul hBi (Real.rpow_le_rpow_of_exponent_le hZ1 hLi)
      (Real.rpow_nonneg (zero_le_one.trans hZ1) _) (hB0.trans hBi)
  have m₁ := h₁ Z ((le_max_left _ _).trans hZ) D
    (hDi B₁ L₁ (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hB₁))
    slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  have m₂ := h₂ Z ((le_max_right _ _).trans hZ) D
    (hDi B₂ L₂ (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hB₂))
    slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  dsimp only [GoodPoolRankMoments] at m₁ m₂ ⊢
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q)
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hFa i]; infer_instance
  exact goodRankMoments_union (poolPrimary F) (poolPrimary_ne_zero F hFa)
    (poolPrimary_coprime F hFa) (poolPrimary_good F hFa) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hZ1 hv0 hC₁.le hC₂.le m₁ m₂

/-! ## Initial states of a parent rectangle and the `u = 0` branch -/

/-- The initial canonical states of a parent with free width `≤ Pmax` and mark width `≤ Smax`
(radius `1`), with slack `κ`, at live width `w` of the marked subcollection (see
`InitGeometry`):
`0 ≤ w ≤ Smax+κ`, residual free width `N - w ≤ Pmax+κ`, `F + Q ≤ Pmax+Smax+κ` (`F = N+V`),
Gauss row `M ≤ 2F - 1 + κ`. -/
def InitState (Pmax Smax κ : ℝ) : StatePred := fun N V M Q z =>
  0 ≤ z ∧ z ≤ Smax+κ ∧ N - z ≤ Pmax+κ ∧ N+V+Q ≤ Pmax+Smax+κ ∧ M ≤ 2*(N+V)-1+κ

/-- Initial states with few live marks (`w ≤ u₀`): the `u = 0` branch. -/
def LowLive (Pmax Smax κ u₀ : ℝ) : StatePred := fun N V M Q z =>
  InitState Pmax Smax κ N V M Q z ∧ z ≤ u₀

/-- Initial states with enough live marks for a selection of width `u₀`. -/
def HighLive (Pmax Smax κ u₀ : ℝ) : StatePred := fun N V M Q z =>
  InitState Pmax Smax κ N V M Q z ∧ u₀ ≤ z

theorem initState_split (Pmax Smax κ u₀ : ℝ) (N V M Q z : ℝ)
    (h : InitState Pmax Smax κ N V M Q z) :
    LowLive Pmax Smax κ u₀ N V M Q z ∨ HighLive Pmax Smax κ u₀ N V M Q z := by
  rcases le_total z u₀ with hz | hz
  · exact Or.inl ⟨h,hz⟩
  · exact Or.inr ⟨h,hz⟩

/-- The reserve of the native `u = 0` branch. -/
def lowReserve (Pmax Smax κ u₀ : ℝ) : ℝ :=
  min (1-Pmax-Smax-u₀-2*κ) (3-2*Pmax-2*Smax-6*u₀-5*κ)

/-- Few live marks are native: `LowLive ⊆ nativeGood 2 2 (lowReserve …)`. -/
theorem lowLive_native (Pmax Smax κ u₀ : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax)
    (hgate : Pmax+Smax+u₀+3*κ < 1) (N V M Q z : ℝ) (hQ : 0 ≤ Q)
    (h : LowLive Pmax Smax κ u₀ N V M Q z) :
    nativeGood 2 2 (lowReserve Pmax Smax κ u₀) N V M Q z := by
  obtain ⟨⟨hz0,_,_,hFQ,hM⟩,hz⟩ := h
  have hm1 := min_le_left (1-Pmax-Smax-u₀-2*κ) (3-2*Pmax-2*Smax-6*u₀-5*κ)
  have hm2 := min_le_right (1-Pmax-Smax-u₀-2*κ) (3-2*Pmax-2*Smax-6*u₀-5*κ)
  unfold nativeGood CanonicalMargins lowReserve
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The `u = 0` branch of the selection: the oracle on `LowLive` states, from the native
theorem. -/
theorem goodEnergyExists_lowLive (Adm : SlotAdm) (Pmax Smax κ u₀ eps : ℝ) (hκ : 0 ≤ κ)
    (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hgate : Pmax+Smax+u₀+3*κ < 1)
    (hgate₂ : 2*Pmax+2*Smax+6*u₀+5*κ < 3) (heps : 0 < eps) (K : ℕ)
    (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hsW : Function.support (W : ℝ → ℂ) ⊆ Set.Icc lo hi) :
    GoodEnergyExists Adm (fun N V M Q z => 0 ≤ N ∧ 0 ≤ V ∧ 0 ≤ Q ∧
      LowLive Pmax Smax κ u₀ N V M Q z) eps 3 K W := by
  have hc : 0 < lowReserve Pmax Smax κ u₀ :=
    lt_min (by linarith) (by linarith)
  have h := goodEnergyExists_native Adm 2 2 _ eps (by norm_num) (by norm_num) hc heps K W lo hi
    hlo hhi hsW
  rw [show (2:ℝ)+1 = 3 by norm_num] at h
  refine h.mono_good ?_
  rintro N V M Q z ⟨_,_,hQ,hl⟩
  exact lowLive_native Pmax Smax κ u₀ hκ hP hS hgate N V M Q z hQ hl

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.goodEnergyExists_native
#print axioms Qrh.MarkedAnchor.Inverse.GoodEnergyExists.union
#print axioms Qrh.MarkedAnchor.Inverse.goodEnergyExists_lowLive
