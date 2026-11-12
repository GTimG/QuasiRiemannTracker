/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Select.Scale
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.AdmDef
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Reduction
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Step
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.InjMark
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Oracle

/-!
# Inverse.Select.Assembly — the selection reduction for the canonical classes

* Quantifier order `∀ K, ∀ q ≠ 0, ∃ dchild C Z₀` (the child degree may depend on the modulus `q`
  of the parent datum); the restored child is `ChildBoundInj` (injective marks, pools may
  overlap, no `PairwiseDisjoint` hypothesis on the datum). The selection (`selection_at_scale`)
  and the Poisson step run with the injective mark, so the child `ChildBoundInj` is consumed
  directly. The separated forms (`selectionReductionExcess'_of` …) use the oracle's
  `PairwiseDisjoint lists` only to identify the oracle's full-mark energy with the injective one
  (`columnEnergyInj_eq`).
* `RestoreChildAt`, `RestoreChildBound`: the restoration statement, with the parent class `cls`
  (`canonicalSlotsRay W (33/50) rayM G hH` for the canonical family) as a parameter fixed in
  front, `∀ ε ∃ mesh ∀ K ∀ q≠0 ∃ dchild C Z₀ ∀ Z ≥ Z₀ ∀ datum`, filter `imageAdm' mesh cls`,
  `∀ base Ψ (IsBaseRayTwist) m≠0 R ⊆ slots`, widths via `logb Z (∏_{slots\R} H)`,
  `Hc' ∈ [Hlo, 2]`, conclusion
  `ChildBoundInj … (slots\R) … Φs dchild Z Xmax (2 bo Xmax) Hc' (C (1+hv)^(2 dchild) Z^(Hc'(1+x)+ε))`.
* `RestoreChildBoundUniform famP famC`: the hypothesis consumed here — from the child source
  `UniformInverseRectSourceExcess famC ρc x`, the restoration holds with ONE mesh for all parent
  classes `cls ∈ famP` and all child profile families `Φs` (the order `∀ ε ∃ mesh ∀ cls Φs`
  instead of `∀ cls Φs ∀ ε ∃ mesh`). This is forced by the oracle: `OracleOn'` fixes the mesh before the column
  profile, and the Poisson family `Φs` depends on the column profile. The restoration's mesh is the
  child source's mesh, which is uniform (`InverseRectSource` has `∃ mesh` before `∀ cls Φ`).
  `RestoreChildBoundUniform.restoreChildBound` recovers the per-`(cls, Φs)` form.
* **`selectionReductionExcessInj_of`**: for ANY families `famP famC`, `PoissonStepStatement` and
  `RestoreChildBoundUniform famP famC` give `Inj.SelectionReductionExcess famP famC imageAdm'`;
  `selectionReductionExcessInj_canonical` is the instance `famP = famC = canonicalFamily` with
  `Poisson.poissonStepStatement`, taking `RestoreChildBoundUniform` as hypothesis (supplied by
  `Restore.restoreChildBoundUniform_canonical`).
* `selectionReductionExcess'_of`, `selectionReductionExcess'_of_restore`,
  `selectionReductionExcess'_canonical`: the same for the separated oracle
  (`SelectionReductionExcess'`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Filter
open OAI OAI.SevenEighths OAI.SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open CanonicalRowCompletion InverseInitialClippedColumns InverseReflectedPhase
open CanonicalCoefficientClass FirstPassCubeLabels SecondPassArithmetic
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => OAI.ActualEisensteinCubic.O

/-- The datum-level restored child bound at one scale. The
parent slot height `hv ≥ 0` of the `imageAdm'` witness is quantified after the datum (after `Z`,
never before `∃ dchild C Z₀`), and the bound pays `(1+hv)^(2 dchild)` (the restored child heights
are `≤ hv + |t| + |τ|`; the `t`, `τ` powers are absorbed in `C` by the Schwartz weights). -/
def RestoreChildAt (ρc : AnchorRect) (x Hlo : ℝ) (cls : SlotClass) {J : ℕ} (Φs : Fin J → ℝ → ℂ)
    (bo mesh : ℝ) (K dchild q : ℕ) (C Z ε : ℝ) : Prop :=
  ∀ (D : ℕ), Z^3 ≤ (D : ℝ) →
  ∀ {σ : Type} [DecidableEq σ] (slots : Finset σ) (lists : σ → Finset (PoolIdx q D))
    (H : σ → ℝ) (a : σ → PoolIdx q D → ℂ), slots.card ≤ K →
    (∀ i ∈ slots, 1 ≤ H i) → (∀ i ∈ slots, ∀ P ∈ lists i, (Ideal.absNorm P.val : ℝ) ≤ H i) →
    (∀ i ∈ slots, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) →
    ∀ hv : ℝ, 0 ≤ hv → imageAdm' mesh cls q D σ slots lists H a Z hv →
    ∀ base : O →* ℂ, (∀ u, ‖base u‖ ≤ 1) →
      FactorsModulo (fixedBaseConductor q) base →
    ∀ Ψ : O →* ℂ, IsBaseRayTwist base Ψ → ∀ m : O, m ≠ 0 →
      ‖ConcreteTraceCRT.eisEmbedding m‖^2 ≤ Z^2 →
    ∀ R ⊆ slots, ∀ Xmax Hc' : ℝ, 0 < Xmax → Xmax ≤ Z^2 → Hlo ≤ Hc' → Hc' ≤ 2 →
      Real.logb Z Xmax - Real.logb Z (∏ i ∈ slots \ R, H i) ≤ ρc.Pmax * Hc' →
      Real.logb Z (∏ i ∈ slots \ R, H i) ≤ ρc.Smax * Hc' →
      (let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D;
       let hF := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
         (reflectionExcludedPrimes_bad q);
       letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
         fun i => by rw [poolPrimary_span F hF i]; infer_instance;
       ChildBoundInj (poolPrimary F) (poolPrimary_good F hF) Finset.univ Ψ m (slots \ R)
         lists a Φs dchild Z Xmax (2*bo*Xmax) Hc' (C * (1+hv)^(2*dchild) * Z^(Hc'*(1+x)+ε)))

/-- The restoration statement per parent class `cls` (its slot bump `W`) and profile family
`Φs`, with the fixed range `Hc' ∈ [Hlo, 2]`. -/
def RestoreChildBound (ρc : AnchorRect) (x Hlo : ℝ) (cls : SlotClass) {J : ℕ}
    (Φs : Fin J → ℝ → ℂ) (bo : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧ ∀ K : ℕ, ∀ q : ℕ, q ≠ 0 →
    ∃ (dchild : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      RestoreChildAt ρc x Hlo cls Φs bo mesh K dchild q C Z ε

/-- The restoration hypothesis consumed by the assembly: from the child source, ONE mesh for all
slot bumps and all (smooth, compactly supported away from `0`) child profile families. -/
def RestoreChildBoundUniform (famP famC : SlotClass → Prop) : Prop :=
  ∀ (ρc : AnchorRect) (x Hlo : ℝ), 0 ≤ x → 0 < Hlo →
    Leaf.UniformInverseRectSourceExcess famC ρc x →
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
  ∀ cls : SlotClass, famP cls →
  ∀ (J : ℕ) (Φs : Fin J → ℝ → ℂ) (a' b' : ℝ), 0 < a' → a' ≤ b' →
    (∀ j, ContDiff ℝ ∞ (Φs j) ∧ Function.support (Φs j) ⊆ Set.Icc a' b') →
  ∀ bo : ℝ, 0 < bo →
  ∀ K : ℕ, ∀ q : ℕ, q ≠ 0 →
    ∃ (dchild : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      RestoreChildAt ρc x Hlo cls Φs bo mesh K dchild q C Z ε

/-- The uniform form implies the per-`(cls, Φs)` form `RestoreChildBound`. -/
theorem RestoreChildBoundUniform.restoreChildBound {famP famC : SlotClass → Prop}
    (h : RestoreChildBoundUniform famP famC) {ρc : AnchorRect} {x Hlo : ℝ} (hx : 0 ≤ x)
    (hHlo : 0 < Hlo) (hchild : Leaf.UniformInverseRectSourceExcess famC ρc x)
    (cls : SlotClass) (hcls : famP cls) {J : ℕ} (Φs : Fin J → ℝ → ℂ) (a' b' : ℝ) (ha' : 0 < a') (hab : a' ≤ b')
    (hΦs : ∀ j, ContDiff ℝ ∞ (Φs j) ∧ Function.support (Φs j) ⊆ Set.Icc a' b')
    (bo : ℝ) (hbo : 0 < bo) :
    RestoreChildBound ρc x Hlo cls Φs bo := by
  intro ε hε
  obtain ⟨mesh, hmesh, hm⟩ := h ρc x Hlo hx hHlo hchild ε hε
  exact ⟨mesh, hmesh, hm cls hcls J Φs a' b' ha' hab hΦs bo hbo⟩

/-- Multiplying the restoration constant by `X ≥ 1` multiplies `selConst` by at most `X`. -/
theorem selConst_mul_le (Ib CP CR Cd boΦ X : ℝ) (K : ℕ) (hCP : 0 ≤ CP) (hCd : 0 ≤ Cd)
    (hbo : 0 ≤ boΦ) (hX : 1 ≤ X) :
    selConst Ib CP (CR*X) Cd boΦ K ≤ selConst Ib CP CR Cd boΦ K * X := by
  unfold selConst
  have hc : 0 ≤ 128^2*(1+boΦ)*Cd^(2*K) := by positivity
  have hP : 0 ≤ Ib^2 * 128^K * (K:ℝ)^K * Cd^(10+4*K) * CP := by positivity
  have h : CR*X + 128^2*(1+boΦ)*Cd^(2*K) ≤ (CR + 128^2*(1+boΦ)*Cd^(2*K)) * X := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hX)]
  calc Ib^2 * 128^K * (K:ℝ)^K * Cd^(10+4*K) * CP * (CR*X + 128^2*(1+boΦ)*Cd^(2*K))
      ≤ Ib^2 * 128^K * (K:ℝ)^K * Cd^(10+4*K) * CP * ((CR + 128^2*(1+boΦ)*Cd^(2*K)) * X) :=
        mul_le_mul_of_nonneg_left h hP
    _ = _ := by ring

/-- The exponent excess is below `eps` for the parameter choice of the assembly. -/
theorem selExcess_le (x mesh κP εP εR η eps : ℝ) (K : ℕ)
    (hmesh : mesh * (5 + 30*x) ≤ eps/4) (hκP : κP * (1+x) ≤ eps/4)
    (hεP : εP ≤ eps/8) (hεR : εR ≤ eps/4) (hη : (10+6*(K:ℝ))*η ≤ eps/8) :
    selExcess x mesh κP εP εR η K ≤ eps := by
  unfold selExcess
  push_cast
  have e1 : x*(30*mesh+κP) = 30*(mesh*x) + κP*x := by ring
  have e2 : mesh*(5+30*x) = 5*mesh + 30*(mesh*x) := by ring
  have e3 : κP*(1+x) = κP + κP*x := by ring
  linarith

/-- **The selection reduction with the injective oracle** (`Inj.SelectionReductionExcess`): for
any parent/child families, conditional only on the second Poisson step
(`PoissonStepStatement`, injective marks) and the restoration (`RestoreChildBoundUniform`). No
disjointness of the lists is used anywhere. -/
theorem selectionReductionExcessInj_of (famP famC : SlotClass → Prop)
    (hPS : Poisson.PoissonStepStatement) (hRB : RestoreChildBoundUniform famP famC) :
    -- literally `Inj.SelectionReductionExcess famP famC imageAdm'` (`Inj/Reduction`)
    ∀ Pmax Smax u κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 ≤ u → 0 < κ →
      Pmax+Smax+4*u+10*κ < 1 → 6*u+2*κ < 1 →
      Leaf.UniformInverseRectSourceExcess famC (childRect Pmax Smax u κ) (u/(1-6*u-κ)) →
      Inj.OracleOnInj' imageAdm' famP (HighLive Pmax Smax κ u) := by
  intro Pmax Smax u κ hP hS hu hκ hdiag hrad hchild
  have hHlo : 0 < 1-6*u-κ := by linarith
  set x := u/(1-6*u-κ) with hx
  have hx0 : 0 ≤ x := div_nonneg hu hHlo.le
  have hRm := hRB (childRect Pmax Smax u κ) x (1-6*u-κ) hx0 hHlo hchild
  intro eps heps
  obtain ⟨meshR, hmeshR, hRmesh⟩ := hRm (eps/4) (by positivity)
  have h530 : 0 < 5+30*x := by positivity
  set mesh := min meshR (min (κ/5) (eps/(4*(5+30*x)))) with hmeshdef
  have hmesh0 : 0 < mesh := lt_min hmeshR (lt_min (by positivity) (by positivity))
  have hmeshR' : mesh ≤ meshR := min_le_left _ _
  have hmeshκ : 5*mesh ≤ κ := by
    have : mesh ≤ κ/5 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hmeshe : mesh * (5+30*x) ≤ eps/4 := by
    have h1 : mesh ≤ eps/(4*(5+30*x)) := (min_le_right _ _).trans (min_le_right _ _)
    calc mesh*(5+30*x) ≤ eps/(4*(5+30*x)) * (5+30*x) := mul_le_mul_of_nonneg_right h1 h530.le
      _ = eps/4 := by field_simp
  refine ⟨mesh, hmesh0, ?_⟩
  intro cls hcls K Wcol lo hi hlo hlh hsW
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlh
  have h2K : (1:ℝ) ≤ 2^K := one_le_pow₀ (by norm_num)
  obtain ⟨Φ, hΦsm, hΦsupp, hΦ1, hΦn, -⟩ :=
    Poisson.exists_profile_bump lo (2^K*hi) hlo (by nlinarith)
  obtain ⟨b, hsep⟩ := profile_separation_wide (Wcol : ℝ → ℂ) (Wcol.smooth ⊤) lo hi hlo hsW K Φ
    hΦ1 hΦsupp
  set boΦ := 2*(2^K*hi) with hboΦ
  have hbo : 0 < boΦ := by positivity
  obtain ⟨J, Φs, a', b', ha', hab', hΦs, hdeg⟩ :=
    hPS K Φ (lo/2) boΦ (by positivity) (by rw [hboΦ]; nlinarith) hΦsupp hΦsm
  have hRq := hRmesh cls hcls J Φs a' b' ha' hab' hΦs boΦ hbo K
  have h1x : 0 < 1+x := by linarith
  set κP := min 1 (eps/(4*(1+x))) with hκPdef
  have hκP0 : 0 < κP := lt_min one_pos (by positivity)
  have hκP1 : κP ≤ 1 := min_le_left _ _
  have hκPe : κP*(1+x) ≤ eps/4 := by
    calc κP*(1+x) ≤ eps/(4*(1+x)) * (1+x) := mul_le_mul_of_nonneg_right (min_le_right _ _) h1x.le
      _ = eps/4 := by field_simp
  have hK6 : 0 < 10+6*(K:ℝ) := by positivity
  set η := eps/(8*(10+6*(K:ℝ))) with hηdef
  have hη0 : 0 < η := by positivity
  have hηe : (10+6*(K:ℝ))*η ≤ eps/8 := by rw [hηdef]; field_simp; rfl
  obtain ⟨Cd0, hCd0, hdiv0⟩ :=
    SevenEighths.CenteredMomentMask.polynomial_mask_divisor_bound η 4 hη0 (by norm_num)
  set Cd := max Cd0 1 with hCddef
  have hCd1 : 1 ≤ Cd := le_max_right _ _
  have hev : ∀ᶠ Z : ℝ in atTop, max 2 (2^K*hi) ≤ Z^mesh :=
    (tendsto_rpow_atTop hmesh0).eventually (eventually_ge_atTop _)
  obtain ⟨Zm, hZm⟩ := eventually_atTop.mp hev
  refine ⟨1, le_rfl, fun q hq => ?_⟩
  obtain ⟨dchild, CR, ZR, hCR, hZR, hRZ⟩ := hRq q hq
  obtain ⟨degree, hPd⟩ := hdeg dchild
  obtain ⟨CP, ZP, hCP, hZP, hPZ⟩ := hPd (eps/8) κP (by positivity) hκP0
  set Ib := ∫ t, ‖b t‖ * (1 + ‖t‖)^degree with hIb
  have hsel0 : 0 ≤ selConst Ib CP CR Cd boΦ K := by
    unfold selConst; have : 0 ≤ Cd := by linarith
    positivity
  refine ⟨degree + dchild, selConst Ib CP CR Cd boΦ K + 1,
    max (max ZP ZR) (max (max Zm boΦ) 2), by linarith,
    lt_max_of_lt_right (lt_max_of_lt_right (by norm_num)), ?_⟩
  intro Z hZ Dp hDp σ _ slots hslots lists H a hH hPn ha hv hv0 hadm base hb hper
  have hZ2 : 2 ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZ)
  have hZ1 : 1 < Z := by linarith
  have hZP' : ZP ≤ Z := (le_max_left _ _).trans ((le_max_left _ _).trans hZ)
  have hZR' : ZR ≤ Z := (le_max_right _ _).trans ((le_max_left _ _).trans hZ)
  have hZm' : Zm ≤ Z :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hZ))
  have hZbo : boΦ ≤ Z :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hZ))
  have hZmesh := hZm Z hZm'
  obtain ⟨hHr, hPr⟩ := imageAdm'_ratio hZ1.le hadm
  dsimp only [Inj.GoodPoolRankMomentsInj]
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dp
  have hFa := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dp
    (reflectionExcludedPrimes_bad q)
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hFa i]; infer_instance
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  have hZ3 : Z^3 ≤ (Dp : ℝ) := by
    have h3 : Z^(3:ℝ) = Z^3 := by norm_cast
    rw [← h3]; simpa using hDp
  have hm2 : ‖ConcreteTraceCRT.eisEmbedding m‖^2 ≤ Z^2 := by
    rw [hnorm]
    have hFQ : N+V+Q ≤ Pmax+Smax+κ := hG.1.2.2.2.1
    have h2 : Z^(2:ℝ) = Z^2 := by norm_cast
    rw [← h2]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have hdiv : ∀ I : Ideal O, I ≠ ⊥ → (Ideal.absNorm I : ℝ) ≤ Z^4 →
      ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) ≤ Cd * Z^η := by
    intro I hI hIN
    have hI0 : I ≠ 0 := fun h => hI (h.trans Ideal.zero_eq_bot)
    have h4 : Z^(4:ℝ) = Z^4 := by norm_cast
    refine (hdiv0 Z hZ1.le I hI0 (by rw [h4]; exact hIN)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
  have hPr' : ∀ i ∈ slots, ∀ P ∈ lists i,
      H i / 2 ≤ FirstPassCubeLabels.primeProductNorm (poolPrimary F) {P} ∧
      FirstPassCubeLabels.primeProductNorm (poolPrimary F) {P} ≤ H i := by
    intro i _ P hP
    rw [InverseInitialRayAttachment.poolPrimary_norm F hFa {P}, Finset.prod_singleton]
    exact hPr i P hP
  have hlab' : ∀ I ∈ labels, I ≠ ⊥ ∧ CompletedGauss.primaryGenerator I ≠ 0 ∧
      (Ideal.absNorm I : ℝ) ≤ Z^V := by
    intro I hI
    exact ⟨fun h => (hlab I hI).1.1 (h.trans Ideal.zero_eq_bot.symm),
      supported_primaryGenerator_ne_zero I (admissible_supported (hlab I hI).1), (hlab I hI).2⟩
  have hbound := selection_at_scale (poolPrimary F) (poolPrimary_ne_zero F hFa)
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa)
    Pmax Smax u κ mesh κP (eps/8) (eps/4) η hP hu hκ hdiag hrad hmesh0 hmeshκ hκP0.le hκP1
    (by positivity) (by positivity) hη0.le K Wcol lo hi hlo hlh hsW Φ hΦn boΦ hbo hΦsupp b hsep
    Φs dchild degree CP (CR * (1+hv)^(2*dchild)) Cd hCP.le (by positivity) hCd1 Z hZ1
    ((le_max_left _ _).trans hZmesh)
    ((le_max_right _ _).trans hZmesh) hZbo (hPZ Z hZP') hdiv slots hslots lists H a ha
    (fun i _ => hHr i) hPr' Ψ (IsBaseRayTwist.norm_le hΨ hb) m
    (fun R' hR' Xmax Hc' hX hX2 hlo' hup hgP hgS => hRZ Z hZR' Dp hZ3 slots lists H a hslots hH
      hPn ha hv hv0 (imageAdm'_mono meshR mesh hmeshR' cls q Dp σ slots lists H a Z hv
        hadm) base hb hper Ψ hΨ m hm hm2 R' hR' Xmax Hc' hX hX2 hlo' hup hgP hgS)
    N V M Q hN hV hM hQ ss hss hG labels hlab' s
  refine hbound.trans ?_
  have hexc : selExcess x mesh κP (eps/8) (eps/4) η K ≤ eps :=
    selExcess_le x mesh κP (eps/8) (eps/4) η eps K hmeshe hκPe le_rfl le_rfl hηe
  have hpow : Z^(N+V+selExcess x mesh κP (eps/8) (eps/4) η K) ≤ Z^(N+V+eps) :=
    Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have hS0 : 0 ≤ (1 + ‖s‖)^(2*degree) := by positivity
  have hX1 : 1 ≤ (1+hv)^(2*dchild) := one_le_hvPow hv0 _
  have hsc := selConst_mul_le Ib CP CR Cd boΦ ((1+hv)^(2*dchild)) K hCP.le (by linarith) hbo.le hX1
  have hZe : 0 ≤ Z^(N+V+eps) := Real.rpow_nonneg (by linarith) _
  have hsplit : (1+hv)^(2*dchild)*(1+‖s‖)^(2*degree) ≤ (1+‖s‖+hv)^(2*(degree+dchild)) := by
    have h1 : (1+hv)^(2*dchild) ≤ (1+‖s‖+hv)^(2*dchild) :=
      pow_le_pow_left₀ (by linarith) (by linarith [norm_nonneg s]) _
    have h2 := heightPow_row_le s hv hv0 (2*degree)
    calc _ ≤ (1+‖s‖+hv)^(2*dchild)*(1+‖s‖+hv)^(2*degree) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; ring
  calc selConst Ib CP (CR * (1+hv)^(2*dchild)) Cd boΦ K *
        Z^(N+V+selExcess x mesh κP (eps/8) (eps/4) η K) * (1 + ‖s‖)^(2*degree)
      ≤ (selConst Ib CP CR Cd boΦ K * (1+hv)^(2*dchild)) * Z^(N+V+eps) * (1 + ‖s‖)^(2*degree) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hsc hpow (Real.rpow_nonneg (by linarith) _)
          (mul_nonneg hsel0 (by positivity))) hS0
    _ = selConst Ib CP CR Cd boΦ K * Z^(N+V+eps) * ((1+hv)^(2*dchild)*(1 + ‖s‖)^(2*degree)) := by
        ring
    _ ≤ (selConst Ib CP CR Cd boΦ K + 1) * Z^(N+V+eps) * (1+‖s‖+hv)^(2*(degree+dchild)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hZe) hsplit (by positivity)
          (mul_nonneg (by linarith) hZe)

/-- On separated data the injective oracle is the (full-mark) oracle. -/
theorem goodEnergyExists_of_inj {Adm : SlotAdm} {G : StatePred} {eps L : ℝ} {K : ℕ}
    {W : 𝓢(ℝ,ℂ)} (h : Inj.GoodEnergyExistsInj Adm G eps L K W) :
    GoodEnergyExists Adm G eps L K W := by
  obtain ⟨B, hB, h⟩ := h
  refine ⟨B, hB, fun q hq => ?_⟩
  obtain ⟨degree, C, Z₀, hC, hZ₀, h⟩ := h q hq
  refine ⟨degree, C, Z₀, hC, hZ₀, ?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  have hm := h Z hZ D hD slots hslots lists H a hH hP ha hv hv0 hadm base hb hper
  dsimp only [GoodPoolRankMoments, Inj.GoodPoolRankMomentsInj] at hm ⊢
  let F := InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D
  have hFa := InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q)
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hFa i]; infer_instance
  intro Ψ hΨ m hm0 N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  rw [← columnEnergyInj_eq (poolPrimary F) (poolPrimary_ne_zero F hFa) (poolPrimary_coprime F hFa)
    (poolPrimary_good F hFa) _ _ _ ss lists a (hdis.subset (Finset.coe_subset.mpr hss))]
  exact hm Ψ hΨ m hm0 N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s

theorem oracleOn'_of_inj {Adm : ℝ → SlotClass → SlotAdm} {fam : SlotClass → Prop}
    {G : StatePred} (h : Inj.OracleOnInj' Adm fam G) : OracleOn' Adm fam G := by
  intro eps heps
  obtain ⟨mesh, hmesh, h⟩ := h eps heps
  exact ⟨mesh, hmesh, fun cls hcls K W lo hi hlo hlh hsW =>
    goodEnergyExists_of_inj (h cls hcls K W lo hi hlo hlh hsW)⟩

/-- **`SelectionReductionExcess'`** (the separated oracle) from the injective one. -/
theorem selectionReductionExcess'_of (famP famC : SlotClass → Prop)
    (hPS : Poisson.PoissonStepStatement) (hRB : RestoreChildBoundUniform famP famC) :
    SelectionReductionExcess' famP famC imageAdm' :=
  fun Pmax Smax u κ hP hS hu hκ hdiag hrad hchild =>
    oracleOn'_of_inj (selectionReductionExcessInj_of famP famC hPS hRB Pmax Smax u κ hP hS hu hκ
      hdiag hrad hchild)

/-- The injective selection reduction for the canonical classes (conditional only on the
restoration). -/
theorem selectionReductionExcessInj_canonical
    (hRB : RestoreChildBoundUniform canonicalFamily canonicalFamily) :
    ∀ Pmax Smax u κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 ≤ u → 0 < κ →
      Pmax+Smax+4*u+10*κ < 1 → 6*u+2*κ < 1 →
      Leaf.UniformInverseRectSourceExcess canonicalFamily (childRect Pmax Smax u κ)
        (u/(1-6*u-κ)) →
      Inj.OracleOnInj' imageAdm' canonicalFamily (HighLive Pmax Smax κ u) :=
  selectionReductionExcessInj_of canonicalFamily canonicalFamily Poisson.poissonStepStatement hRB

/-- `selectionReductionExcess'_of` with the second Poisson step `Poisson.poissonStepStatement`,
conditional only on the restoration. -/
theorem selectionReductionExcess'_of_restore (famP famC : SlotClass → Prop)
    (hRB : RestoreChildBoundUniform famP famC) : SelectionReductionExcess' famP famC imageAdm' :=
  selectionReductionExcess'_of famP famC Poisson.poissonStepStatement hRB

/-- The canonical instance (conditional only on the restoration). -/
theorem selectionReductionExcess'_canonical
    (hRB : RestoreChildBoundUniform canonicalFamily canonicalFamily) :
    SelectionReductionExcess' canonicalFamily canonicalFamily imageAdm' :=
  selectionReductionExcess'_of_restore canonicalFamily canonicalFamily hRB

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.selectionReductionExcess'_of
#print axioms Qrh.MarkedAnchor.Inverse.selectionReductionExcess'_canonical
#print axioms Qrh.MarkedAnchor.Inverse.selectionReductionExcessInj_canonical
