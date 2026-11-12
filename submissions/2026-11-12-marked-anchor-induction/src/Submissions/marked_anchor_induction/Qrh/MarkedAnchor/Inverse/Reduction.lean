/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Oracle
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Predicate
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Leaf.HighInput

/-!
# Inverse.Reduction — the inverse reduction (target theorem, hypothesis-parametric form)

Parent: the inverse contract `UniformInverseRectSource fam ⟨Pmax, Smax⟩` (radius `1`).
Child: the inverse contract on `childRect Pmax Smax u κ = ⟨(Pmax+2κ)/(1-6u-κ), (Smax-u+3κ)/(1-6u-κ)⟩`
at radius `1`; by the rescaling of `Inverse.Predicate` this is the child at row radius
`H - κ = 1-6u-κ`, free width `≤ Pmax+2κ`, mark width `≤ Smax-u+3κ` (free width not above the
parent's, marks reduced by the selected width `u`, radius `≥ H`).

The theorems here take the two halves of the reduction as hypotheses:

* `OracleChain fam Adm` (the oracle-parametric clone of the baseline chain
  `retained_physical_bound … original_source_energy` plus HC's `direct_reference_energy`
  dictionary): the canonical-energy oracle on the initial states `InitState Pmax Smax κ` of the
  parent gives the parent contract.
* `SelectionReduction fam Adm` (fourth-power selection, the second Poisson step
  `PoissonStepStatement`, restoration of the inverse and the slots): the child contract gives the
  oracle on the states with enough live marks (`HighLive … u`, live width `≥ u`).
* The states with few live marks (`LowLive … u`, live width `≤ u`: take `u = 0`) are paid
  natively: `goodEnergyExists_lowLive` (from the baseline `canonical_marked_energy_exists`).
* Gluing: `GoodEnergyExists.union`, `initState_split`.

`inverse_reduction` is the target theorem; `inverse_reduction_stage` is its form at
`u = (1-H)/6`, `H ∈ [47/50, 1]`. The instances for the canonical family, with both hypotheses
supplied, use the injective forms of `Inj/Reduction`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths OAI.SevenEighths.InverseMoment
open Qrh.MarkedAnchor.Interface.Contract

/-- The oracle on the states `Good`: for every loss `eps` a slot mesh,
then for every slot bound `K` and every compactly supported Schwartz profile on `[lo, hi]`,
`0 < lo` (the fresh profiles produced inside `actual_physical_reference_bound`), the oracle with
the pool exponent `L = 3` (the baseline's `cap+1` with `cap = 2`). -/
def OracleOn (Adm : ℝ → SlotAdm) (Good : StatePred) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ mesh : ℝ, 0 < mesh ∧
    ∀ (K : ℕ) (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ), 0 < lo → lo ≤ hi →
      Function.support (W : ℝ → ℂ) ⊆ Icc lo hi →
      GoodEnergyExists (Adm mesh) Good eps 3 K W

theorem OracleOn.mono_good {Adm : ℝ → SlotAdm} {G G' : StatePred}
    (hG : ∀ N V M Q z, G' N V M Q z → G N V M Q z) (h : OracleOn Adm G) :
    OracleOn Adm G' := by
  intro eps heps
  obtain ⟨mesh,hmesh,h⟩ := h eps heps
  refine ⟨mesh,hmesh,fun K W lo hi hlo hlh hs => ?_⟩
  exact (h K W lo hi hlo hlh hs).mono_good hG

/-- The states of `GoodRankMoments` are nonnegative; adding this to `Good` changes nothing. -/
def withNonneg (G : StatePred) : StatePred := fun N V M Q z =>
  0 ≤ N ∧ 0 ≤ V ∧ 0 ≤ Q ∧ G N V M Q z

theorem GoodEnergyExists.of_withNonneg {Adm : SlotAdm} {G : StatePred} {eps L : ℝ}
    {K : ℕ} {W : 𝓢(ℝ,ℂ)} (h : GoodEnergyExists Adm (withNonneg G) eps L K W) :
    GoodEnergyExists Adm G eps L K W := by
  obtain ⟨B,hB,h⟩ := h
  refine ⟨B,hB,fun q hq => ?_⟩
  obtain ⟨degree,C,Z₀,hC,hZ₀,h⟩ := h q hq
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ D hD σ _ slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  have hmom := h Z hZ D hD slots hslots lists H a hdis hH hP ha hv hv0 hadm base hb hper
  dsimp only [GoodPoolRankMoments] at hmom ⊢
  intro Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss hG labels hlab s
  exact hmom Ψ hΨ m hm N V M Q hN hV hM hQ hnorm ss hss ⟨hN,hV,hQ,hG⟩ labels hlab s

/-- The child rectangle of a parent `⟨Pmax, Smax⟩` at selection width `u` and slack `κ`,
relative to the child radius `1-6u-κ` (radius `1` after rescaling): free width `≤ Pmax+2κ`
(`N - w ≤ Pmax+κ` at the actual live width `w`), marks `≤ Smax-u+3κ` (selected width
`≥ u - mesh`). -/
def childRect (Pmax Smax u κ : ℝ) : AnchorRect :=
  ⟨(Pmax+2*κ)/(1-6*u-κ), (Smax-u+3*κ)/(1-6*u-κ)⟩

/-! ## The two halves of the reduction -/

/-- The oracle-parametric baseline chain. For every parent rectangle and slack
`κ > 0`, the canonical-energy oracle on the initial states of the parent (for the slot data
admitted by `Adm mesh`) gives the parent inverse contract. -/
def OracleChain (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm) : Prop :=
  ∀ Pmax Smax κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 < κ → Pmax+Smax+κ < 1 →
    OracleOn Adm (InitState Pmax Smax κ) →
    UniformInverseRectSource fam ⟨Pmax, Smax⟩

/-- The selection reduction: fourth-power selection of width `u`, the second Poisson step
(`PoissonStepStatement`) and the restoration of the actual inverse and slots turn the child
contract into the oracle on the initial states with live width
`≥ u`. Gates: the direct diagonal `F + 4u < 1` (`F ≤ Pmax + Smax + 2κ`), the child radius
`1-6u-κ > 0`. -/
def SelectionReduction (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm) : Prop :=
  ∀ Pmax Smax u κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 ≤ u → 0 < κ →
    Pmax+Smax+4*u+10*κ < 1 → 6*u+2*κ < 1 →
    UniformInverseRectSource fam (childRect Pmax Smax u κ) →
    OracleOn Adm (HighLive Pmax Smax κ u)

/-! ## The `u = 0` branch and the target theorem -/

/-- Few live marks: the oracle on `LowLive` states (native). -/
theorem oracleOn_lowLive (Adm : ℝ → SlotAdm) (Pmax Smax κ u : ℝ) (hκ : 0 ≤ κ)
    (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hgate₁ : Pmax+Smax+u+3*κ < 1)
    (hgate₂ : 2*Pmax+2*Smax+6*u+5*κ < 3) :
    OracleOn Adm (LowLive Pmax Smax κ u) := by
  intro eps heps
  refine ⟨1,one_pos,fun K W lo hi hlo hlh hs => ?_⟩
  exact GoodEnergyExists.of_withNonneg
    (goodEnergyExists_lowLive (Adm 1) Pmax Smax κ u eps hκ hP hS hgate₁ hgate₂ heps K W lo hi
      hlo (hlo.le.trans hlh) hs)

/-- Gluing the native low-live oracle and the selected high-live oracle. -/
theorem oracleOn_initState (Adm : ℝ → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' q D σ slots lists H a Z hv → Adm mesh q D σ slots lists H a Z hv)
    (Pmax Smax κ u : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax)
    (hgate₁ : Pmax+Smax+u+3*κ < 1) (hgate₂ : 2*Pmax+2*Smax+6*u+5*κ < 3)
    (hhigh : OracleOn Adm (HighLive Pmax Smax κ u)) :
    OracleOn Adm (InitState Pmax Smax κ) := by
  intro eps heps
  obtain ⟨mesh,hmesh,hh⟩ := hhigh eps heps
  have hlow := oracleOn_lowLive Adm Pmax Smax κ u hκ hP hS hgate₁ hgate₂ eps heps
  obtain ⟨mesh₁,hmesh₁,hl⟩ := hlow
  refine ⟨min mesh mesh₁,lt_min hmesh hmesh₁,fun K W lo hi hlo hlh hs => ?_⟩
  have h₁ := hl K W lo hi hlo hlh hs
  have h₂ := hh K W lo hi hlo hlh hs
  have h₁' := h₁.mono_adm (Adm' := Adm (min mesh mesh₁))
    (fun q D σ _ slots lists H a Z hv h =>
      hAdm mesh₁ _ (min_le_right _ _) q D σ slots lists H a Z hv h)
  have h₂' := h₂.mono_adm (Adm' := Adm (min mesh mesh₁))
    (fun q D σ _ slots lists H a Z hv h =>
      hAdm mesh _ (min_le_left _ _) q D σ slots lists H a Z hv h)
  have hu := h₁'.union h₂'
  rw [max_self] at hu
  refine hu.mono_good ?_
  intro N V M Q z hI
  exact initState_split Pmax Smax κ u N V M Q z hI

/-- **Target theorem.** Under the diagonal gate and the native gate of the `u = 0`
branch, the child inverse contract on `childRect Pmax Smax u κ` gives the parent inverse
contract on `⟨Pmax, Smax⟩`, given the oracle chain and the selection reduction. -/
theorem inverse_reduction (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' q D σ slots lists H a Z hv → Adm mesh q D σ slots lists H a Z hv)
    (hchain : OracleChain fam Adm) (hsel : SelectionReduction fam Adm)
    (Pmax Smax u κ : ℝ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hu : 0 ≤ u) (hκ : 0 < κ)
    (hdiag : Pmax+Smax+4*u+10*κ < 1) (hrad : 6*u+2*κ < 1)
    (hchild : UniformInverseRectSource fam (childRect Pmax Smax u κ)) :
    UniformInverseRectSource fam ⟨Pmax, Smax⟩ := by
  apply hchain Pmax Smax κ hP hS hκ (by linarith)
  exact oracleOn_initState Adm hAdm Pmax Smax κ u hκ.le hP hS (by linarith) (by linarith)
    (hsel Pmax Smax u κ hP hS hu hκ hdiag hrad hchild)

/-- The target theorem at a stage: `H ∈ [47/50, 1]`, `u = (1-H)/6 ∈ [0, 1/100]`, parent free
width `r ≤ 4/5`, diagonal gate `r + s + 4u + 10κ < 1`, slack `κ ≤ 1/1000`. The native gates of
the `u = 0` branch are automatic. -/
theorem inverse_reduction_stage (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' q D σ slots lists H a Z hv → Adm mesh q D σ slots lists H a Z hv)
    (hchain : OracleChain fam Adm) (hsel : SelectionReduction fam Adm)
    (H r s κ : ℝ) (hH : 47/50 ≤ H) (hH1 : H ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 4/5) (hs : 0 ≤ s)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/1000) (hdiag : r+s+4*((1-H)/6)+10*κ < 1)
    (hchild : UniformInverseRectSource fam (childRect r s ((1-H)/6) κ)) :
    UniformInverseRectSource fam ⟨r, s⟩ :=
  inverse_reduction fam Adm hAdm hchain hsel r s ((1-H)/6) κ hr hs (by linarith) hκ hdiag
    (by linarith) hchild

/-! ## The child rectangle against an earlier anchor (rescaling bookkeeping) -/

/-- The child rectangle lies in an anchor rectangle `⟨P', S'⟩` (radius `1`) as soon as
`Pmax + 2κ ≤ P' (1-6u-κ)` and `Smax - u + 3κ ≤ S' (1-6u-κ)`. -/
theorem childRect_restricts {Pmax Smax u κ : ℝ} {ρ : AnchorRect} (hrad : 6*u+κ < 1)
    (hP : Pmax+2*κ ≤ ρ.Pmax*(1-6*u-κ)) (hS : Smax-u+3*κ ≤ ρ.Smax*(1-6*u-κ)) :
    ρ.Restricts (childRect Pmax Smax u κ) := by
  have hpos : 0 < 1-6*u-κ := by linarith
  constructor
  · show (Pmax+2*κ)/(1-6*u-κ) ≤ ρ.Pmax
    rw [div_le_iff₀ hpos]; exact hP
  · show (Smax-u+3*κ)/(1-6*u-κ) ≤ ρ.Smax
    rw [div_le_iff₀ hpos]; exact hS

/-- The target theorem with the child supplied by an earlier anchor contract. -/
theorem inverse_reduction_of_anchor (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' q D σ slots lists H a Z hv → Adm mesh q D σ slots lists H a Z hv)
    (hchain : OracleChain fam Adm) (hsel : SelectionReduction fam Adm)
    (Pmax Smax u κ : ℝ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hu : 0 ≤ u) (hκ : 0 < κ)
    (hdiag : Pmax+Smax+4*u+10*κ < 1) (hrad : 6*u+2*κ < 1)
    {ρ : AnchorRect} (hρP : Pmax+2*κ ≤ ρ.Pmax*(1-6*u-κ)) (hρS : Smax-u+3*κ ≤ ρ.Smax*(1-6*u-κ))
    (hanchor : UniformInverseRectSource fam ρ) :
    UniformInverseRectSource fam ⟨Pmax, Smax⟩ :=
  inverse_reduction fam Adm hAdm hchain hsel Pmax Smax u κ hP hS hu hκ hdiag hrad
    (hanchor.restrict (childRect_restricts (by linarith) hρP hρS))

/-! ## The excess form of the child

The physical child is paid at `Z^(H+u+ε)`, not row-sized: the child is consumed as
`UniformInverseRectSourceExcess fam (childRect Pmax Smax u κ) (u/(1-6u-κ))`, normalized at the
child radius `Hc = 1-6u-κ` with relative excess `u/Hc` (absolute excess `u`), exactly the output
of `Leaf.chain_inverse_child`. -/

/-- The selection reduction in the excess form: the child with absolute excess `u` gives the
oracle on the states with live width `≥ u`. Implies `SelectionReduction`. -/
def SelectionReductionExcess (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm) : Prop :=
  ∀ Pmax Smax u κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 ≤ u → 0 < κ →
    Pmax+Smax+4*u+10*κ < 1 → 6*u+2*κ < 1 →
    Leaf.UniformInverseRectSourceExcess fam (childRect Pmax Smax u κ) (u/(1-6*u-κ)) →
    OracleOn Adm (HighLive Pmax Smax κ u)

theorem SelectionReductionExcess.toSelectionReduction {fam : SlotClass → Prop}
    {Adm : ℝ → SlotAdm} (h : SelectionReductionExcess fam Adm) : SelectionReduction fam Adm := by
  intro Pmax Smax u κ hP hS hu hκ hdiag hrad hchild
  exact h Pmax Smax u κ hP hS hu hκ hdiag hrad
    (Leaf.UniformInverseRectSource.excess (div_nonneg hu (by linarith)) hchild)

/-- **Target theorem, excess form.** -/
theorem inverse_reduction_excess (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' q D σ slots lists H a Z hv → Adm mesh q D σ slots lists H a Z hv)
    (hchain : OracleChain fam Adm) (hsel : SelectionReductionExcess fam Adm)
    (Pmax Smax u κ : ℝ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hu : 0 ≤ u) (hκ : 0 < κ)
    (hdiag : Pmax+Smax+4*u+10*κ < 1) (hrad : 6*u+2*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess fam (childRect Pmax Smax u κ) (u/(1-6*u-κ))) :
    UniformInverseRectSource fam ⟨Pmax, Smax⟩ := by
  apply hchain Pmax Smax κ hP hS hκ (by linarith)
  exact oracleOn_initState Adm hAdm Pmax Smax κ u hκ.le hP hS (by linarith) (by linarith)
    (hsel Pmax Smax u κ hP hS hu hκ hdiag hrad hchild)

/-- The excess target theorem at a stage `u = (1-H)/6`. -/
theorem inverse_reduction_excess_stage (fam : SlotClass → Prop) (Adm : ℝ → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' q D σ slots lists H a Z hv → Adm mesh q D σ slots lists H a Z hv)
    (hchain : OracleChain fam Adm) (hsel : SelectionReductionExcess fam Adm)
    (H r s κ : ℝ) (hH : 47/50 ≤ H) (hH1 : H ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/1000) (hdiag : r+s+4*((1-H)/6)+10*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess fam (childRect r s ((1-H)/6) κ)
      (((1-H)/6)/(1-6*((1-H)/6)-κ))) :
    UniformInverseRectSource fam ⟨r, s⟩ :=
  inverse_reduction_excess fam Adm hAdm hchain hsel r s ((1-H)/6) κ hr hs (by linarith) hκ hdiag
    (by linarith) hchild

/-! ## Class-indexed slot filter (per-class reduction)

Here the filter depends on the parent slot class: `Adm : ℝ → SlotClass → SlotAdm`. The oracle fixes
the class after the mesh and BEFORE `∃ degree B, ∀ q ∃ C Z₀` (as `InverseRectSource`'s
`∀ K cls Φ ∃ degree`), so constants may depend on the class (its slot bump), while the mesh is
uniform over the family. The selection reduction is stated with separate parent and child families
`famP`, `famC`. -/

/-- The oracle on the states `Good`, per slot class of `fam` (class-indexed filter). -/
def OracleOn' (Adm : ℝ → SlotClass → SlotAdm) (fam : SlotClass → Prop) (Good : StatePred) :
    Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ mesh : ℝ, 0 < mesh ∧
    ∀ cls : SlotClass, fam cls →
    ∀ (K : ℕ) (W : 𝓢(ℝ,ℂ)) (lo hi : ℝ), 0 < lo → lo ≤ hi →
      Function.support (W : ℝ → ℂ) ⊆ Icc lo hi →
      GoodEnergyExists (Adm mesh cls) Good eps 3 K W

theorem OracleOn'.mono_good {Adm : ℝ → SlotClass → SlotAdm} {fam : SlotClass → Prop}
    {G G' : StatePred} (hG : ∀ N V M Q z, G' N V M Q z → G N V M Q z) (h : OracleOn' Adm fam G) :
    OracleOn' Adm fam G' := by
  intro eps heps
  obtain ⟨mesh,hmesh,h⟩ := h eps heps
  exact ⟨mesh,hmesh,fun cls hcls K W lo hi hlo hlh hs =>
    (h cls hcls K W lo hi hlo hlh hs).mono_good hG⟩

/-- The oracle chain for the class-indexed filter. -/
def OracleChain' (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm) : Prop :=
  ∀ Pmax Smax κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 < κ → Pmax+Smax+κ < 1 →
    OracleOn' Adm fam (InitState Pmax Smax κ) →
    UniformInverseRectSource fam ⟨Pmax, Smax⟩

/-- The selection reduction, excess form, per class: the child contract of the family `famC` (absolute excess
`u`) gives the oracle for the parent classes of `famP` on the states with live width `≥ u`. -/
def SelectionReductionExcess' (famP famC : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm) :
    Prop :=
  ∀ Pmax Smax u κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 ≤ u → 0 < κ →
    Pmax+Smax+4*u+10*κ < 1 → 6*u+2*κ < 1 →
    Leaf.UniformInverseRectSourceExcess famC (childRect Pmax Smax u κ) (u/(1-6*u-κ)) →
    OracleOn' Adm famP (HighLive Pmax Smax κ u)

theorem oracleOn'_lowLive (Adm : ℝ → SlotClass → SlotAdm) (fam : SlotClass → Prop)
    (Pmax Smax κ u : ℝ) (hκ : 0 ≤ κ)
    (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hgate₁ : Pmax+Smax+u+3*κ < 1)
    (hgate₂ : 2*Pmax+2*Smax+6*u+5*κ < 3) :
    OracleOn' Adm fam (LowLive Pmax Smax κ u) := by
  intro eps heps
  refine ⟨1,one_pos,fun cls _ K W lo hi hlo hlh hs => ?_⟩
  exact GoodEnergyExists.of_withNonneg
    (goodEnergyExists_lowLive (Adm 1 cls) Pmax Smax κ u eps hκ hP hS hgate₁ hgate₂ heps K W lo
      hi hlo (hlo.le.trans hlh) hs)

theorem oracleOn'_initState (Adm : ℝ → SlotClass → SlotAdm) (fam : SlotClass → Prop)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ cls q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' cls q D σ slots lists H a Z hv → Adm mesh cls q D σ slots lists H a Z hv)
    (Pmax Smax κ u : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax)
    (hgate₁ : Pmax+Smax+u+3*κ < 1) (hgate₂ : 2*Pmax+2*Smax+6*u+5*κ < 3)
    (hhigh : OracleOn' Adm fam (HighLive Pmax Smax κ u)) :
    OracleOn' Adm fam (InitState Pmax Smax κ) := by
  intro eps heps
  obtain ⟨mesh,hmesh,hh⟩ := hhigh eps heps
  obtain ⟨mesh₁,hmesh₁,hl⟩ :=
    oracleOn'_lowLive Adm fam Pmax Smax κ u hκ hP hS hgate₁ hgate₂ eps heps
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

/-- **Target theorem, excess form, class-indexed filter.** -/
theorem inverse_reduction_excess' (famP famC : SlotClass → Prop)
    (Adm : ℝ → SlotClass → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ cls q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' cls q D σ slots lists H a Z hv → Adm mesh cls q D σ slots lists H a Z hv)
    (hchain : OracleChain' famP Adm) (hsel : SelectionReductionExcess' famP famC Adm)
    (Pmax Smax u κ : ℝ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hu : 0 ≤ u) (hκ : 0 < κ)
    (hdiag : Pmax+Smax+4*u+10*κ < 1) (hrad : 6*u+2*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess famC (childRect Pmax Smax u κ)
      (u/(1-6*u-κ))) :
    UniformInverseRectSource famP ⟨Pmax, Smax⟩ := by
  apply hchain Pmax Smax κ hP hS hκ (by linarith)
  exact oracleOn'_initState Adm famP hAdm Pmax Smax κ u hκ.le hP hS (by linarith) (by linarith)
    (hsel Pmax Smax u κ hP hS hu hκ hdiag hrad hchild)

/-- The class-indexed excess target theorem at a stage `u = (1-H)/6`. -/
theorem inverse_reduction_excess_stage' (famP famC : SlotClass → Prop)
    (Adm : ℝ → SlotClass → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ cls q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' cls q D σ slots lists H a Z hv → Adm mesh cls q D σ slots lists H a Z hv)
    (hchain : OracleChain' famP Adm) (hsel : SelectionReductionExcess' famP famC Adm)
    (H r s κ : ℝ) (hH : 47/50 ≤ H) (hH1 : H ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/1000) (hdiag : r+s+4*((1-H)/6)+10*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess famC (childRect r s ((1-H)/6) κ)
      (((1-H)/6)/(1-6*((1-H)/6)-κ))) :
    UniformInverseRectSource famP ⟨r, s⟩ :=
  inverse_reduction_excess' famP famC Adm hAdm hchain hsel r s ((1-H)/6) κ hr hs (by linarith)
    hκ hdiag (by linarith) hchild

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.inverse_reduction_excess'
#print axioms Qrh.MarkedAnchor.Inverse.oracleOn_initState
#print axioms Qrh.MarkedAnchor.Inverse.inverse_reduction
#print axioms Qrh.MarkedAnchor.Inverse.inverse_reduction_stage
#print axioms Qrh.MarkedAnchor.Inverse.inverse_reduction_of_anchor
#print axioms Qrh.MarkedAnchor.Inverse.inverse_reduction_excess
