/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Chain
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.AdmDef
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Oracle

/-!
# Inverse.Inj.Reduction — the target theorem with the injective oracle

`Inverse.Chain.OracleChainInj'` takes the DISJOINT oracle `OracleOn'` (`GoodEnergyExists` with
`PairwiseDisjoint lists`) as hypothesis. On overlapping canonical lists that oracle says nothing
(colored sub-lists are not dictionary images, so `imageAdm'` rejects them), hence the injective
chain consumes the INJECTIVE oracle `Inj.OracleOnInj'` (`Inj/Oracle.lean`). This file states
the two halves of the reduction in that form and glues them:

* `Inj.OracleChain fam Adm` — `OracleChainInj'` with `OracleOnInj'` (supplied by
  `Inj.oracleChain_canonical`, `Inj/Init/DirectEnergy`);
* `Inj.SelectionReductionExcess famP famC Adm` — `SelectionReductionExcess'` producing
  `OracleOnInj'` on `HighLive` (supplied by `selectionReductionExcessInj_canonical`,
  `Select/Assembly`, given the restoration);
* `Inj.inverse_reduction_excess`, `Inj.inverse_reduction_excess_canonical_stage`: the glue
  (native `LowLive` branch via coloring, `full ⇐ injective` exit).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open Qrh.MarkedAnchor.Interface.Contract
open Qrh.MarkedAnchor.Inverse

/-- The injective chain with the injective oracle. -/
def OracleChain (fam : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm) : Prop :=
  ∀ Pmax Smax κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 < κ → Pmax+Smax+κ < 1 →
    OracleOnInj' Adm fam (InitState Pmax Smax κ) →
    UniformInverseRectSourceInj fam ⟨Pmax, Smax⟩

/-- The selection reduction producing the injective oracle. -/
def SelectionReductionExcess (famP famC : SlotClass → Prop) (Adm : ℝ → SlotClass → SlotAdm) :
    Prop :=
  ∀ Pmax Smax u κ : ℝ, 0 ≤ Pmax → 0 ≤ Smax → 0 ≤ u → 0 < κ →
    Pmax+Smax+4*u+10*κ < 1 → 6*u+2*κ < 1 →
    Leaf.UniformInverseRectSourceExcess famC (childRect Pmax Smax u κ) (u/(1-6*u-κ)) →
    OracleOnInj' Adm famP (HighLive Pmax Smax κ u)

/-- **Target theorem (excess form) with the injective oracle.** -/
theorem inverse_reduction_excess (famP famC : SlotClass → Prop)
    (Adm : ℝ → SlotClass → SlotAdm)
    (hAdm : ∀ mesh mesh', mesh' ≤ mesh → ∀ cls q D σ [DecidableEq σ] slots lists H a Z hv,
      Adm mesh' cls q D σ slots lists H a Z hv → Adm mesh cls q D σ slots lists H a Z hv)
    (hemb : ∀ cls, famP cls → EmbClosed cls)
    (hchain : OracleChain famP Adm) (hsel : SelectionReductionExcess famP famC Adm)
    (Pmax Smax u κ : ℝ) (hP : 0 ≤ Pmax) (hS : 0 ≤ Smax) (hu : 0 ≤ u) (hκ : 0 < κ)
    (hdiag : Pmax+Smax+4*u+10*κ < 1) (hrad : 6*u+2*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess famC (childRect Pmax Smax u κ)
      (u/(1-6*u-κ))) :
    UniformInverseRectSource famP ⟨Pmax, Smax⟩ := by
  apply UniformInverseRectSourceInj.toFull hemb
  apply hchain Pmax Smax κ hP hS hκ (by linarith)
  exact oracleOnInj'_initState Adm famP hAdm Pmax Smax κ u hκ.le hP hS (by linarith)
    (by linarith) (hsel Pmax Smax u κ hP hS hu hκ hdiag hrad hchild)

/-- The canonical stage form (`u = (1-H)/6`, image filter). -/
theorem inverse_reduction_excess_canonical_stage
    (hchain : OracleChain canonicalFamily imageAdm')
    (hsel : SelectionReductionExcess canonicalFamily canonicalFamily imageAdm')
    (H r s κ : ℝ) (hH : 47/50 ≤ H) (hH1 : H ≤ 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/1000) (hdiag : r+s+4*((1-H)/6)+10*κ < 1)
    (hchild : Leaf.UniformInverseRectSourceExcess canonicalFamily (childRect r s ((1-H)/6) κ)
      (((1-H)/6)/(1-6*((1-H)/6)-κ))) :
    UniformInverseRectSource canonicalFamily ⟨r, s⟩ :=
  inverse_reduction_excess canonicalFamily canonicalFamily imageAdm' imageAdm'_mono
    canonicalFamily_embClosed hchain hsel r s ((1-H)/6) κ hr hs (by linarith) hκ hdiag
    (by linarith) hchild

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.inverse_reduction_excess_canonical_stage
