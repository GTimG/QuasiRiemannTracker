/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Actual zero-stage-decrement inverse anchor. The generic restoration and
selection reductions are reused with their literal Möbius coefficients. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.Leaf
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.Priced
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.TopSources
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Price.Gates
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Leaf.Stage
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Inj.Reduction
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Inj.Init.DirectEnergy
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.Stage
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Main

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorZeroLoss
noncomputable section
open Qrh.MarkedAnchor Qrh.MarkedAnchor.Price
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Interface.Native
open Qrh.TwoSlot.AnchorExtension.ChainData

/-- The exact child rectangle at zero fixed stage decrement. -/
def zeroChild (R z k r β : ℝ) : AnchorRect :=
  Qrh.MarkedAnchor.Inverse.childRect (r-β) ((1-r)/2+fY R z k r-β) (fu R r) (β/8)

def zeroExcess (R r β : ℝ) : ℝ := fu R r/(1-6*fu R r-β/8)

/-- Inverse restoration from an actual priced HIGH input. This theorem
retains every positive rectangle decrement and is independent of the choice
of an earlier-source construction. -/
theorem inverse_anchor_of_priced [shift : High.WitnessShift]
    {R z k r a0 a1 wlo : ℝ} (hS : StageHyp R z k r) (hprev : AnchorAt R z)
    (hpriced : High.Inverse.InverseHighPriced canonicalFamily a0 a1 k wlo)
    (hledger : ∀ β : ℝ, 0 < β → β ≤ 1/1000 → ∀ P S : ℝ,
      (zeroChild R z k r β).Admissible P S 1 →
      High.highPriceFW a0 a1 k wlo P S 1 ≤ zeroExcess R r β) :
    ∀ β : ℝ, 0 < β → UniformInverseRectSource canonicalFamily
      (anchorRect r (fY R z k r) β) := by
  have hsmall (β : ℝ) (hb : 0<β) (hbhi : β≤1/1000) :
      UniformInverseRectSource canonicalFamily (anchorRect r (fY R z k r) β) := by
    have hkappa : 0<β/8 := by linarith
    have hu := hS.hu
    have hu0 := hS.u_nonneg
    have hHlo := hS.H_ge
    have hHhi := hS.H_le_one
    have hRlo := hS.hR.1
    have hRhi := hS.hR.2
    have hrlo := hS.hr.1
    have hrhi := hS.hr.2
    have hSR := hS.hSR
    have hz := hS.hz
    have hy := hS.Y_nonneg
    have hg := hS.g4
    dsimp only [fS] at hg
    have hpos : 0<1-6*fu R r-β/8 := by linarith
    have hρ : (zeroChild R z k r β).Pmax≤1 := by
      change (r-β+2*(β/8))/(1-6*fu R r-β/8)≤1
      rw [div_le_one hpos]
      linarith
    have hhigh := High.Inverse.inverse_high_energy_of_priced hpriced hρ (hledger β hb hbhi)
    have hchild := Qrh.MarkedAnchor.Inverse.Leaf.inverse_child_stage_u canonicalFamily
      Qrh.MarkedAnchor.Inverse.Leaf.canonicalFamily_subClosed R z k r 0 β (β/8) hS.R_pos hrhi hS.k_pos (by norm_num)
      hb hkappa (by linarith)
      (by nlinarith) (by nlinarith) (by linarith) (by linarith)
      (fun δ hδ=>(hprev δ hδ).1)
      (by simpa only [zeroChild,zeroExcess,sub_zero] using hhigh)
    have hu_eq : (1-fH R r)/6=fu R r := by unfold fH fu; ring
    have hchild' : Qrh.MarkedAnchor.Inverse.Leaf.UniformInverseRectSourceExcess canonicalFamily
        (Qrh.MarkedAnchor.Inverse.childRect (r-β) ((1-r)/2+fY R z k r-β)
          ((1-fH R r)/6) (β/8))
        (((1-fH R r)/6)/(1-6*((1-fH R r)/6)-β/8)) := by
      rw [hu_eq]
      simpa only [sub_zero] using hchild
    exact Qrh.MarkedAnchor.Inverse.Inj.inverse_reduction_excess_canonical_stage
      Qrh.MarkedAnchor.Inverse.Inj.oracleChain_canonical
      (Qrh.MarkedAnchor.Inverse.selectionReductionExcessInj_canonical
        Qrh.MarkedAnchor.Inverse.Restore.restoreChildBoundUniform_canonical)
      (fH R r) (r-β) ((1-r)/2+fY R z k r-β) (β/8)
      (by linarith) hHhi (by linarith) (by linarith) hkappa (by linarith)
      (by rw [hu_eq]; linarith) hchild'
  intro β hb
  by_cases h : β≤1/1000
  · exact hsmall β hb h
  · exact (hsmall (1/1000) (by norm_num) le_rfl).restrict
      (anchorRect_restricts (by linarith) (by linarith))

theorem inverse_anchor_of_earlier {R z k r a0 a1 wlo T : ℝ}
    (hS : StageHyp R z k r)
    (hβ : (51/100:ℝ)≤OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : ReserveParametricSource) (hprev : AnchorAt R z)
    (hR : R<wlo) (hwlo : 0≤wlo) (hwlocut : wlo≤High.cutHi)
    (hTlo : 3/4≤T) (hThi : T≤7/9)
    (ha : 0≤a1) (ha1 : a1≤2/5) (hl : a0-a1*T≤0)
    (hprior : ∀x : ℝ,R<x → x≤T → ∃gain : ℝ,0≤gain ∧ a0-a1*x≤gain ∧ AnchorAt x gain)
    (hledger : ∀β : ℝ,0<β → β≤1/1000 → ∀P S : ℝ,
      (zeroChild R z k r β).Admissible P S 1 →
      High.highPriceFW a0 a1 k wlo P S 1≤zeroExcess R r β) :
    ∀β : ℝ,0<β → UniformInverseRectSource canonicalFamily (anchorRect r (fY R z k r) β) := by
  have hM := High.Marked.markedCore_of_earlier hβ hres R T wlo a0 a1
    hR hwlo hTlo hThi ha ha1 hl hprior
  have hpriced := High.Inverse.inverseHighLeaf a0 a1 k wlo hβ
    (by linarith [hS.hk.1]) (by linarith [hS.hk.2]) ha (by linarith) hwlocut hM
  exact inverse_anchor_of_priced hS hprev hpriced hledger

end
end Qrh.TwoSlot.AnchorZeroLoss
#print axioms Qrh.TwoSlot.AnchorZeroLoss.inverse_anchor_of_earlier
