/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Leaf.Stage
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Price.Gates

/-!
# Inverse.Leaf.Chain — the inverse child at every point of the 176-stage chain

Stage `n < 176`, `r ∈ [left n, R n]`, anchor decrement `β ∈ (0, 1/1000]`, reduction slack
`κ ∈ (0, β/8]`, stage decrement `δ = 4·10^-8`. The scalar facts come from
`Price.stageHyp_chain` (ChainCheck gates interpolated to real `r`): `R ∈ [7/10, 311/400]`,
`k = cut n ∈ [45457/125000, 1/2)`, `z = gain n ≥ 0`, `S_R ≤ 137/1000`, `u ≤ 10^-4`.

`chain_inverse_child`: previous inverse anchor `(R n, gain n)` + the HIGH input on the child
rectangle ⇒ the child contract on
`childRect (r-β) ((1-r)/2 + (Y(r)-δ) - β) u κ` with excess `u/(1-6u-κ)` (absolute `u` at the
child radius: the child budget `H + u`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Leaf
noncomputable section

open Qrh.MarkedAnchor.Interface.Contract
open Qrh.MarkedAnchor.Anchor.ChainData

/-- The child rectangle of the inverse reduction at stage `n`, point `r`, decrements `β`, `κ`. -/
def chainChildRect (n : ℕ) (r β κ : ℝ) : AnchorRect :=
  childRect (r-β) ((1-r)/2 + (fY (R n : ℝ) (gain n) (cut n) r - 1/25000000) - β)
    (fu (R n : ℝ) r) κ

/-- The excess of the chain child: `u/(1-6u-κ)`. -/
def chainExcess (n : ℕ) (r κ : ℝ) : ℝ := fu (R n : ℝ) r/(1-6*fu (R n : ℝ) r-κ)

/-- **The inverse child at a chain point.** -/
theorem chain_inverse_child (n : ℕ) (hn : n < 176) (r : ℝ) (h1 : (left n : ℝ) ≤ r)
    (h2 : r ≤ R n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000) (κ : ℝ) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ β/8)
    (hprev : ∀ δ' : ℝ, 0 < δ' →
      UniformInverseRectSource canonicalFamily (anchorRect (R n) (gain n) δ'))
    (hhigh : InverseHighEnergy canonicalFamily (chainChildRect n r β κ) (cut n)
      (chainExcess n r κ)) :
    UniformInverseRectSourceExcess canonicalFamily (chainChildRect n r β κ)
      (chainExcess n r κ) := by
  have h := Qrh.MarkedAnchor.Price.stageHyp_chain n hn r h1 h2
  have hR1 := h.hR.2
  have hSR := h.hSR
  have hz := h.hz
  have hu := h.hu
  have hκR : (R n : ℝ)*κ ≤ 311/400*κ := mul_le_mul_of_nonneg_right hR1 hκ0.le
  have hκS : ((1-(R n : ℝ))/2 + gain n)*κ ≤ 137/1000*κ :=
    mul_le_mul_of_nonneg_right hSR hκ0.le
  have hβκ : β*κ ≤ 1/1000*κ := mul_le_mul_of_nonneg_right hβ1 hκ0.le
  have hR0 := h.hR.1
  exact inverse_child_stage_u canonicalFamily canonicalFamily_subClosed (R n) (gain n) (cut n) r
    (1/25000000) β κ h.R_pos h.hr.2 h.k_pos (by norm_num) hβ0 hκ0 (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) hprev hhigh

/-- The same with the previous anchor given as `AnchorAt`. -/
theorem chain_inverse_child_of_anchor (n : ℕ) (hn : n < 176) (r : ℝ) (h1 : (left n : ℝ) ≤ r)
    (h2 : r ≤ R n) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1/1000) (κ : ℝ) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ β/8) (hA : AnchorAt (R n) (gain n))
    (hhigh : InverseHighEnergy canonicalFamily (chainChildRect n r β κ) (cut n)
      (chainExcess n r κ)) :
    UniformInverseRectSourceExcess canonicalFamily (chainChildRect n r β κ)
      (chainExcess n r κ) :=
  chain_inverse_child n hn r h1 h2 β hβ0 hβ1 κ hκ0 hκ1 (fun δ' hδ' => (hA δ' hδ').1) hhigh

end
end Qrh.MarkedAnchor.Inverse.Leaf

#print axioms Qrh.MarkedAnchor.Inverse.Leaf.chain_inverse_child
#print axioms Qrh.MarkedAnchor.Inverse.Leaf.chain_inverse_child_of_anchor
