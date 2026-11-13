/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ToleranceSources
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafBranch

/-! Transport the variable source pad to the existing selected-width interface
by an exact change of line intercept. The witness shift remains explicit in the
physical fiber count and localization theorems. -/

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum.Tolerances
noncomputable section

def intercept (q a0 : ℝ) : ℝ := a0 + 1/10000000000000 - sourcePad q

theorem cap_recenter (q a0 a1 x : ℝ) :
    max 0 ((1-x)/2+(intercept q a0-a1*x)-1/10000000000000) =
      max 0 ((1-x)/2+(a0-a1*x)-sourcePad q) := by
  congr 1
  unfold intercept
  ring

theorem sig_recenter (q a0 a1 x : ℝ) :
    Qrh.TwoSlot.AnchorZeroLoss.High.sig (intercept q a0) a1 x = sig q a0 a1 x :=
  cap_recenter q a0 a1 x

/-- The generic exponential price and the explicit coupled-tolerance ledger
are the same function at the chosen local witness shift. -/
theorem parametric_price_eq
    [shift : Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift]
    (a0 a1 ν e w P S M : ℝ) :
    Qrh.TwoSlot.AnchorZeroLoss.High.detEx
      (intercept Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift.value a0) a1 ν e w P S M =
      detEx Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift.value a0 a1 ν e w P S M := by
  unfold Qrh.TwoSlot.AnchorZeroLoss.High.detEx
    Qrh.TwoSlot.AnchorZeroLoss.High.shortCnt
    Qrh.TwoSlot.AnchorZeroLoss.High.longCnt
    detEx shortCnt longCnt
  rw [sig_recenter]

/-- The physical marked input is unchanged by recentering the line: no
coefficient, mask, profile, selected subset or height is changed. -/
theorem marked_input_recenter {q a0 a1 wlo : ℝ}
    (h : Qrh.TwoSlot.AnchorZeroLoss.High.HighMarkedCoreInputsH
      a0 a1 wlo (sourcePad q) q) :
    Qrh.TwoSlot.AnchorZeroLoss.High.HighMarkedCoreInputsH
      (intercept q a0) a1 wlo (1/10000000000000) q := by
  unfold Qrh.TwoSlot.AnchorZeroLoss.High.HighMarkedCoreInputsH at h ⊢
  simpa only [cap_recenter] using h

/-- The same intercept transport before introducing supported witnesses. This
form supplies the complete paired core input consumed by the inverse leaf. -/
theorem marked_core_recenter {q a0 a1 wlo : ℝ}
    (h : Qrh.TwoSlot.AnchorZeroLoss.High.Marked.MarkedCoreR1
      a0 a1 wlo (sourcePad q) q) :
    Qrh.TwoSlot.AnchorZeroLoss.High.Marked.MarkedCoreR1
      (intercept q a0) a1 wlo (1/10000000000000) q := by
  unfold Qrh.TwoSlot.AnchorZeroLoss.High.Marked.MarkedCoreR1
    Qrh.TwoSlot.AnchorZeroLoss.High.Marked.InvMarkedField
    Qrh.TwoSlot.AnchorZeroLoss.High.Marked.PlainMarkedField at h ⊢
  simpa only [cap_recenter] using h

/-- The actual ordinary HIGH branch supplied by earlier paired anchors, with
one arbitrarily small positive shift shared by the source, witness and consumer.
The early mesh and all physical masks/profiles are inherited from those inputs. -/
theorem high_branch_of_earlier
    [shift : Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift]
    (hβ : (51/100:ℝ) ≤ OAI.SevenEighths.HeckeZeroSupremum.beta)
    (hres : Qrh.MarkedAnchor.Interface.Native.ReserveParametricSource)
    (R T wlo a0 a1 k : ℝ) (hR : R < wlo) (hwlo : 0 ≤ wlo)
    (hTlo : 3/4 ≤ T) (hThi : T ≤ 7/9)
    (ha : 0 ≤ a1) (ha1 : a1 ≤ 2/5) (hl : a0-a1*T ≤ 0)
    (hk0 : 1/6 ≤ k) (hk1 : k ≤ 3/4)
    (hlo : wlo ≤ Qrh.TwoSlot.AnchorZeroLoss.High.cutHi)
    (hprior : ∀ r : ℝ, R < r → r ≤ T → ∃ z : ℝ, 0 ≤ z ∧ a0-a1*r ≤ z ∧
      Qrh.MarkedAnchor.Interface.Contract.AnchorAt r z) :
    Qrh.TwoSlot.AnchorZeroLoss.High.HighBranchMesh
      (Qrh.TwoSlot.AnchorZeroLoss.High.highPriceW
        (intercept Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift.value a0) a1 k wlo
        (by linarith) hk1) k := by
  have hM := highMarkedCoreInputs_of_earlier hβ hres
    Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift.pos
    Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift.le_fixed
    R T wlo a0 a1 hR hwlo hTlo hThi ha ha1 hl hprior
  exact Qrh.TwoSlot.AnchorZeroLoss.High.high_branch_mesh hβ hk0 hk1 hlo ha
    (by linarith) (marked_input_recenter hM)

/-- Exact identification of the physical fiber rate with the coupled-tolerance
detector price. This is an identity, not a numerical domination of endpoints. -/
theorem fiber_price_eq (q a0 a1 ν e w P S : ℝ) :
    ν*P + e*S +
      Qrh.TwoSlot.AnchorZeroLoss.High.fiberTarget (intercept q a0) a1 ν e w S q - 1 =
        detEx q a0 a1 ν e w P S 1 := by
  simp only [Qrh.TwoSlot.AnchorZeroLoss.High.fiberTarget,
    Qrh.TwoSlot.AnchorZeroLoss.High.selW, sig_recenter,
    detEx, shortCnt, longCnt, mul_one, one_mul]
  rw [min_comm S (sig q a0 a1 w)]

end
end Qrh.TwoSlot.AnchorContinuum.Tolerances
