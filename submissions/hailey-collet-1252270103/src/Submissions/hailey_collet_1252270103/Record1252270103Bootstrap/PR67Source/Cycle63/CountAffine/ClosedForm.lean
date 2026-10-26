import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The detector count in which the critical plain witness is controlled by the interior affine
moment (Collet, Cycle61 Theorem 2.2). The count-side use of that moment follows liqsweep's
proposal in tracker PR #52; this file adapts it to the computed affine constants of this source.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.CountAffine
noncomputable section
open Cycle63.Arithmetic

/-- The least inverse length for which the inverse fiber moment with slot capacity `(1 - r)/2`
is used: one minus twice the slot supply `7/37` of the inverse marked moment. -/
def inverseFloor : ℝ := 23/37

/-- The tolerance of the cutoff at the crossing of the two short counts. The count takes the
count error `ε` as the tolerance (`merged_count_bound`), so it is the bound `ε ≤ 1/1000` of the count
contracts. -/
def crossingSlack : ℝ := 1/1000

/-- The least cutoff for which a plain witness below the window forces an inverse witness of
length at least `inverseFloor`. -/
def cutoffFloor : ℝ := inverseFloor + windowBottom + crossingSlack

/-- The least crossing inverse length for which the inverse witness before the crossing is at least
`inverseFloor`. -/
def crossingFloor : ℝ := inverseFloor + crossingSlack

/-! The affine plain line `aP - sP m`, with the slot capacity `(B - 2m)/λ`. -/

def sI (δ p : ℝ) : ℝ := δ - δ*p
def sP (δ p : ℝ) : ℝ := 2*δ - 4*(δ*p)/lambda
def aP (δ p : ℝ) : ℝ := 1 - 2*(δ*p)*B/lambda
def tNum (δ p : ℝ) : ℝ := (1-δ*p)*sP δ p + aP δ p*sI δ p - (sI δ p + sP δ p)/6
def tDen (δ p : ℝ) : ℝ := (5/6-δ)*(sI δ p + sP δ p) + sI δ p*sP δ p
/-- The balanced cutoff of the detector. -/
def tStar (δ p : ℝ) : ℝ := tNum δ p / tDen δ p
/-- The closed-form count. -/
def RStar (δ p : ℝ) : ℝ := 1/6 + (5/6-δ)*tStar δ p
/-- The plain length and inverse length at the crossing of the two short counts. -/
def mC (δ p : ℝ) : ℝ := (aP δ p - 1 + δ*p + sI δ p*tStar δ p)/(sI δ p + sP δ p)
def rC (δ p : ℝ) : ℝ := tStar δ p - mC δ p
/-- Slot capacity supplied by the interior affine moment at plain length `m`. -/
def zS (m : ℝ) : ℝ := min Cycle63.Optimization.slotTop ((B-2*m)/lambda)
def plainNew (δ p m : ℝ) : ℝ := 1 - 2*δ*m - 2*(δ*p)*zS m
def plainOld (κ δ p m : ℝ) : ℝ := 1 - 2*δ*m - 2*(δ*p)*(1-2*m)/(6*κ)
def inverseLine (δ p r : ℝ) : ℝ := 1 - δ*p - sI δ p*r

/-! The capped plain line `aPc - sPc m`, with the slot capacity at the window top `slotTop`. -/

def sPc (δ : ℝ) : ℝ := 2*δ
def aPc (δ p : ℝ) : ℝ := 1 - 2*(δ*p)*Cycle63.Optimization.slotTop
def tNumC (δ p : ℝ) : ℝ := (1-δ*p)*sPc δ + aPc δ p*sI δ p - (sI δ p + sPc δ)/6
def tDenC (δ p : ℝ) : ℝ := (5/6-δ)*(sI δ p + sPc δ) + sI δ p*sPc δ
/-- The balanced cutoff of the capped line. -/
def tStarC (δ p : ℝ) : ℝ := tNumC δ p / tDenC δ p
/-- The closed-form count of the capped line. -/
def RStarC (δ p : ℝ) : ℝ := 1/6 + (5/6-δ)*tStarC δ p
/-- Plain and inverse lengths at the crossing of the capped line with the inverse line. -/
def mCC (δ p : ℝ) : ℝ := (aPc δ p - 1 + δ*p + sI δ p*tStarC δ p)/(sI δ p + sPc δ)
def rCC (δ p : ℝ) : ℝ := tStarC δ p - mCC δ p

/-- The new branch count: the larger closed form of the two plain lines, or the old plain moment
just above the window. -/
def newBranch (κ δ p : ℝ) : ℝ := max (max (RStar δ p) (RStarC δ p)) (plainOld κ δ p plainTop)

/-- The rectangle on which the closed forms are used. It contains the binding bin of the top row;
outside it the old count suffices. -/
def inRegion (δ p : ℝ) : Prop := 43/100 ≤ δ ∧ δ ≤ 49/100 ∧ 495/1000 ≤ p ∧ p ≤ 1/2

theorem inRegion_up {δ p p' : ℝ} (h : inRegion δ p) (hp : p ≤ p') (hp' : p' ≤ 1/2) :
    inRegion δ p' :=
  ⟨h.1, h.2.1, by linarith [h.2.2.1], hp'⟩

theorem inRegion_bounds {δ p : ℝ} (h : inRegion δ p) :
    43/100 ≤ δ ∧ δ ≤ 49/100 ∧ 495/1000 ≤ p ∧ p ≤ 1/2 := h

theorem B_bounds : (98/100:ℝ) < B ∧ B < 1 := by
  have hB := Cycle63.Arithmetic.B_bounds
  constructor <;> linarith [hB.1, hB.2]

/-- The slope and the intercept as interval variables, for certificates with enough slack to ignore
their coupling through the bin split. -/
alias lambda_mem := Cycle63.Arithmetic.lambda_bounds

alias B_mem := Cycle63.Arithmetic.B_bounds

/-- The two crossing identities defining the closed form. -/
theorem crossing_identities {δ p : ℝ} (hD : tDen δ p ≠ 0) (hS : sI δ p + sP δ p ≠ 0) :
    inverseLine δ p (rC δ p) = RStar δ p ∧
      aP δ p - sP δ p*mC δ p = RStar δ p := by
  have hl : lambda ≠ 0 := lambda_pos.ne'
  constructor
  · unfold inverseLine rC mC RStar tStar
    field_simp
    unfold tNum tDen
    ring
  · unfold mC RStar tStar
    field_simp
    unfold tNum tDen
    ring

theorem crossing_identitiesC {δ p : ℝ} (hD : tDenC δ p ≠ 0) (hS : sI δ p + sPc δ ≠ 0) :
    inverseLine δ p (rCC δ p) = RStarC δ p ∧
      aPc δ p - sPc δ*mCC δ p = RStarC δ p := by
  constructor
  · unfold inverseLine rCC mCC RStarC tStarC
    field_simp
    unfold tNumC tDenC
    ring
  · unfold mCC RStarC tStarC
    field_simp
    unfold tNumC tDenC
    ring

theorem inverseLine_anti {δ p r r' : ℝ} (hs : 0 ≤ sI δ p) (hr : r ≤ r') :
    inverseLine δ p r' ≤ inverseLine δ p r := by
  unfold inverseLine
  nlinarith

theorem sI_nonneg {δ p : ℝ} (hδ : 0 ≤ δ) (hp : p ≤ 1) : 0 ≤ sI δ p := by
  unfold sI
  nlinarith

theorem plainOld_anti {κ δ p m m' : ℝ} (hk : 7/10 ≤ κ) (hδ : 0 ≤ δ) (hp0 : 0 ≤ p)
    (hp : p ≤ 1/2) (hm : m ≤ m') : plainOld κ δ p m' ≤ plainOld κ δ p m := by
  have hk0 : 0 < 6*κ := by linarith
  have hq : 0 ≤ δ*p := mul_nonneg hδ hp0
  have hqd : δ*p ≤ δ/2 := by nlinarith
  have hid : plainOld κ δ p m - plainOld κ δ p m' =
      (m'-m)*(2*δ - 4*(δ*p)/(6*κ)) := by
    unfold plainOld; field_simp; ring
  have hc : 4*(δ*p)/(6*κ) ≤ 2*δ := by
    rw [div_le_iff₀ hk0]; nlinarith
  have : 0 ≤ (m'-m)*(2*δ - 4*(δ*p)/(6*κ)) := mul_nonneg (by linarith) (by linarith)
  linarith

end
end Cycle63.CountAffine

end Record1252270103Bootstrap.PR67
