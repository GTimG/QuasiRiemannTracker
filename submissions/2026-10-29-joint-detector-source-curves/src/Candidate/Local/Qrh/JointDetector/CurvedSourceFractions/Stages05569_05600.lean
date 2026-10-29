/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05569_05600
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98885696420382,98885426436251,98885156428565,98884886397325,98884616342532,98884346264187,98884076162290,98883806036843,98883535887846,98883265715301,98882995519208,98882725299569,98882455056384,98882184789654,98881914499380,98881644185563,98881373848204,98881103487304,98880833102864,98880562694885,98880292263368,98880021808313,98879751329722,98879480827595,98879210301934,98878939752739,98878669180011,98878398583752,98878127963962,98877857320642,98877586653793,98877315963416,98877045249512]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5568+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5569 := params 0
abbrev ray5569 := rays 0
def bank5569 : Fin 2 → Cell := twoBank p5569 ray5569
theorem signs5569 : ∀ j, Signs p5569 (bank5569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5570 := params 1
abbrev ray5570 := rays 1
def bank5570 : Fin 2 → Cell := twoBank p5570 ray5570
theorem signs5570 : ∀ j, Signs p5570 (bank5570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5571 := params 2
abbrev ray5571 := rays 2
def bank5571 : Fin 2 → Cell := twoBank p5571 ray5571
theorem signs5571 : ∀ j, Signs p5571 (bank5571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5572 := params 3
abbrev ray5572 := rays 3
def bank5572 : Fin 2 → Cell := twoBank p5572 ray5572
theorem signs5572 : ∀ j, Signs p5572 (bank5572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5573 := params 4
abbrev ray5573 := rays 4
def bank5573 : Fin 2 → Cell := twoBank p5573 ray5573
theorem signs5573 : ∀ j, Signs p5573 (bank5573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5574 := params 5
abbrev ray5574 := rays 5
def bank5574 : Fin 2 → Cell := twoBank p5574 ray5574
theorem signs5574 : ∀ j, Signs p5574 (bank5574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5575 := params 6
abbrev ray5575 := rays 6
def bank5575 : Fin 2 → Cell := twoBank p5575 ray5575
theorem signs5575 : ∀ j, Signs p5575 (bank5575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5576 := params 7
abbrev ray5576 := rays 7
def bank5576 : Fin 2 → Cell := twoBank p5576 ray5576
theorem signs5576 : ∀ j, Signs p5576 (bank5576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5577 := params 8
abbrev ray5577 := rays 8
def bank5577 : Fin 2 → Cell := twoBank p5577 ray5577
theorem signs5577 : ∀ j, Signs p5577 (bank5577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5578 := params 9
abbrev ray5578 := rays 9
def bank5578 : Fin 2 → Cell := twoBank p5578 ray5578
theorem signs5578 : ∀ j, Signs p5578 (bank5578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5579 := params 10
abbrev ray5579 := rays 10
def bank5579 : Fin 2 → Cell := twoBank p5579 ray5579
theorem signs5579 : ∀ j, Signs p5579 (bank5579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5580 := params 11
abbrev ray5580 := rays 11
def bank5580 : Fin 2 → Cell := twoBank p5580 ray5580
theorem signs5580 : ∀ j, Signs p5580 (bank5580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5581 := params 12
abbrev ray5581 := rays 12
def bank5581 : Fin 2 → Cell := twoBank p5581 ray5581
theorem signs5581 : ∀ j, Signs p5581 (bank5581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5582 := params 13
abbrev ray5582 := rays 13
def bank5582 : Fin 2 → Cell := twoBank p5582 ray5582
theorem signs5582 : ∀ j, Signs p5582 (bank5582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5583 := params 14
abbrev ray5583 := rays 14
def bank5583 : Fin 2 → Cell := twoBank p5583 ray5583
theorem signs5583 : ∀ j, Signs p5583 (bank5583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5584 := params 15
abbrev ray5584 := rays 15
def bank5584 : Fin 2 → Cell := twoBank p5584 ray5584
theorem signs5584 : ∀ j, Signs p5584 (bank5584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5585 := params 16
abbrev ray5585 := rays 16
def bank5585 : Fin 2 → Cell := twoBank p5585 ray5585
theorem signs5585 : ∀ j, Signs p5585 (bank5585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5586 := params 17
abbrev ray5586 := rays 17
def bank5586 : Fin 2 → Cell := twoBank p5586 ray5586
theorem signs5586 : ∀ j, Signs p5586 (bank5586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5587 := params 18
abbrev ray5587 := rays 18
def bank5587 : Fin 2 → Cell := twoBank p5587 ray5587
theorem signs5587 : ∀ j, Signs p5587 (bank5587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5588 := params 19
abbrev ray5588 := rays 19
def bank5588 : Fin 2 → Cell := twoBank p5588 ray5588
theorem signs5588 : ∀ j, Signs p5588 (bank5588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5589 := params 20
abbrev ray5589 := rays 20
def bank5589 : Fin 2 → Cell := twoBank p5589 ray5589
theorem signs5589 : ∀ j, Signs p5589 (bank5589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5590 := params 21
abbrev ray5590 := rays 21
def bank5590 : Fin 2 → Cell := twoBank p5590 ray5590
theorem signs5590 : ∀ j, Signs p5590 (bank5590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5591 := params 22
abbrev ray5591 := rays 22
def bank5591 : Fin 2 → Cell := twoBank p5591 ray5591
theorem signs5591 : ∀ j, Signs p5591 (bank5591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5592 := params 23
abbrev ray5592 := rays 23
def bank5592 : Fin 2 → Cell := twoBank p5592 ray5592
theorem signs5592 : ∀ j, Signs p5592 (bank5592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5593 := params 24
abbrev ray5593 := rays 24
def bank5593 : Fin 2 → Cell := twoBank p5593 ray5593
theorem signs5593 : ∀ j, Signs p5593 (bank5593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5594 := params 25
abbrev ray5594 := rays 25
def bank5594 : Fin 2 → Cell := twoBank p5594 ray5594
theorem signs5594 : ∀ j, Signs p5594 (bank5594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5595 := params 26
abbrev ray5595 := rays 26
def bank5595 : Fin 2 → Cell := twoBank p5595 ray5595
theorem signs5595 : ∀ j, Signs p5595 (bank5595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5596 := params 27
abbrev ray5596 := rays 27
def bank5596 : Fin 2 → Cell := twoBank p5596 ray5596
theorem signs5596 : ∀ j, Signs p5596 (bank5596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5597 := params 28
abbrev ray5597 := rays 28
def bank5597 : Fin 2 → Cell := twoBank p5597 ray5597
theorem signs5597 : ∀ j, Signs p5597 (bank5597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5598 := params 29
abbrev ray5598 := rays 29
def bank5598 : Fin 2 → Cell := twoBank p5598 ray5598
theorem signs5598 : ∀ j, Signs p5598 (bank5598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5599 := params 30
abbrev ray5599 := rays 30
def bank5599 : Fin 2 → Cell := twoBank p5599 ray5599
theorem signs5599 : ∀ j, Signs p5599 (bank5599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5600 := params 31
abbrev ray5600 := rays 31
def bank5600 : Fin 2 → Cell := twoBank p5600 ray5600
theorem signs5600 : ∀ j, Signs p5600 (bank5600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05569_05600
