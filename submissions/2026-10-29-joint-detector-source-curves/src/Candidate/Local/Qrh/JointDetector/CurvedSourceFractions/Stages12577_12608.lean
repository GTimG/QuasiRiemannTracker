/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12577_12608
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96459304776948,96458887410357,96458470024651,96458052619829,96457635195892,96457217752841,96456800290676,96456382809397,96455965309004,96455547789499,96455130250881,96454712693151,96454295116309,96453877520356,96453459905292,96453042271117,96452624617832,96452206945437,96451789253933,96451371543320,96450953813598,96450536064768,96450118296831,96449700509786,96449282703634,96448864878376,96448447034011,96448029170541,96447611287965,96447193386284,96446775465499,96446357525610,96445939566617]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12576+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12577 := params 0
abbrev ray12577 := rays 0
def bank12577 : Fin 2 → Cell := twoBank p12577 ray12577
theorem signs12577 : ∀ j, Signs p12577 (bank12577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12578 := params 1
abbrev ray12578 := rays 1
def bank12578 : Fin 2 → Cell := twoBank p12578 ray12578
theorem signs12578 : ∀ j, Signs p12578 (bank12578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12579 := params 2
abbrev ray12579 := rays 2
def bank12579 : Fin 2 → Cell := twoBank p12579 ray12579
theorem signs12579 : ∀ j, Signs p12579 (bank12579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12580 := params 3
abbrev ray12580 := rays 3
def bank12580 : Fin 2 → Cell := twoBank p12580 ray12580
theorem signs12580 : ∀ j, Signs p12580 (bank12580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12581 := params 4
abbrev ray12581 := rays 4
def bank12581 : Fin 2 → Cell := twoBank p12581 ray12581
theorem signs12581 : ∀ j, Signs p12581 (bank12581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12582 := params 5
abbrev ray12582 := rays 5
def bank12582 : Fin 2 → Cell := twoBank p12582 ray12582
theorem signs12582 : ∀ j, Signs p12582 (bank12582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12583 := params 6
abbrev ray12583 := rays 6
def bank12583 : Fin 2 → Cell := twoBank p12583 ray12583
theorem signs12583 : ∀ j, Signs p12583 (bank12583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12584 := params 7
abbrev ray12584 := rays 7
def bank12584 : Fin 2 → Cell := twoBank p12584 ray12584
theorem signs12584 : ∀ j, Signs p12584 (bank12584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12585 := params 8
abbrev ray12585 := rays 8
def bank12585 : Fin 2 → Cell := twoBank p12585 ray12585
theorem signs12585 : ∀ j, Signs p12585 (bank12585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12586 := params 9
abbrev ray12586 := rays 9
def bank12586 : Fin 2 → Cell := twoBank p12586 ray12586
theorem signs12586 : ∀ j, Signs p12586 (bank12586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12587 := params 10
abbrev ray12587 := rays 10
def bank12587 : Fin 2 → Cell := twoBank p12587 ray12587
theorem signs12587 : ∀ j, Signs p12587 (bank12587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12588 := params 11
abbrev ray12588 := rays 11
def bank12588 : Fin 2 → Cell := twoBank p12588 ray12588
theorem signs12588 : ∀ j, Signs p12588 (bank12588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12589 := params 12
abbrev ray12589 := rays 12
def bank12589 : Fin 2 → Cell := twoBank p12589 ray12589
theorem signs12589 : ∀ j, Signs p12589 (bank12589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12590 := params 13
abbrev ray12590 := rays 13
def bank12590 : Fin 2 → Cell := twoBank p12590 ray12590
theorem signs12590 : ∀ j, Signs p12590 (bank12590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12591 := params 14
abbrev ray12591 := rays 14
def bank12591 : Fin 2 → Cell := twoBank p12591 ray12591
theorem signs12591 : ∀ j, Signs p12591 (bank12591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12592 := params 15
abbrev ray12592 := rays 15
def bank12592 : Fin 2 → Cell := twoBank p12592 ray12592
theorem signs12592 : ∀ j, Signs p12592 (bank12592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12593 := params 16
abbrev ray12593 := rays 16
def bank12593 : Fin 2 → Cell := twoBank p12593 ray12593
theorem signs12593 : ∀ j, Signs p12593 (bank12593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12594 := params 17
abbrev ray12594 := rays 17
def bank12594 : Fin 2 → Cell := twoBank p12594 ray12594
theorem signs12594 : ∀ j, Signs p12594 (bank12594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12595 := params 18
abbrev ray12595 := rays 18
def bank12595 : Fin 2 → Cell := twoBank p12595 ray12595
theorem signs12595 : ∀ j, Signs p12595 (bank12595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12596 := params 19
abbrev ray12596 := rays 19
def bank12596 : Fin 2 → Cell := twoBank p12596 ray12596
theorem signs12596 : ∀ j, Signs p12596 (bank12596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12597 := params 20
abbrev ray12597 := rays 20
def bank12597 : Fin 2 → Cell := twoBank p12597 ray12597
theorem signs12597 : ∀ j, Signs p12597 (bank12597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12598 := params 21
abbrev ray12598 := rays 21
def bank12598 : Fin 2 → Cell := twoBank p12598 ray12598
theorem signs12598 : ∀ j, Signs p12598 (bank12598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12599 := params 22
abbrev ray12599 := rays 22
def bank12599 : Fin 2 → Cell := twoBank p12599 ray12599
theorem signs12599 : ∀ j, Signs p12599 (bank12599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12600 := params 23
abbrev ray12600 := rays 23
def bank12600 : Fin 2 → Cell := twoBank p12600 ray12600
theorem signs12600 : ∀ j, Signs p12600 (bank12600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12601 := params 24
abbrev ray12601 := rays 24
def bank12601 : Fin 2 → Cell := twoBank p12601 ray12601
theorem signs12601 : ∀ j, Signs p12601 (bank12601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12602 := params 25
abbrev ray12602 := rays 25
def bank12602 : Fin 2 → Cell := twoBank p12602 ray12602
theorem signs12602 : ∀ j, Signs p12602 (bank12602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12603 := params 26
abbrev ray12603 := rays 26
def bank12603 : Fin 2 → Cell := twoBank p12603 ray12603
theorem signs12603 : ∀ j, Signs p12603 (bank12603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12604 := params 27
abbrev ray12604 := rays 27
def bank12604 : Fin 2 → Cell := twoBank p12604 ray12604
theorem signs12604 : ∀ j, Signs p12604 (bank12604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12605 := params 28
abbrev ray12605 := rays 28
def bank12605 : Fin 2 → Cell := twoBank p12605 ray12605
theorem signs12605 : ∀ j, Signs p12605 (bank12605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12606 := params 29
abbrev ray12606 := rays 29
def bank12606 : Fin 2 → Cell := twoBank p12606 ray12606
theorem signs12606 : ∀ j, Signs p12606 (bank12606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12607 := params 30
abbrev ray12607 := rays 30
def bank12607 : Fin 2 → Cell := twoBank p12607 ray12607
theorem signs12607 : ∀ j, Signs p12607 (bank12607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12608 := params 31
abbrev ray12608 := rays 31
def bank12608 : Fin 2 → Cell := twoBank p12608 ray12608
theorem signs12608 : ∀ j, Signs p12608 (bank12608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12577_12608
