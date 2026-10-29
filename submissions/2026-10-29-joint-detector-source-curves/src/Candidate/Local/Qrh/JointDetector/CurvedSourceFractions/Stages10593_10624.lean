/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10593_10624
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97249161906063,97248783325178,97248404724273,97248026103348,97247647462403,97247268801439,97246890120457,97246511419457,97246132698440,97245753957406,97245375196355,97244996415288,97244617614206,97244238793109,97243859951998,97243481090873,97243102209735,97242723308584,97242344387421,97241965446246,97241586485060,97241207503863,97240828502656,97240449481439,97240070440213,97239691378978,97239312297735,97238933196484,97238554075226,97238174933962,97237795772692,97237416591416,97237037390135]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10592+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10593 := params 0
abbrev ray10593 := rays 0
def bank10593 : Fin 2 → Cell := twoBank p10593 ray10593
theorem signs10593 : ∀ j, Signs p10593 (bank10593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10594 := params 1
abbrev ray10594 := rays 1
def bank10594 : Fin 2 → Cell := twoBank p10594 ray10594
theorem signs10594 : ∀ j, Signs p10594 (bank10594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10595 := params 2
abbrev ray10595 := rays 2
def bank10595 : Fin 2 → Cell := twoBank p10595 ray10595
theorem signs10595 : ∀ j, Signs p10595 (bank10595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10596 := params 3
abbrev ray10596 := rays 3
def bank10596 : Fin 2 → Cell := twoBank p10596 ray10596
theorem signs10596 : ∀ j, Signs p10596 (bank10596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10597 := params 4
abbrev ray10597 := rays 4
def bank10597 : Fin 2 → Cell := twoBank p10597 ray10597
theorem signs10597 : ∀ j, Signs p10597 (bank10597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10598 := params 5
abbrev ray10598 := rays 5
def bank10598 : Fin 2 → Cell := twoBank p10598 ray10598
theorem signs10598 : ∀ j, Signs p10598 (bank10598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10599 := params 6
abbrev ray10599 := rays 6
def bank10599 : Fin 2 → Cell := twoBank p10599 ray10599
theorem signs10599 : ∀ j, Signs p10599 (bank10599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10600 := params 7
abbrev ray10600 := rays 7
def bank10600 : Fin 2 → Cell := twoBank p10600 ray10600
theorem signs10600 : ∀ j, Signs p10600 (bank10600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10601 := params 8
abbrev ray10601 := rays 8
def bank10601 : Fin 2 → Cell := twoBank p10601 ray10601
theorem signs10601 : ∀ j, Signs p10601 (bank10601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10602 := params 9
abbrev ray10602 := rays 9
def bank10602 : Fin 2 → Cell := twoBank p10602 ray10602
theorem signs10602 : ∀ j, Signs p10602 (bank10602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10603 := params 10
abbrev ray10603 := rays 10
def bank10603 : Fin 2 → Cell := twoBank p10603 ray10603
theorem signs10603 : ∀ j, Signs p10603 (bank10603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10604 := params 11
abbrev ray10604 := rays 11
def bank10604 : Fin 2 → Cell := twoBank p10604 ray10604
theorem signs10604 : ∀ j, Signs p10604 (bank10604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10605 := params 12
abbrev ray10605 := rays 12
def bank10605 : Fin 2 → Cell := twoBank p10605 ray10605
theorem signs10605 : ∀ j, Signs p10605 (bank10605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10606 := params 13
abbrev ray10606 := rays 13
def bank10606 : Fin 2 → Cell := twoBank p10606 ray10606
theorem signs10606 : ∀ j, Signs p10606 (bank10606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10607 := params 14
abbrev ray10607 := rays 14
def bank10607 : Fin 2 → Cell := twoBank p10607 ray10607
theorem signs10607 : ∀ j, Signs p10607 (bank10607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10608 := params 15
abbrev ray10608 := rays 15
def bank10608 : Fin 2 → Cell := twoBank p10608 ray10608
theorem signs10608 : ∀ j, Signs p10608 (bank10608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10609 := params 16
abbrev ray10609 := rays 16
def bank10609 : Fin 2 → Cell := twoBank p10609 ray10609
theorem signs10609 : ∀ j, Signs p10609 (bank10609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10610 := params 17
abbrev ray10610 := rays 17
def bank10610 : Fin 2 → Cell := twoBank p10610 ray10610
theorem signs10610 : ∀ j, Signs p10610 (bank10610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10611 := params 18
abbrev ray10611 := rays 18
def bank10611 : Fin 2 → Cell := twoBank p10611 ray10611
theorem signs10611 : ∀ j, Signs p10611 (bank10611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10612 := params 19
abbrev ray10612 := rays 19
def bank10612 : Fin 2 → Cell := twoBank p10612 ray10612
theorem signs10612 : ∀ j, Signs p10612 (bank10612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10613 := params 20
abbrev ray10613 := rays 20
def bank10613 : Fin 2 → Cell := twoBank p10613 ray10613
theorem signs10613 : ∀ j, Signs p10613 (bank10613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10614 := params 21
abbrev ray10614 := rays 21
def bank10614 : Fin 2 → Cell := twoBank p10614 ray10614
theorem signs10614 : ∀ j, Signs p10614 (bank10614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10615 := params 22
abbrev ray10615 := rays 22
def bank10615 : Fin 2 → Cell := twoBank p10615 ray10615
theorem signs10615 : ∀ j, Signs p10615 (bank10615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10616 := params 23
abbrev ray10616 := rays 23
def bank10616 : Fin 2 → Cell := twoBank p10616 ray10616
theorem signs10616 : ∀ j, Signs p10616 (bank10616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10617 := params 24
abbrev ray10617 := rays 24
def bank10617 : Fin 2 → Cell := twoBank p10617 ray10617
theorem signs10617 : ∀ j, Signs p10617 (bank10617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10618 := params 25
abbrev ray10618 := rays 25
def bank10618 : Fin 2 → Cell := twoBank p10618 ray10618
theorem signs10618 : ∀ j, Signs p10618 (bank10618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10619 := params 26
abbrev ray10619 := rays 26
def bank10619 : Fin 2 → Cell := twoBank p10619 ray10619
theorem signs10619 : ∀ j, Signs p10619 (bank10619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10620 := params 27
abbrev ray10620 := rays 27
def bank10620 : Fin 2 → Cell := twoBank p10620 ray10620
theorem signs10620 : ∀ j, Signs p10620 (bank10620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10621 := params 28
abbrev ray10621 := rays 28
def bank10621 : Fin 2 → Cell := twoBank p10621 ray10621
theorem signs10621 : ∀ j, Signs p10621 (bank10621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10622 := params 29
abbrev ray10622 := rays 29
def bank10622 : Fin 2 → Cell := twoBank p10622 ray10622
theorem signs10622 : ∀ j, Signs p10622 (bank10622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10623 := params 30
abbrev ray10623 := rays 30
def bank10623 : Fin 2 → Cell := twoBank p10623 ray10623
theorem signs10623 : ∀ j, Signs p10623 (bank10623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10624 := params 31
abbrev ray10624 := rays 31
def bank10624 : Fin 2 → Cell := twoBank p10624 ray10624
theorem signs10624 : ∀ j, Signs p10624 (bank10624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10593_10624
