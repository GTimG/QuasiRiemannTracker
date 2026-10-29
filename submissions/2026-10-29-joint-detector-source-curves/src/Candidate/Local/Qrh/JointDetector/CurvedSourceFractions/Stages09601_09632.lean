/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09601_09632
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97614766807643,97614408351345,97614049874483,97613691377059,97613332859072,97612974320523,97612615761413,97612257181743,97611898581513,97611539960723,97611181319374,97610822657467,97610463975002,97610105271980,97609746548402,97609387804268,97609029039579,97608670254335,97608311448537,97607952622185,97607593775280,97607234907822,97606876019813,97606517111252,97606158182141,97605799232479,97605440262268,97605081271508,97604722260199,97604363228343,97604004175939,97603645102989,97603286009493]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9600+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9601 := params 0
abbrev ray9601 := rays 0
def bank9601 : Fin 2 → Cell := twoBank p9601 ray9601
theorem signs9601 : ∀ j, Signs p9601 (bank9601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9602 := params 1
abbrev ray9602 := rays 1
def bank9602 : Fin 2 → Cell := twoBank p9602 ray9602
theorem signs9602 : ∀ j, Signs p9602 (bank9602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9603 := params 2
abbrev ray9603 := rays 2
def bank9603 : Fin 2 → Cell := twoBank p9603 ray9603
theorem signs9603 : ∀ j, Signs p9603 (bank9603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9604 := params 3
abbrev ray9604 := rays 3
def bank9604 : Fin 2 → Cell := twoBank p9604 ray9604
theorem signs9604 : ∀ j, Signs p9604 (bank9604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9605 := params 4
abbrev ray9605 := rays 4
def bank9605 : Fin 2 → Cell := twoBank p9605 ray9605
theorem signs9605 : ∀ j, Signs p9605 (bank9605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9606 := params 5
abbrev ray9606 := rays 5
def bank9606 : Fin 2 → Cell := twoBank p9606 ray9606
theorem signs9606 : ∀ j, Signs p9606 (bank9606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9607 := params 6
abbrev ray9607 := rays 6
def bank9607 : Fin 2 → Cell := twoBank p9607 ray9607
theorem signs9607 : ∀ j, Signs p9607 (bank9607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9608 := params 7
abbrev ray9608 := rays 7
def bank9608 : Fin 2 → Cell := twoBank p9608 ray9608
theorem signs9608 : ∀ j, Signs p9608 (bank9608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9609 := params 8
abbrev ray9609 := rays 8
def bank9609 : Fin 2 → Cell := twoBank p9609 ray9609
theorem signs9609 : ∀ j, Signs p9609 (bank9609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9610 := params 9
abbrev ray9610 := rays 9
def bank9610 : Fin 2 → Cell := twoBank p9610 ray9610
theorem signs9610 : ∀ j, Signs p9610 (bank9610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9611 := params 10
abbrev ray9611 := rays 10
def bank9611 : Fin 2 → Cell := twoBank p9611 ray9611
theorem signs9611 : ∀ j, Signs p9611 (bank9611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9612 := params 11
abbrev ray9612 := rays 11
def bank9612 : Fin 2 → Cell := twoBank p9612 ray9612
theorem signs9612 : ∀ j, Signs p9612 (bank9612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9613 := params 12
abbrev ray9613 := rays 12
def bank9613 : Fin 2 → Cell := twoBank p9613 ray9613
theorem signs9613 : ∀ j, Signs p9613 (bank9613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9614 := params 13
abbrev ray9614 := rays 13
def bank9614 : Fin 2 → Cell := twoBank p9614 ray9614
theorem signs9614 : ∀ j, Signs p9614 (bank9614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9615 := params 14
abbrev ray9615 := rays 14
def bank9615 : Fin 2 → Cell := twoBank p9615 ray9615
theorem signs9615 : ∀ j, Signs p9615 (bank9615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9616 := params 15
abbrev ray9616 := rays 15
def bank9616 : Fin 2 → Cell := twoBank p9616 ray9616
theorem signs9616 : ∀ j, Signs p9616 (bank9616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9617 := params 16
abbrev ray9617 := rays 16
def bank9617 : Fin 2 → Cell := twoBank p9617 ray9617
theorem signs9617 : ∀ j, Signs p9617 (bank9617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9618 := params 17
abbrev ray9618 := rays 17
def bank9618 : Fin 2 → Cell := twoBank p9618 ray9618
theorem signs9618 : ∀ j, Signs p9618 (bank9618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9619 := params 18
abbrev ray9619 := rays 18
def bank9619 : Fin 2 → Cell := twoBank p9619 ray9619
theorem signs9619 : ∀ j, Signs p9619 (bank9619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9620 := params 19
abbrev ray9620 := rays 19
def bank9620 : Fin 2 → Cell := twoBank p9620 ray9620
theorem signs9620 : ∀ j, Signs p9620 (bank9620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9621 := params 20
abbrev ray9621 := rays 20
def bank9621 : Fin 2 → Cell := twoBank p9621 ray9621
theorem signs9621 : ∀ j, Signs p9621 (bank9621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9622 := params 21
abbrev ray9622 := rays 21
def bank9622 : Fin 2 → Cell := twoBank p9622 ray9622
theorem signs9622 : ∀ j, Signs p9622 (bank9622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9623 := params 22
abbrev ray9623 := rays 22
def bank9623 : Fin 2 → Cell := twoBank p9623 ray9623
theorem signs9623 : ∀ j, Signs p9623 (bank9623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9624 := params 23
abbrev ray9624 := rays 23
def bank9624 : Fin 2 → Cell := twoBank p9624 ray9624
theorem signs9624 : ∀ j, Signs p9624 (bank9624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9625 := params 24
abbrev ray9625 := rays 24
def bank9625 : Fin 2 → Cell := twoBank p9625 ray9625
theorem signs9625 : ∀ j, Signs p9625 (bank9625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9626 := params 25
abbrev ray9626 := rays 25
def bank9626 : Fin 2 → Cell := twoBank p9626 ray9626
theorem signs9626 : ∀ j, Signs p9626 (bank9626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9627 := params 26
abbrev ray9627 := rays 26
def bank9627 : Fin 2 → Cell := twoBank p9627 ray9627
theorem signs9627 : ∀ j, Signs p9627 (bank9627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9628 := params 27
abbrev ray9628 := rays 27
def bank9628 : Fin 2 → Cell := twoBank p9628 ray9628
theorem signs9628 : ∀ j, Signs p9628 (bank9628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9629 := params 28
abbrev ray9629 := rays 28
def bank9629 : Fin 2 → Cell := twoBank p9629 ray9629
theorem signs9629 : ∀ j, Signs p9629 (bank9629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9630 := params 29
abbrev ray9630 := rays 29
def bank9630 : Fin 2 → Cell := twoBank p9630 ray9630
theorem signs9630 : ∀ j, Signs p9630 (bank9630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9631 := params 30
abbrev ray9631 := rays 30
def bank9631 : Fin 2 → Cell := twoBank p9631 ray9631
theorem signs9631 : ∀ j, Signs p9631 (bank9631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9632 := params 31
abbrev ray9632 := rays 31
def bank9632 : Fin 2 → Cell := twoBank p9632 ray9632
theorem signs9632 : ∀ j, Signs p9632 (bank9632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09601_09632
