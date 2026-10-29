/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11617_11648
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96851097935748,96850699112742,96850300270211,96849901408155,96849502526575,96849103625472,96848704704846,96848305764697,96847906805026,96847507825833,96847108827119,96846709808884,96846310771128,96845911713853,96845512637058,96845113540744,96844714424911,96844315289560,96843916134692,96843516960306,96843117766404,96842718552985,96842319320050,96841920067600,96841520795635,96841121504155,96840722193161,96840322862654,96839923512634,96839524143101,96839124754056,96838725345499,96838325917430]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11616+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11617 := params 0
abbrev ray11617 := rays 0
def bank11617 : Fin 2 → Cell := twoBank p11617 ray11617
theorem signs11617 : ∀ j, Signs p11617 (bank11617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11618 := params 1
abbrev ray11618 := rays 1
def bank11618 : Fin 2 → Cell := twoBank p11618 ray11618
theorem signs11618 : ∀ j, Signs p11618 (bank11618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11619 := params 2
abbrev ray11619 := rays 2
def bank11619 : Fin 2 → Cell := twoBank p11619 ray11619
theorem signs11619 : ∀ j, Signs p11619 (bank11619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11620 := params 3
abbrev ray11620 := rays 3
def bank11620 : Fin 2 → Cell := twoBank p11620 ray11620
theorem signs11620 : ∀ j, Signs p11620 (bank11620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11621 := params 4
abbrev ray11621 := rays 4
def bank11621 : Fin 2 → Cell := twoBank p11621 ray11621
theorem signs11621 : ∀ j, Signs p11621 (bank11621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11622 := params 5
abbrev ray11622 := rays 5
def bank11622 : Fin 2 → Cell := twoBank p11622 ray11622
theorem signs11622 : ∀ j, Signs p11622 (bank11622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11623 := params 6
abbrev ray11623 := rays 6
def bank11623 : Fin 2 → Cell := twoBank p11623 ray11623
theorem signs11623 : ∀ j, Signs p11623 (bank11623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11624 := params 7
abbrev ray11624 := rays 7
def bank11624 : Fin 2 → Cell := twoBank p11624 ray11624
theorem signs11624 : ∀ j, Signs p11624 (bank11624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11625 := params 8
abbrev ray11625 := rays 8
def bank11625 : Fin 2 → Cell := twoBank p11625 ray11625
theorem signs11625 : ∀ j, Signs p11625 (bank11625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11626 := params 9
abbrev ray11626 := rays 9
def bank11626 : Fin 2 → Cell := twoBank p11626 ray11626
theorem signs11626 : ∀ j, Signs p11626 (bank11626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11627 := params 10
abbrev ray11627 := rays 10
def bank11627 : Fin 2 → Cell := twoBank p11627 ray11627
theorem signs11627 : ∀ j, Signs p11627 (bank11627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11628 := params 11
abbrev ray11628 := rays 11
def bank11628 : Fin 2 → Cell := twoBank p11628 ray11628
theorem signs11628 : ∀ j, Signs p11628 (bank11628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11629 := params 12
abbrev ray11629 := rays 12
def bank11629 : Fin 2 → Cell := twoBank p11629 ray11629
theorem signs11629 : ∀ j, Signs p11629 (bank11629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11630 := params 13
abbrev ray11630 := rays 13
def bank11630 : Fin 2 → Cell := twoBank p11630 ray11630
theorem signs11630 : ∀ j, Signs p11630 (bank11630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11631 := params 14
abbrev ray11631 := rays 14
def bank11631 : Fin 2 → Cell := twoBank p11631 ray11631
theorem signs11631 : ∀ j, Signs p11631 (bank11631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11632 := params 15
abbrev ray11632 := rays 15
def bank11632 : Fin 2 → Cell := twoBank p11632 ray11632
theorem signs11632 : ∀ j, Signs p11632 (bank11632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11633 := params 16
abbrev ray11633 := rays 16
def bank11633 : Fin 2 → Cell := twoBank p11633 ray11633
theorem signs11633 : ∀ j, Signs p11633 (bank11633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11634 := params 17
abbrev ray11634 := rays 17
def bank11634 : Fin 2 → Cell := twoBank p11634 ray11634
theorem signs11634 : ∀ j, Signs p11634 (bank11634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11635 := params 18
abbrev ray11635 := rays 18
def bank11635 : Fin 2 → Cell := twoBank p11635 ray11635
theorem signs11635 : ∀ j, Signs p11635 (bank11635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11636 := params 19
abbrev ray11636 := rays 19
def bank11636 : Fin 2 → Cell := twoBank p11636 ray11636
theorem signs11636 : ∀ j, Signs p11636 (bank11636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11637 := params 20
abbrev ray11637 := rays 20
def bank11637 : Fin 2 → Cell := twoBank p11637 ray11637
theorem signs11637 : ∀ j, Signs p11637 (bank11637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11638 := params 21
abbrev ray11638 := rays 21
def bank11638 : Fin 2 → Cell := twoBank p11638 ray11638
theorem signs11638 : ∀ j, Signs p11638 (bank11638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11639 := params 22
abbrev ray11639 := rays 22
def bank11639 : Fin 2 → Cell := twoBank p11639 ray11639
theorem signs11639 : ∀ j, Signs p11639 (bank11639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11640 := params 23
abbrev ray11640 := rays 23
def bank11640 : Fin 2 → Cell := twoBank p11640 ray11640
theorem signs11640 : ∀ j, Signs p11640 (bank11640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11641 := params 24
abbrev ray11641 := rays 24
def bank11641 : Fin 2 → Cell := twoBank p11641 ray11641
theorem signs11641 : ∀ j, Signs p11641 (bank11641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11642 := params 25
abbrev ray11642 := rays 25
def bank11642 : Fin 2 → Cell := twoBank p11642 ray11642
theorem signs11642 : ∀ j, Signs p11642 (bank11642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11643 := params 26
abbrev ray11643 := rays 26
def bank11643 : Fin 2 → Cell := twoBank p11643 ray11643
theorem signs11643 : ∀ j, Signs p11643 (bank11643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11644 := params 27
abbrev ray11644 := rays 27
def bank11644 : Fin 2 → Cell := twoBank p11644 ray11644
theorem signs11644 : ∀ j, Signs p11644 (bank11644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11645 := params 28
abbrev ray11645 := rays 28
def bank11645 : Fin 2 → Cell := twoBank p11645 ray11645
theorem signs11645 : ∀ j, Signs p11645 (bank11645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11646 := params 29
abbrev ray11646 := rays 29
def bank11646 : Fin 2 → Cell := twoBank p11646 ray11646
theorem signs11646 : ∀ j, Signs p11646 (bank11646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11647 := params 30
abbrev ray11647 := rays 30
def bank11647 : Fin 2 → Cell := twoBank p11647 ray11647
theorem signs11647 : ∀ j, Signs p11647 (bank11647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11648 := params 31
abbrev ray11648 := rays 31
def bank11648 : Fin 2 → Cell := twoBank p11648 ray11648
theorem signs11648 : ∀ j, Signs p11648 (bank11648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11617_11648
