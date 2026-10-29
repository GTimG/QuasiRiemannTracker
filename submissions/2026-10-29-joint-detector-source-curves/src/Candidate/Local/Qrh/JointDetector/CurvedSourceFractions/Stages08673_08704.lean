/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08673_08704
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97938470498547,97938131384770,97937792249861,97937453093820,97937113916647,97936774718343,97936435498909,97936096258346,97935756996654,97935417713834,97935078409886,97934739084811,97934399738610,97934060371283,97933720982831,97933381573255,97933042142555,97932702690732,97932363217787,97932023723720,97931684208532,97931344672224,97931005114796,97930665536249,97930325936583,97929986315799,97929646673898,97929307010881,97928967326748,97928627621499,97928287895136,97927948147659,97927608379069]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8672+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8673 := params 0
abbrev ray8673 := rays 0
def bank8673 : Fin 2 → Cell := twoBank p8673 ray8673
theorem signs8673 : ∀ j, Signs p8673 (bank8673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8674 := params 1
abbrev ray8674 := rays 1
def bank8674 : Fin 2 → Cell := twoBank p8674 ray8674
theorem signs8674 : ∀ j, Signs p8674 (bank8674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8675 := params 2
abbrev ray8675 := rays 2
def bank8675 : Fin 2 → Cell := twoBank p8675 ray8675
theorem signs8675 : ∀ j, Signs p8675 (bank8675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8676 := params 3
abbrev ray8676 := rays 3
def bank8676 : Fin 2 → Cell := twoBank p8676 ray8676
theorem signs8676 : ∀ j, Signs p8676 (bank8676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8677 := params 4
abbrev ray8677 := rays 4
def bank8677 : Fin 2 → Cell := twoBank p8677 ray8677
theorem signs8677 : ∀ j, Signs p8677 (bank8677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8678 := params 5
abbrev ray8678 := rays 5
def bank8678 : Fin 2 → Cell := twoBank p8678 ray8678
theorem signs8678 : ∀ j, Signs p8678 (bank8678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8679 := params 6
abbrev ray8679 := rays 6
def bank8679 : Fin 2 → Cell := twoBank p8679 ray8679
theorem signs8679 : ∀ j, Signs p8679 (bank8679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8680 := params 7
abbrev ray8680 := rays 7
def bank8680 : Fin 2 → Cell := twoBank p8680 ray8680
theorem signs8680 : ∀ j, Signs p8680 (bank8680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8681 := params 8
abbrev ray8681 := rays 8
def bank8681 : Fin 2 → Cell := twoBank p8681 ray8681
theorem signs8681 : ∀ j, Signs p8681 (bank8681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8682 := params 9
abbrev ray8682 := rays 9
def bank8682 : Fin 2 → Cell := twoBank p8682 ray8682
theorem signs8682 : ∀ j, Signs p8682 (bank8682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8683 := params 10
abbrev ray8683 := rays 10
def bank8683 : Fin 2 → Cell := twoBank p8683 ray8683
theorem signs8683 : ∀ j, Signs p8683 (bank8683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8684 := params 11
abbrev ray8684 := rays 11
def bank8684 : Fin 2 → Cell := twoBank p8684 ray8684
theorem signs8684 : ∀ j, Signs p8684 (bank8684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8685 := params 12
abbrev ray8685 := rays 12
def bank8685 : Fin 2 → Cell := twoBank p8685 ray8685
theorem signs8685 : ∀ j, Signs p8685 (bank8685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8686 := params 13
abbrev ray8686 := rays 13
def bank8686 : Fin 2 → Cell := twoBank p8686 ray8686
theorem signs8686 : ∀ j, Signs p8686 (bank8686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8687 := params 14
abbrev ray8687 := rays 14
def bank8687 : Fin 2 → Cell := twoBank p8687 ray8687
theorem signs8687 : ∀ j, Signs p8687 (bank8687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8688 := params 15
abbrev ray8688 := rays 15
def bank8688 : Fin 2 → Cell := twoBank p8688 ray8688
theorem signs8688 : ∀ j, Signs p8688 (bank8688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8689 := params 16
abbrev ray8689 := rays 16
def bank8689 : Fin 2 → Cell := twoBank p8689 ray8689
theorem signs8689 : ∀ j, Signs p8689 (bank8689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8690 := params 17
abbrev ray8690 := rays 17
def bank8690 : Fin 2 → Cell := twoBank p8690 ray8690
theorem signs8690 : ∀ j, Signs p8690 (bank8690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8691 := params 18
abbrev ray8691 := rays 18
def bank8691 : Fin 2 → Cell := twoBank p8691 ray8691
theorem signs8691 : ∀ j, Signs p8691 (bank8691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8692 := params 19
abbrev ray8692 := rays 19
def bank8692 : Fin 2 → Cell := twoBank p8692 ray8692
theorem signs8692 : ∀ j, Signs p8692 (bank8692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8693 := params 20
abbrev ray8693 := rays 20
def bank8693 : Fin 2 → Cell := twoBank p8693 ray8693
theorem signs8693 : ∀ j, Signs p8693 (bank8693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8694 := params 21
abbrev ray8694 := rays 21
def bank8694 : Fin 2 → Cell := twoBank p8694 ray8694
theorem signs8694 : ∀ j, Signs p8694 (bank8694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8695 := params 22
abbrev ray8695 := rays 22
def bank8695 : Fin 2 → Cell := twoBank p8695 ray8695
theorem signs8695 : ∀ j, Signs p8695 (bank8695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8696 := params 23
abbrev ray8696 := rays 23
def bank8696 : Fin 2 → Cell := twoBank p8696 ray8696
theorem signs8696 : ∀ j, Signs p8696 (bank8696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8697 := params 24
abbrev ray8697 := rays 24
def bank8697 : Fin 2 → Cell := twoBank p8697 ray8697
theorem signs8697 : ∀ j, Signs p8697 (bank8697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8698 := params 25
abbrev ray8698 := rays 25
def bank8698 : Fin 2 → Cell := twoBank p8698 ray8698
theorem signs8698 : ∀ j, Signs p8698 (bank8698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8699 := params 26
abbrev ray8699 := rays 26
def bank8699 : Fin 2 → Cell := twoBank p8699 ray8699
theorem signs8699 : ∀ j, Signs p8699 (bank8699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8700 := params 27
abbrev ray8700 := rays 27
def bank8700 : Fin 2 → Cell := twoBank p8700 ray8700
theorem signs8700 : ∀ j, Signs p8700 (bank8700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8701 := params 28
abbrev ray8701 := rays 28
def bank8701 : Fin 2 → Cell := twoBank p8701 ray8701
theorem signs8701 : ∀ j, Signs p8701 (bank8701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8702 := params 29
abbrev ray8702 := rays 29
def bank8702 : Fin 2 → Cell := twoBank p8702 ray8702
theorem signs8702 : ∀ j, Signs p8702 (bank8702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8703 := params 30
abbrev ray8703 := rays 30
def bank8703 : Fin 2 → Cell := twoBank p8703 ray8703
theorem signs8703 : ∀ j, Signs p8703 (bank8703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8704 := params 31
abbrev ray8704 := rays 31
def bank8704 : Fin 2 → Cell := twoBank p8704 ray8704
theorem signs8704 : ∀ j, Signs p8704 (bank8704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08673_08704
