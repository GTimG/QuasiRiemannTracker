/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07585_07616
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98294763012947,98294447291921,98294131549011,98293815784218,98293499997543,98293184188986,98292868358548,98292552506230,98292236632033,98291920735957,98291604818003,98291288878172,98290972916464,98290656932880,98290340927421,98290024900088,98289708850882,98289392779803,98289076686852,98288760572029,98288444435336,98288128276773,98287812096341,98287495894040,98287179669872,98286863423837,98286547155935,98286230866168,98285914554536,98285598221040,98285281865681,98284965488459,98284649089375]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7584+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7585 := params 0
abbrev ray7585 := rays 0
def bank7585 : Fin 2 → Cell := twoBank p7585 ray7585
theorem signs7585 : ∀ j, Signs p7585 (bank7585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7586 := params 1
abbrev ray7586 := rays 1
def bank7586 : Fin 2 → Cell := twoBank p7586 ray7586
theorem signs7586 : ∀ j, Signs p7586 (bank7586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7587 := params 2
abbrev ray7587 := rays 2
def bank7587 : Fin 2 → Cell := twoBank p7587 ray7587
theorem signs7587 : ∀ j, Signs p7587 (bank7587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7588 := params 3
abbrev ray7588 := rays 3
def bank7588 : Fin 2 → Cell := twoBank p7588 ray7588
theorem signs7588 : ∀ j, Signs p7588 (bank7588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7589 := params 4
abbrev ray7589 := rays 4
def bank7589 : Fin 2 → Cell := twoBank p7589 ray7589
theorem signs7589 : ∀ j, Signs p7589 (bank7589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7590 := params 5
abbrev ray7590 := rays 5
def bank7590 : Fin 2 → Cell := twoBank p7590 ray7590
theorem signs7590 : ∀ j, Signs p7590 (bank7590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7591 := params 6
abbrev ray7591 := rays 6
def bank7591 : Fin 2 → Cell := twoBank p7591 ray7591
theorem signs7591 : ∀ j, Signs p7591 (bank7591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7592 := params 7
abbrev ray7592 := rays 7
def bank7592 : Fin 2 → Cell := twoBank p7592 ray7592
theorem signs7592 : ∀ j, Signs p7592 (bank7592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7593 := params 8
abbrev ray7593 := rays 8
def bank7593 : Fin 2 → Cell := twoBank p7593 ray7593
theorem signs7593 : ∀ j, Signs p7593 (bank7593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7594 := params 9
abbrev ray7594 := rays 9
def bank7594 : Fin 2 → Cell := twoBank p7594 ray7594
theorem signs7594 : ∀ j, Signs p7594 (bank7594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7595 := params 10
abbrev ray7595 := rays 10
def bank7595 : Fin 2 → Cell := twoBank p7595 ray7595
theorem signs7595 : ∀ j, Signs p7595 (bank7595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7596 := params 11
abbrev ray7596 := rays 11
def bank7596 : Fin 2 → Cell := twoBank p7596 ray7596
theorem signs7596 : ∀ j, Signs p7596 (bank7596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7597 := params 12
abbrev ray7597 := rays 12
def bank7597 : Fin 2 → Cell := twoBank p7597 ray7597
theorem signs7597 : ∀ j, Signs p7597 (bank7597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7598 := params 13
abbrev ray7598 := rays 13
def bank7598 : Fin 2 → Cell := twoBank p7598 ray7598
theorem signs7598 : ∀ j, Signs p7598 (bank7598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7599 := params 14
abbrev ray7599 := rays 14
def bank7599 : Fin 2 → Cell := twoBank p7599 ray7599
theorem signs7599 : ∀ j, Signs p7599 (bank7599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7600 := params 15
abbrev ray7600 := rays 15
def bank7600 : Fin 2 → Cell := twoBank p7600 ray7600
theorem signs7600 : ∀ j, Signs p7600 (bank7600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7601 := params 16
abbrev ray7601 := rays 16
def bank7601 : Fin 2 → Cell := twoBank p7601 ray7601
theorem signs7601 : ∀ j, Signs p7601 (bank7601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7602 := params 17
abbrev ray7602 := rays 17
def bank7602 : Fin 2 → Cell := twoBank p7602 ray7602
theorem signs7602 : ∀ j, Signs p7602 (bank7602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7603 := params 18
abbrev ray7603 := rays 18
def bank7603 : Fin 2 → Cell := twoBank p7603 ray7603
theorem signs7603 : ∀ j, Signs p7603 (bank7603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7604 := params 19
abbrev ray7604 := rays 19
def bank7604 : Fin 2 → Cell := twoBank p7604 ray7604
theorem signs7604 : ∀ j, Signs p7604 (bank7604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7605 := params 20
abbrev ray7605 := rays 20
def bank7605 : Fin 2 → Cell := twoBank p7605 ray7605
theorem signs7605 : ∀ j, Signs p7605 (bank7605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7606 := params 21
abbrev ray7606 := rays 21
def bank7606 : Fin 2 → Cell := twoBank p7606 ray7606
theorem signs7606 : ∀ j, Signs p7606 (bank7606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7607 := params 22
abbrev ray7607 := rays 22
def bank7607 : Fin 2 → Cell := twoBank p7607 ray7607
theorem signs7607 : ∀ j, Signs p7607 (bank7607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7608 := params 23
abbrev ray7608 := rays 23
def bank7608 : Fin 2 → Cell := twoBank p7608 ray7608
theorem signs7608 : ∀ j, Signs p7608 (bank7608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7609 := params 24
abbrev ray7609 := rays 24
def bank7609 : Fin 2 → Cell := twoBank p7609 ray7609
theorem signs7609 : ∀ j, Signs p7609 (bank7609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7610 := params 25
abbrev ray7610 := rays 25
def bank7610 : Fin 2 → Cell := twoBank p7610 ray7610
theorem signs7610 : ∀ j, Signs p7610 (bank7610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7611 := params 26
abbrev ray7611 := rays 26
def bank7611 : Fin 2 → Cell := twoBank p7611 ray7611
theorem signs7611 : ∀ j, Signs p7611 (bank7611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7612 := params 27
abbrev ray7612 := rays 27
def bank7612 : Fin 2 → Cell := twoBank p7612 ray7612
theorem signs7612 : ∀ j, Signs p7612 (bank7612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7613 := params 28
abbrev ray7613 := rays 28
def bank7613 : Fin 2 → Cell := twoBank p7613 ray7613
theorem signs7613 : ∀ j, Signs p7613 (bank7613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7614 := params 29
abbrev ray7614 := rays 29
def bank7614 : Fin 2 → Cell := twoBank p7614 ray7614
theorem signs7614 : ∀ j, Signs p7614 (bank7614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7615 := params 30
abbrev ray7615 := rays 30
def bank7615 : Fin 2 → Cell := twoBank p7615 ray7615
theorem signs7615 : ∀ j, Signs p7615 (bank7615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7616 := params 31
abbrev ray7616 := rays 31
def bank7616 : Fin 2 → Cell := twoBank p7616 ray7616
theorem signs7616 : ∀ j, Signs p7616 (bank7616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07585_07616
