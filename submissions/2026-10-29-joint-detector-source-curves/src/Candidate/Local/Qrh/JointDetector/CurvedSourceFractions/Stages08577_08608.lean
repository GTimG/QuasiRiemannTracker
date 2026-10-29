/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08577_08608
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97970926928341,97970589846333,97970252743129,97969915618731,97969578473139,97969241306354,97968904118376,97968566909206,97968229678845,97967892427293,97967555154551,97967217860620,97966880545500,97966543209192,97966205851697,97965868473015,97965531073147,97965193652093,97964856209855,97964518746432,97964181261826,97963843756037,97963506229066,97963168680914,97962831111581,97962493521067,97962155909374,97961818276502,97961480622452,97961142947224,97960805250819,97960467533238,97960129794481]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8576+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8577 := params 0
abbrev ray8577 := rays 0
def bank8577 : Fin 2 → Cell := twoBank p8577 ray8577
theorem signs8577 : ∀ j, Signs p8577 (bank8577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8578 := params 1
abbrev ray8578 := rays 1
def bank8578 : Fin 2 → Cell := twoBank p8578 ray8578
theorem signs8578 : ∀ j, Signs p8578 (bank8578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8579 := params 2
abbrev ray8579 := rays 2
def bank8579 : Fin 2 → Cell := twoBank p8579 ray8579
theorem signs8579 : ∀ j, Signs p8579 (bank8579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8580 := params 3
abbrev ray8580 := rays 3
def bank8580 : Fin 2 → Cell := twoBank p8580 ray8580
theorem signs8580 : ∀ j, Signs p8580 (bank8580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8581 := params 4
abbrev ray8581 := rays 4
def bank8581 : Fin 2 → Cell := twoBank p8581 ray8581
theorem signs8581 : ∀ j, Signs p8581 (bank8581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8582 := params 5
abbrev ray8582 := rays 5
def bank8582 : Fin 2 → Cell := twoBank p8582 ray8582
theorem signs8582 : ∀ j, Signs p8582 (bank8582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8583 := params 6
abbrev ray8583 := rays 6
def bank8583 : Fin 2 → Cell := twoBank p8583 ray8583
theorem signs8583 : ∀ j, Signs p8583 (bank8583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8584 := params 7
abbrev ray8584 := rays 7
def bank8584 : Fin 2 → Cell := twoBank p8584 ray8584
theorem signs8584 : ∀ j, Signs p8584 (bank8584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8585 := params 8
abbrev ray8585 := rays 8
def bank8585 : Fin 2 → Cell := twoBank p8585 ray8585
theorem signs8585 : ∀ j, Signs p8585 (bank8585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8586 := params 9
abbrev ray8586 := rays 9
def bank8586 : Fin 2 → Cell := twoBank p8586 ray8586
theorem signs8586 : ∀ j, Signs p8586 (bank8586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8587 := params 10
abbrev ray8587 := rays 10
def bank8587 : Fin 2 → Cell := twoBank p8587 ray8587
theorem signs8587 : ∀ j, Signs p8587 (bank8587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8588 := params 11
abbrev ray8588 := rays 11
def bank8588 : Fin 2 → Cell := twoBank p8588 ray8588
theorem signs8588 : ∀ j, Signs p8588 (bank8588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8589 := params 12
abbrev ray8589 := rays 12
def bank8589 : Fin 2 → Cell := twoBank p8589 ray8589
theorem signs8589 : ∀ j, Signs p8589 (bank8589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8590 := params 13
abbrev ray8590 := rays 13
def bank8590 : Fin 2 → Cell := twoBank p8590 ray8590
theorem signs8590 : ∀ j, Signs p8590 (bank8590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8591 := params 14
abbrev ray8591 := rays 14
def bank8591 : Fin 2 → Cell := twoBank p8591 ray8591
theorem signs8591 : ∀ j, Signs p8591 (bank8591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8592 := params 15
abbrev ray8592 := rays 15
def bank8592 : Fin 2 → Cell := twoBank p8592 ray8592
theorem signs8592 : ∀ j, Signs p8592 (bank8592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8593 := params 16
abbrev ray8593 := rays 16
def bank8593 : Fin 2 → Cell := twoBank p8593 ray8593
theorem signs8593 : ∀ j, Signs p8593 (bank8593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8594 := params 17
abbrev ray8594 := rays 17
def bank8594 : Fin 2 → Cell := twoBank p8594 ray8594
theorem signs8594 : ∀ j, Signs p8594 (bank8594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8595 := params 18
abbrev ray8595 := rays 18
def bank8595 : Fin 2 → Cell := twoBank p8595 ray8595
theorem signs8595 : ∀ j, Signs p8595 (bank8595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8596 := params 19
abbrev ray8596 := rays 19
def bank8596 : Fin 2 → Cell := twoBank p8596 ray8596
theorem signs8596 : ∀ j, Signs p8596 (bank8596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8597 := params 20
abbrev ray8597 := rays 20
def bank8597 : Fin 2 → Cell := twoBank p8597 ray8597
theorem signs8597 : ∀ j, Signs p8597 (bank8597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8598 := params 21
abbrev ray8598 := rays 21
def bank8598 : Fin 2 → Cell := twoBank p8598 ray8598
theorem signs8598 : ∀ j, Signs p8598 (bank8598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8599 := params 22
abbrev ray8599 := rays 22
def bank8599 : Fin 2 → Cell := twoBank p8599 ray8599
theorem signs8599 : ∀ j, Signs p8599 (bank8599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8600 := params 23
abbrev ray8600 := rays 23
def bank8600 : Fin 2 → Cell := twoBank p8600 ray8600
theorem signs8600 : ∀ j, Signs p8600 (bank8600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8601 := params 24
abbrev ray8601 := rays 24
def bank8601 : Fin 2 → Cell := twoBank p8601 ray8601
theorem signs8601 : ∀ j, Signs p8601 (bank8601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8602 := params 25
abbrev ray8602 := rays 25
def bank8602 : Fin 2 → Cell := twoBank p8602 ray8602
theorem signs8602 : ∀ j, Signs p8602 (bank8602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8603 := params 26
abbrev ray8603 := rays 26
def bank8603 : Fin 2 → Cell := twoBank p8603 ray8603
theorem signs8603 : ∀ j, Signs p8603 (bank8603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8604 := params 27
abbrev ray8604 := rays 27
def bank8604 : Fin 2 → Cell := twoBank p8604 ray8604
theorem signs8604 : ∀ j, Signs p8604 (bank8604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8605 := params 28
abbrev ray8605 := rays 28
def bank8605 : Fin 2 → Cell := twoBank p8605 ray8605
theorem signs8605 : ∀ j, Signs p8605 (bank8605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8606 := params 29
abbrev ray8606 := rays 29
def bank8606 : Fin 2 → Cell := twoBank p8606 ray8606
theorem signs8606 : ∀ j, Signs p8606 (bank8606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8607 := params 30
abbrev ray8607 := rays 30
def bank8607 : Fin 2 → Cell := twoBank p8607 ray8607
theorem signs8607 : ∀ j, Signs p8607 (bank8607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8608 := params 31
abbrev ray8608 := rays 31
def bank8608 : Fin 2 → Cell := twoBank p8608 ray8608
theorem signs8608 : ∀ j, Signs p8608 (bank8608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08577_08608
