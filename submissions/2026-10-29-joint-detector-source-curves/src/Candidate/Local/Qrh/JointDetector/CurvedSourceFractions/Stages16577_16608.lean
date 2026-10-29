/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16577_16608
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94657651574222,94657168990058,94656686389910,94656203773778,94655721141663,94655238493564,94654755829481,94654273149414,94653790453364,94653307741330,94652825013312,94652342269310,94651859509324,94651376733355,94650893941402,94650411133465,94649928309544,94649445469639,94648962613750,94648479741877,94647996854021,94647513950181,94647031030357,94646548094549,94646065142757,94645582174981,94645099191221,94644616191477,94644133175749,94643650144037,94643167096341,94642684032661,94642200952997]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16576+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16577 := params 0
abbrev ray16577 := rays 0
def bank16577 : Fin 1 → Cell := oneBank p16577 ray16577
theorem signs16577 : ∀ j, Signs p16577 (bank16577 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16578 := params 1
abbrev ray16578 := rays 1
def bank16578 : Fin 1 → Cell := oneBank p16578 ray16578
theorem signs16578 : ∀ j, Signs p16578 (bank16578 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16579 := params 2
abbrev ray16579 := rays 2
def bank16579 : Fin 1 → Cell := oneBank p16579 ray16579
theorem signs16579 : ∀ j, Signs p16579 (bank16579 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16580 := params 3
abbrev ray16580 := rays 3
def bank16580 : Fin 1 → Cell := oneBank p16580 ray16580
theorem signs16580 : ∀ j, Signs p16580 (bank16580 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16581 := params 4
abbrev ray16581 := rays 4
def bank16581 : Fin 1 → Cell := oneBank p16581 ray16581
theorem signs16581 : ∀ j, Signs p16581 (bank16581 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16582 := params 5
abbrev ray16582 := rays 5
def bank16582 : Fin 1 → Cell := oneBank p16582 ray16582
theorem signs16582 : ∀ j, Signs p16582 (bank16582 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16583 := params 6
abbrev ray16583 := rays 6
def bank16583 : Fin 1 → Cell := oneBank p16583 ray16583
theorem signs16583 : ∀ j, Signs p16583 (bank16583 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16584 := params 7
abbrev ray16584 := rays 7
def bank16584 : Fin 1 → Cell := oneBank p16584 ray16584
theorem signs16584 : ∀ j, Signs p16584 (bank16584 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16585 := params 8
abbrev ray16585 := rays 8
def bank16585 : Fin 1 → Cell := oneBank p16585 ray16585
theorem signs16585 : ∀ j, Signs p16585 (bank16585 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16586 := params 9
abbrev ray16586 := rays 9
def bank16586 : Fin 1 → Cell := oneBank p16586 ray16586
theorem signs16586 : ∀ j, Signs p16586 (bank16586 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16587 := params 10
abbrev ray16587 := rays 10
def bank16587 : Fin 1 → Cell := oneBank p16587 ray16587
theorem signs16587 : ∀ j, Signs p16587 (bank16587 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16588 := params 11
abbrev ray16588 := rays 11
def bank16588 : Fin 1 → Cell := oneBank p16588 ray16588
theorem signs16588 : ∀ j, Signs p16588 (bank16588 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16589 := params 12
abbrev ray16589 := rays 12
def bank16589 : Fin 1 → Cell := oneBank p16589 ray16589
theorem signs16589 : ∀ j, Signs p16589 (bank16589 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16590 := params 13
abbrev ray16590 := rays 13
def bank16590 : Fin 1 → Cell := oneBank p16590 ray16590
theorem signs16590 : ∀ j, Signs p16590 (bank16590 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16591 := params 14
abbrev ray16591 := rays 14
def bank16591 : Fin 1 → Cell := oneBank p16591 ray16591
theorem signs16591 : ∀ j, Signs p16591 (bank16591 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16592 := params 15
abbrev ray16592 := rays 15
def bank16592 : Fin 1 → Cell := oneBank p16592 ray16592
theorem signs16592 : ∀ j, Signs p16592 (bank16592 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16593 := params 16
abbrev ray16593 := rays 16
def bank16593 : Fin 1 → Cell := oneBank p16593 ray16593
theorem signs16593 : ∀ j, Signs p16593 (bank16593 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16594 := params 17
abbrev ray16594 := rays 17
def bank16594 : Fin 1 → Cell := oneBank p16594 ray16594
theorem signs16594 : ∀ j, Signs p16594 (bank16594 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16595 := params 18
abbrev ray16595 := rays 18
def bank16595 : Fin 1 → Cell := oneBank p16595 ray16595
theorem signs16595 : ∀ j, Signs p16595 (bank16595 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16596 := params 19
abbrev ray16596 := rays 19
def bank16596 : Fin 1 → Cell := oneBank p16596 ray16596
theorem signs16596 : ∀ j, Signs p16596 (bank16596 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16597 := params 20
abbrev ray16597 := rays 20
def bank16597 : Fin 1 → Cell := oneBank p16597 ray16597
theorem signs16597 : ∀ j, Signs p16597 (bank16597 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16598 := params 21
abbrev ray16598 := rays 21
def bank16598 : Fin 1 → Cell := oneBank p16598 ray16598
theorem signs16598 : ∀ j, Signs p16598 (bank16598 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16599 := params 22
abbrev ray16599 := rays 22
def bank16599 : Fin 1 → Cell := oneBank p16599 ray16599
theorem signs16599 : ∀ j, Signs p16599 (bank16599 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16600 := params 23
abbrev ray16600 := rays 23
def bank16600 : Fin 1 → Cell := oneBank p16600 ray16600
theorem signs16600 : ∀ j, Signs p16600 (bank16600 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16601 := params 24
abbrev ray16601 := rays 24
def bank16601 : Fin 1 → Cell := oneBank p16601 ray16601
theorem signs16601 : ∀ j, Signs p16601 (bank16601 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16602 := params 25
abbrev ray16602 := rays 25
def bank16602 : Fin 1 → Cell := oneBank p16602 ray16602
theorem signs16602 : ∀ j, Signs p16602 (bank16602 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16603 := params 26
abbrev ray16603 := rays 26
def bank16603 : Fin 1 → Cell := oneBank p16603 ray16603
theorem signs16603 : ∀ j, Signs p16603 (bank16603 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16604 := params 27
abbrev ray16604 := rays 27
def bank16604 : Fin 1 → Cell := oneBank p16604 ray16604
theorem signs16604 : ∀ j, Signs p16604 (bank16604 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16605 := params 28
abbrev ray16605 := rays 28
def bank16605 : Fin 1 → Cell := oneBank p16605 ray16605
theorem signs16605 : ∀ j, Signs p16605 (bank16605 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16606 := params 29
abbrev ray16606 := rays 29
def bank16606 : Fin 1 → Cell := oneBank p16606 ray16606
theorem signs16606 : ∀ j, Signs p16606 (bank16606 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16607 := params 30
abbrev ray16607 := rays 30
def bank16607 : Fin 1 → Cell := oneBank p16607 ray16607
theorem signs16607 : ∀ j, Signs p16607 (bank16607 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16608 := params 31
abbrev ray16608 := rays 31
def bank16608 : Fin 1 → Cell := oneBank p16608 ray16608
theorem signs16608 : ∀ j, Signs p16608 (bank16608 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16577_16608
