/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16641_16672
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94626733964148,94626250357007,94625766733881,94625283094771,94624799439677,94624315768598,94623832081535,94623348378487,94622864659455,94622380924438,94621897173437,94621413406452,94620929623482,94620445824528,94619962009589,94619478178666,94618994331758,94618510468865,94618026589988,94617542695126,94617058784280,94616574857449,94616090914633,94615606955833,94615122981048,94614638990279,94614154983525,94613670960786,94613186922062,94612702867354,94612218796661,94611734709983,94611250607320]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16640+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16641 := params 0
abbrev ray16641 := rays 0
def bank16641 : Fin 1 → Cell := oneBank p16641 ray16641
theorem signs16641 : ∀ j, Signs p16641 (bank16641 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16642 := params 1
abbrev ray16642 := rays 1
def bank16642 : Fin 1 → Cell := oneBank p16642 ray16642
theorem signs16642 : ∀ j, Signs p16642 (bank16642 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16643 := params 2
abbrev ray16643 := rays 2
def bank16643 : Fin 1 → Cell := oneBank p16643 ray16643
theorem signs16643 : ∀ j, Signs p16643 (bank16643 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16644 := params 3
abbrev ray16644 := rays 3
def bank16644 : Fin 1 → Cell := oneBank p16644 ray16644
theorem signs16644 : ∀ j, Signs p16644 (bank16644 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16645 := params 4
abbrev ray16645 := rays 4
def bank16645 : Fin 1 → Cell := oneBank p16645 ray16645
theorem signs16645 : ∀ j, Signs p16645 (bank16645 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16646 := params 5
abbrev ray16646 := rays 5
def bank16646 : Fin 1 → Cell := oneBank p16646 ray16646
theorem signs16646 : ∀ j, Signs p16646 (bank16646 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16647 := params 6
abbrev ray16647 := rays 6
def bank16647 : Fin 1 → Cell := oneBank p16647 ray16647
theorem signs16647 : ∀ j, Signs p16647 (bank16647 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16648 := params 7
abbrev ray16648 := rays 7
def bank16648 : Fin 1 → Cell := oneBank p16648 ray16648
theorem signs16648 : ∀ j, Signs p16648 (bank16648 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16649 := params 8
abbrev ray16649 := rays 8
def bank16649 : Fin 1 → Cell := oneBank p16649 ray16649
theorem signs16649 : ∀ j, Signs p16649 (bank16649 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16650 := params 9
abbrev ray16650 := rays 9
def bank16650 : Fin 1 → Cell := oneBank p16650 ray16650
theorem signs16650 : ∀ j, Signs p16650 (bank16650 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16651 := params 10
abbrev ray16651 := rays 10
def bank16651 : Fin 1 → Cell := oneBank p16651 ray16651
theorem signs16651 : ∀ j, Signs p16651 (bank16651 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16652 := params 11
abbrev ray16652 := rays 11
def bank16652 : Fin 1 → Cell := oneBank p16652 ray16652
theorem signs16652 : ∀ j, Signs p16652 (bank16652 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16653 := params 12
abbrev ray16653 := rays 12
def bank16653 : Fin 1 → Cell := oneBank p16653 ray16653
theorem signs16653 : ∀ j, Signs p16653 (bank16653 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16654 := params 13
abbrev ray16654 := rays 13
def bank16654 : Fin 1 → Cell := oneBank p16654 ray16654
theorem signs16654 : ∀ j, Signs p16654 (bank16654 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16655 := params 14
abbrev ray16655 := rays 14
def bank16655 : Fin 1 → Cell := oneBank p16655 ray16655
theorem signs16655 : ∀ j, Signs p16655 (bank16655 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16656 := params 15
abbrev ray16656 := rays 15
def bank16656 : Fin 1 → Cell := oneBank p16656 ray16656
theorem signs16656 : ∀ j, Signs p16656 (bank16656 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16657 := params 16
abbrev ray16657 := rays 16
def bank16657 : Fin 1 → Cell := oneBank p16657 ray16657
theorem signs16657 : ∀ j, Signs p16657 (bank16657 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16658 := params 17
abbrev ray16658 := rays 17
def bank16658 : Fin 1 → Cell := oneBank p16658 ray16658
theorem signs16658 : ∀ j, Signs p16658 (bank16658 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16659 := params 18
abbrev ray16659 := rays 18
def bank16659 : Fin 1 → Cell := oneBank p16659 ray16659
theorem signs16659 : ∀ j, Signs p16659 (bank16659 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16660 := params 19
abbrev ray16660 := rays 19
def bank16660 : Fin 1 → Cell := oneBank p16660 ray16660
theorem signs16660 : ∀ j, Signs p16660 (bank16660 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16661 := params 20
abbrev ray16661 := rays 20
def bank16661 : Fin 1 → Cell := oneBank p16661 ray16661
theorem signs16661 : ∀ j, Signs p16661 (bank16661 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16662 := params 21
abbrev ray16662 := rays 21
def bank16662 : Fin 1 → Cell := oneBank p16662 ray16662
theorem signs16662 : ∀ j, Signs p16662 (bank16662 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16663 := params 22
abbrev ray16663 := rays 22
def bank16663 : Fin 1 → Cell := oneBank p16663 ray16663
theorem signs16663 : ∀ j, Signs p16663 (bank16663 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16664 := params 23
abbrev ray16664 := rays 23
def bank16664 : Fin 1 → Cell := oneBank p16664 ray16664
theorem signs16664 : ∀ j, Signs p16664 (bank16664 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16665 := params 24
abbrev ray16665 := rays 24
def bank16665 : Fin 1 → Cell := oneBank p16665 ray16665
theorem signs16665 : ∀ j, Signs p16665 (bank16665 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16666 := params 25
abbrev ray16666 := rays 25
def bank16666 : Fin 1 → Cell := oneBank p16666 ray16666
theorem signs16666 : ∀ j, Signs p16666 (bank16666 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16667 := params 26
abbrev ray16667 := rays 26
def bank16667 : Fin 1 → Cell := oneBank p16667 ray16667
theorem signs16667 : ∀ j, Signs p16667 (bank16667 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16668 := params 27
abbrev ray16668 := rays 27
def bank16668 : Fin 1 → Cell := oneBank p16668 ray16668
theorem signs16668 : ∀ j, Signs p16668 (bank16668 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16669 := params 28
abbrev ray16669 := rays 28
def bank16669 : Fin 1 → Cell := oneBank p16669 ray16669
theorem signs16669 : ∀ j, Signs p16669 (bank16669 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16670 := params 29
abbrev ray16670 := rays 29
def bank16670 : Fin 1 → Cell := oneBank p16670 ray16670
theorem signs16670 : ∀ j, Signs p16670 (bank16670 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16671 := params 30
abbrev ray16671 := rays 30
def bank16671 : Fin 1 → Cell := oneBank p16671 ray16671
theorem signs16671 : ∀ j, Signs p16671 (bank16671 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16672 := params 31
abbrev ray16672 := rays 31
def bank16672 : Fin 1 → Cell := oneBank p16672 ray16672
theorem signs16672 : ∀ j, Signs p16672 (bank16672 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16641_16672
