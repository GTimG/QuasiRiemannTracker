/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15617_15648
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95113557775298,95113090543355,95112623295400,95112156031433,95111688751455,95111221455466,95110754143465,95110286815453,95109819471430,95109352111396,95108884735350,95108417343293,95107949935226,95107482511148,95107015071059,95106547614959,95106080142848,95105612654727,95105145150595,95104677630453,95104210094300,95103742542137,95103274973963,95102807389779,95102339789585,95101872173381,95101404541167,95100936892943,95100469228709,95100001548465,95099533852211,95099066139947,95098598411674]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15616+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15617 := params 0
abbrev ray15617 := rays 0
def bank15617 : Fin 1 → Cell := oneBank p15617 ray15617
theorem signs15617 : ∀ j, Signs p15617 (bank15617 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15618 := params 1
abbrev ray15618 := rays 1
def bank15618 : Fin 1 → Cell := oneBank p15618 ray15618
theorem signs15618 : ∀ j, Signs p15618 (bank15618 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15619 := params 2
abbrev ray15619 := rays 2
def bank15619 : Fin 1 → Cell := oneBank p15619 ray15619
theorem signs15619 : ∀ j, Signs p15619 (bank15619 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15620 := params 3
abbrev ray15620 := rays 3
def bank15620 : Fin 1 → Cell := oneBank p15620 ray15620
theorem signs15620 : ∀ j, Signs p15620 (bank15620 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15621 := params 4
abbrev ray15621 := rays 4
def bank15621 : Fin 1 → Cell := oneBank p15621 ray15621
theorem signs15621 : ∀ j, Signs p15621 (bank15621 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15622 := params 5
abbrev ray15622 := rays 5
def bank15622 : Fin 1 → Cell := oneBank p15622 ray15622
theorem signs15622 : ∀ j, Signs p15622 (bank15622 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15623 := params 6
abbrev ray15623 := rays 6
def bank15623 : Fin 1 → Cell := oneBank p15623 ray15623
theorem signs15623 : ∀ j, Signs p15623 (bank15623 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15624 := params 7
abbrev ray15624 := rays 7
def bank15624 : Fin 1 → Cell := oneBank p15624 ray15624
theorem signs15624 : ∀ j, Signs p15624 (bank15624 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15625 := params 8
abbrev ray15625 := rays 8
def bank15625 : Fin 1 → Cell := oneBank p15625 ray15625
theorem signs15625 : ∀ j, Signs p15625 (bank15625 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15626 := params 9
abbrev ray15626 := rays 9
def bank15626 : Fin 1 → Cell := oneBank p15626 ray15626
theorem signs15626 : ∀ j, Signs p15626 (bank15626 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15627 := params 10
abbrev ray15627 := rays 10
def bank15627 : Fin 1 → Cell := oneBank p15627 ray15627
theorem signs15627 : ∀ j, Signs p15627 (bank15627 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15628 := params 11
abbrev ray15628 := rays 11
def bank15628 : Fin 1 → Cell := oneBank p15628 ray15628
theorem signs15628 : ∀ j, Signs p15628 (bank15628 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15629 := params 12
abbrev ray15629 := rays 12
def bank15629 : Fin 1 → Cell := oneBank p15629 ray15629
theorem signs15629 : ∀ j, Signs p15629 (bank15629 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15630 := params 13
abbrev ray15630 := rays 13
def bank15630 : Fin 1 → Cell := oneBank p15630 ray15630
theorem signs15630 : ∀ j, Signs p15630 (bank15630 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15631 := params 14
abbrev ray15631 := rays 14
def bank15631 : Fin 1 → Cell := oneBank p15631 ray15631
theorem signs15631 : ∀ j, Signs p15631 (bank15631 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15632 := params 15
abbrev ray15632 := rays 15
def bank15632 : Fin 1 → Cell := oneBank p15632 ray15632
theorem signs15632 : ∀ j, Signs p15632 (bank15632 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15633 := params 16
abbrev ray15633 := rays 16
def bank15633 : Fin 1 → Cell := oneBank p15633 ray15633
theorem signs15633 : ∀ j, Signs p15633 (bank15633 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15634 := params 17
abbrev ray15634 := rays 17
def bank15634 : Fin 1 → Cell := oneBank p15634 ray15634
theorem signs15634 : ∀ j, Signs p15634 (bank15634 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15635 := params 18
abbrev ray15635 := rays 18
def bank15635 : Fin 1 → Cell := oneBank p15635 ray15635
theorem signs15635 : ∀ j, Signs p15635 (bank15635 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15636 := params 19
abbrev ray15636 := rays 19
def bank15636 : Fin 1 → Cell := oneBank p15636 ray15636
theorem signs15636 : ∀ j, Signs p15636 (bank15636 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15637 := params 20
abbrev ray15637 := rays 20
def bank15637 : Fin 1 → Cell := oneBank p15637 ray15637
theorem signs15637 : ∀ j, Signs p15637 (bank15637 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15638 := params 21
abbrev ray15638 := rays 21
def bank15638 : Fin 1 → Cell := oneBank p15638 ray15638
theorem signs15638 : ∀ j, Signs p15638 (bank15638 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15639 := params 22
abbrev ray15639 := rays 22
def bank15639 : Fin 1 → Cell := oneBank p15639 ray15639
theorem signs15639 : ∀ j, Signs p15639 (bank15639 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15640 := params 23
abbrev ray15640 := rays 23
def bank15640 : Fin 1 → Cell := oneBank p15640 ray15640
theorem signs15640 : ∀ j, Signs p15640 (bank15640 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15641 := params 24
abbrev ray15641 := rays 24
def bank15641 : Fin 1 → Cell := oneBank p15641 ray15641
theorem signs15641 : ∀ j, Signs p15641 (bank15641 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15642 := params 25
abbrev ray15642 := rays 25
def bank15642 : Fin 1 → Cell := oneBank p15642 ray15642
theorem signs15642 : ∀ j, Signs p15642 (bank15642 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15643 := params 26
abbrev ray15643 := rays 26
def bank15643 : Fin 1 → Cell := oneBank p15643 ray15643
theorem signs15643 : ∀ j, Signs p15643 (bank15643 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15644 := params 27
abbrev ray15644 := rays 27
def bank15644 : Fin 1 → Cell := oneBank p15644 ray15644
theorem signs15644 : ∀ j, Signs p15644 (bank15644 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15645 := params 28
abbrev ray15645 := rays 28
def bank15645 : Fin 1 → Cell := oneBank p15645 ray15645
theorem signs15645 : ∀ j, Signs p15645 (bank15645 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15646 := params 29
abbrev ray15646 := rays 29
def bank15646 : Fin 1 → Cell := oneBank p15646 ray15646
theorem signs15646 : ∀ j, Signs p15646 (bank15646 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15647 := params 30
abbrev ray15647 := rays 30
def bank15647 : Fin 1 → Cell := oneBank p15647 ray15647
theorem signs15647 : ∀ j, Signs p15647 (bank15647 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15648 := params 31
abbrev ray15648 := rays 31
def bank15648 : Fin 1 → Cell := oneBank p15648 ray15648
theorem signs15648 : ∀ j, Signs p15648 (bank15648 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15617_15648
