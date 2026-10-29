/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15585_15616
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95128500742965,95128034023428,95127567287877,95127100536312,95126633768734,95126166985142,95125700185537,95125233369918,95124766538286,95124299690641,95123832826983,95123365947311,95122899051626,95122432139928,95121965212218,95121498268495,95121031308759,95120564333010,95120097341249,95119630333475,95119163309688,95118696269889,95118229214078,95117762142254,95117295054418,95116827950570,95116360830710,95115893694838,95115426542954,95114959375058,95114492191150,95114024991230,95113557775298]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15584+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15585 := params 0
abbrev ray15585 := rays 0
def bank15585 : Fin 1 → Cell := oneBank p15585 ray15585
theorem signs15585 : ∀ j, Signs p15585 (bank15585 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15586 := params 1
abbrev ray15586 := rays 1
def bank15586 : Fin 1 → Cell := oneBank p15586 ray15586
theorem signs15586 : ∀ j, Signs p15586 (bank15586 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15587 := params 2
abbrev ray15587 := rays 2
def bank15587 : Fin 1 → Cell := oneBank p15587 ray15587
theorem signs15587 : ∀ j, Signs p15587 (bank15587 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15588 := params 3
abbrev ray15588 := rays 3
def bank15588 : Fin 1 → Cell := oneBank p15588 ray15588
theorem signs15588 : ∀ j, Signs p15588 (bank15588 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15589 := params 4
abbrev ray15589 := rays 4
def bank15589 : Fin 1 → Cell := oneBank p15589 ray15589
theorem signs15589 : ∀ j, Signs p15589 (bank15589 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15590 := params 5
abbrev ray15590 := rays 5
def bank15590 : Fin 1 → Cell := oneBank p15590 ray15590
theorem signs15590 : ∀ j, Signs p15590 (bank15590 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15591 := params 6
abbrev ray15591 := rays 6
def bank15591 : Fin 1 → Cell := oneBank p15591 ray15591
theorem signs15591 : ∀ j, Signs p15591 (bank15591 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15592 := params 7
abbrev ray15592 := rays 7
def bank15592 : Fin 1 → Cell := oneBank p15592 ray15592
theorem signs15592 : ∀ j, Signs p15592 (bank15592 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15593 := params 8
abbrev ray15593 := rays 8
def bank15593 : Fin 1 → Cell := oneBank p15593 ray15593
theorem signs15593 : ∀ j, Signs p15593 (bank15593 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15594 := params 9
abbrev ray15594 := rays 9
def bank15594 : Fin 1 → Cell := oneBank p15594 ray15594
theorem signs15594 : ∀ j, Signs p15594 (bank15594 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15595 := params 10
abbrev ray15595 := rays 10
def bank15595 : Fin 1 → Cell := oneBank p15595 ray15595
theorem signs15595 : ∀ j, Signs p15595 (bank15595 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15596 := params 11
abbrev ray15596 := rays 11
def bank15596 : Fin 1 → Cell := oneBank p15596 ray15596
theorem signs15596 : ∀ j, Signs p15596 (bank15596 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15597 := params 12
abbrev ray15597 := rays 12
def bank15597 : Fin 1 → Cell := oneBank p15597 ray15597
theorem signs15597 : ∀ j, Signs p15597 (bank15597 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15598 := params 13
abbrev ray15598 := rays 13
def bank15598 : Fin 1 → Cell := oneBank p15598 ray15598
theorem signs15598 : ∀ j, Signs p15598 (bank15598 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15599 := params 14
abbrev ray15599 := rays 14
def bank15599 : Fin 1 → Cell := oneBank p15599 ray15599
theorem signs15599 : ∀ j, Signs p15599 (bank15599 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15600 := params 15
abbrev ray15600 := rays 15
def bank15600 : Fin 1 → Cell := oneBank p15600 ray15600
theorem signs15600 : ∀ j, Signs p15600 (bank15600 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15601 := params 16
abbrev ray15601 := rays 16
def bank15601 : Fin 1 → Cell := oneBank p15601 ray15601
theorem signs15601 : ∀ j, Signs p15601 (bank15601 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15602 := params 17
abbrev ray15602 := rays 17
def bank15602 : Fin 1 → Cell := oneBank p15602 ray15602
theorem signs15602 : ∀ j, Signs p15602 (bank15602 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15603 := params 18
abbrev ray15603 := rays 18
def bank15603 : Fin 1 → Cell := oneBank p15603 ray15603
theorem signs15603 : ∀ j, Signs p15603 (bank15603 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15604 := params 19
abbrev ray15604 := rays 19
def bank15604 : Fin 1 → Cell := oneBank p15604 ray15604
theorem signs15604 : ∀ j, Signs p15604 (bank15604 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15605 := params 20
abbrev ray15605 := rays 20
def bank15605 : Fin 1 → Cell := oneBank p15605 ray15605
theorem signs15605 : ∀ j, Signs p15605 (bank15605 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15606 := params 21
abbrev ray15606 := rays 21
def bank15606 : Fin 1 → Cell := oneBank p15606 ray15606
theorem signs15606 : ∀ j, Signs p15606 (bank15606 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15607 := params 22
abbrev ray15607 := rays 22
def bank15607 : Fin 1 → Cell := oneBank p15607 ray15607
theorem signs15607 : ∀ j, Signs p15607 (bank15607 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15608 := params 23
abbrev ray15608 := rays 23
def bank15608 : Fin 1 → Cell := oneBank p15608 ray15608
theorem signs15608 : ∀ j, Signs p15608 (bank15608 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15609 := params 24
abbrev ray15609 := rays 24
def bank15609 : Fin 1 → Cell := oneBank p15609 ray15609
theorem signs15609 : ∀ j, Signs p15609 (bank15609 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15610 := params 25
abbrev ray15610 := rays 25
def bank15610 : Fin 1 → Cell := oneBank p15610 ray15610
theorem signs15610 : ∀ j, Signs p15610 (bank15610 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15611 := params 26
abbrev ray15611 := rays 26
def bank15611 : Fin 1 → Cell := oneBank p15611 ray15611
theorem signs15611 : ∀ j, Signs p15611 (bank15611 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15612 := params 27
abbrev ray15612 := rays 27
def bank15612 : Fin 1 → Cell := oneBank p15612 ray15612
theorem signs15612 : ∀ j, Signs p15612 (bank15612 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15613 := params 28
abbrev ray15613 := rays 28
def bank15613 : Fin 1 → Cell := oneBank p15613 ray15613
theorem signs15613 : ∀ j, Signs p15613 (bank15613 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15614 := params 29
abbrev ray15614 := rays 29
def bank15614 : Fin 1 → Cell := oneBank p15614 ray15614
theorem signs15614 : ∀ j, Signs p15614 (bank15614 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15615 := params 30
abbrev ray15615 := rays 30
def bank15615 : Fin 1 → Cell := oneBank p15615 ray15615
theorem signs15615 : ∀ j, Signs p15615 (bank15615 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15616 := params 31
abbrev ray15616 := rays 31
def bank15616 : Fin 1 → Cell := oneBank p15616 ray15616
theorem signs15616 : ∀ j, Signs p15616 (bank15616 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15585_15616
