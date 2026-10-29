/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14689_14720
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95540236120119,95539783784902,95539331433581,95538879066156,95538426682627,95537974282995,95537521867259,95537069435420,95536616987478,95536164523433,95535712043285,95535259547034,95534807034680,95534354506224,95533901961666,95533449401005,95532996824242,95532544231377,95532091622411,95531638997343,95531186356173,95530733698902,95530281025530,95529828336056,95529375630481,95528922908805,95528470171029,95528017417152,95527564647175,95527111861097,95526659058919,95526206240641,95525753406263]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14688+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14689 := params 0
abbrev ray14689 := rays 0
def bank14689 : Fin 1 → Cell := oneBank p14689 ray14689
theorem signs14689 : ∀ j, Signs p14689 (bank14689 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14690 := params 1
abbrev ray14690 := rays 1
def bank14690 : Fin 1 → Cell := oneBank p14690 ray14690
theorem signs14690 : ∀ j, Signs p14690 (bank14690 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14691 := params 2
abbrev ray14691 := rays 2
def bank14691 : Fin 1 → Cell := oneBank p14691 ray14691
theorem signs14691 : ∀ j, Signs p14691 (bank14691 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14692 := params 3
abbrev ray14692 := rays 3
def bank14692 : Fin 1 → Cell := oneBank p14692 ray14692
theorem signs14692 : ∀ j, Signs p14692 (bank14692 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14693 := params 4
abbrev ray14693 := rays 4
def bank14693 : Fin 1 → Cell := oneBank p14693 ray14693
theorem signs14693 : ∀ j, Signs p14693 (bank14693 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14694 := params 5
abbrev ray14694 := rays 5
def bank14694 : Fin 1 → Cell := oneBank p14694 ray14694
theorem signs14694 : ∀ j, Signs p14694 (bank14694 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14695 := params 6
abbrev ray14695 := rays 6
def bank14695 : Fin 1 → Cell := oneBank p14695 ray14695
theorem signs14695 : ∀ j, Signs p14695 (bank14695 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14696 := params 7
abbrev ray14696 := rays 7
def bank14696 : Fin 1 → Cell := oneBank p14696 ray14696
theorem signs14696 : ∀ j, Signs p14696 (bank14696 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14697 := params 8
abbrev ray14697 := rays 8
def bank14697 : Fin 1 → Cell := oneBank p14697 ray14697
theorem signs14697 : ∀ j, Signs p14697 (bank14697 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14698 := params 9
abbrev ray14698 := rays 9
def bank14698 : Fin 1 → Cell := oneBank p14698 ray14698
theorem signs14698 : ∀ j, Signs p14698 (bank14698 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14699 := params 10
abbrev ray14699 := rays 10
def bank14699 : Fin 1 → Cell := oneBank p14699 ray14699
theorem signs14699 : ∀ j, Signs p14699 (bank14699 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14700 := params 11
abbrev ray14700 := rays 11
def bank14700 : Fin 1 → Cell := oneBank p14700 ray14700
theorem signs14700 : ∀ j, Signs p14700 (bank14700 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14701 := params 12
abbrev ray14701 := rays 12
def bank14701 : Fin 1 → Cell := oneBank p14701 ray14701
theorem signs14701 : ∀ j, Signs p14701 (bank14701 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14702 := params 13
abbrev ray14702 := rays 13
def bank14702 : Fin 1 → Cell := oneBank p14702 ray14702
theorem signs14702 : ∀ j, Signs p14702 (bank14702 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14703 := params 14
abbrev ray14703 := rays 14
def bank14703 : Fin 1 → Cell := oneBank p14703 ray14703
theorem signs14703 : ∀ j, Signs p14703 (bank14703 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14704 := params 15
abbrev ray14704 := rays 15
def bank14704 : Fin 1 → Cell := oneBank p14704 ray14704
theorem signs14704 : ∀ j, Signs p14704 (bank14704 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14705 := params 16
abbrev ray14705 := rays 16
def bank14705 : Fin 1 → Cell := oneBank p14705 ray14705
theorem signs14705 : ∀ j, Signs p14705 (bank14705 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14706 := params 17
abbrev ray14706 := rays 17
def bank14706 : Fin 1 → Cell := oneBank p14706 ray14706
theorem signs14706 : ∀ j, Signs p14706 (bank14706 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14707 := params 18
abbrev ray14707 := rays 18
def bank14707 : Fin 1 → Cell := oneBank p14707 ray14707
theorem signs14707 : ∀ j, Signs p14707 (bank14707 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14708 := params 19
abbrev ray14708 := rays 19
def bank14708 : Fin 1 → Cell := oneBank p14708 ray14708
theorem signs14708 : ∀ j, Signs p14708 (bank14708 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14709 := params 20
abbrev ray14709 := rays 20
def bank14709 : Fin 1 → Cell := oneBank p14709 ray14709
theorem signs14709 : ∀ j, Signs p14709 (bank14709 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14710 := params 21
abbrev ray14710 := rays 21
def bank14710 : Fin 1 → Cell := oneBank p14710 ray14710
theorem signs14710 : ∀ j, Signs p14710 (bank14710 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14711 := params 22
abbrev ray14711 := rays 22
def bank14711 : Fin 1 → Cell := oneBank p14711 ray14711
theorem signs14711 : ∀ j, Signs p14711 (bank14711 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14712 := params 23
abbrev ray14712 := rays 23
def bank14712 : Fin 1 → Cell := oneBank p14712 ray14712
theorem signs14712 : ∀ j, Signs p14712 (bank14712 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14713 := params 24
abbrev ray14713 := rays 24
def bank14713 : Fin 1 → Cell := oneBank p14713 ray14713
theorem signs14713 : ∀ j, Signs p14713 (bank14713 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14714 := params 25
abbrev ray14714 := rays 25
def bank14714 : Fin 1 → Cell := oneBank p14714 ray14714
theorem signs14714 : ∀ j, Signs p14714 (bank14714 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14715 := params 26
abbrev ray14715 := rays 26
def bank14715 : Fin 1 → Cell := oneBank p14715 ray14715
theorem signs14715 : ∀ j, Signs p14715 (bank14715 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14716 := params 27
abbrev ray14716 := rays 27
def bank14716 : Fin 1 → Cell := oneBank p14716 ray14716
theorem signs14716 : ∀ j, Signs p14716 (bank14716 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14717 := params 28
abbrev ray14717 := rays 28
def bank14717 : Fin 1 → Cell := oneBank p14717 ray14717
theorem signs14717 : ∀ j, Signs p14717 (bank14717 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14718 := params 29
abbrev ray14718 := rays 29
def bank14718 : Fin 1 → Cell := oneBank p14718 ray14718
theorem signs14718 : ∀ j, Signs p14718 (bank14718 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14719 := params 30
abbrev ray14719 := rays 30
def bank14719 : Fin 1 → Cell := oneBank p14719 ray14719
theorem signs14719 : ∀ j, Signs p14719 (bank14719 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14720 := params 31
abbrev ray14720 := rays 31
def bank14720 : Fin 1 → Cell := oneBank p14720 ray14720
theorem signs14720 : ∀ j, Signs p14720 (bank14720 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14689_14720
