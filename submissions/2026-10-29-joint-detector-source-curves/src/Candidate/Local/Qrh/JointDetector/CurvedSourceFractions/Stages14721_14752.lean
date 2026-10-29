/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14721_14752
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95525753406263,95525300555785,95524847689207,95524394806530,95523941907753,95523488992877,95523036061902,95522583114828,95522130151655,95521677172383,95521224177012,95520771165543,95520318137975,95519865094309,95519412034545,95518958958683,95518505866723,95518052758665,95517599634510,95517146494257,95516693337907,95516240165460,95515786976916,95515333772275,95514880551537,95514427314702,95513974061771,95513520792743,95513067507619,95512614206399,95512160889083,95511707555671,95511254206163]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14720+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14721 := params 0
abbrev ray14721 := rays 0
def bank14721 : Fin 1 → Cell := oneBank p14721 ray14721
theorem signs14721 : ∀ j, Signs p14721 (bank14721 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14722 := params 1
abbrev ray14722 := rays 1
def bank14722 : Fin 1 → Cell := oneBank p14722 ray14722
theorem signs14722 : ∀ j, Signs p14722 (bank14722 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14723 := params 2
abbrev ray14723 := rays 2
def bank14723 : Fin 1 → Cell := oneBank p14723 ray14723
theorem signs14723 : ∀ j, Signs p14723 (bank14723 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14724 := params 3
abbrev ray14724 := rays 3
def bank14724 : Fin 1 → Cell := oneBank p14724 ray14724
theorem signs14724 : ∀ j, Signs p14724 (bank14724 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14725 := params 4
abbrev ray14725 := rays 4
def bank14725 : Fin 1 → Cell := oneBank p14725 ray14725
theorem signs14725 : ∀ j, Signs p14725 (bank14725 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14726 := params 5
abbrev ray14726 := rays 5
def bank14726 : Fin 1 → Cell := oneBank p14726 ray14726
theorem signs14726 : ∀ j, Signs p14726 (bank14726 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14727 := params 6
abbrev ray14727 := rays 6
def bank14727 : Fin 1 → Cell := oneBank p14727 ray14727
theorem signs14727 : ∀ j, Signs p14727 (bank14727 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14728 := params 7
abbrev ray14728 := rays 7
def bank14728 : Fin 1 → Cell := oneBank p14728 ray14728
theorem signs14728 : ∀ j, Signs p14728 (bank14728 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14729 := params 8
abbrev ray14729 := rays 8
def bank14729 : Fin 1 → Cell := oneBank p14729 ray14729
theorem signs14729 : ∀ j, Signs p14729 (bank14729 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14730 := params 9
abbrev ray14730 := rays 9
def bank14730 : Fin 1 → Cell := oneBank p14730 ray14730
theorem signs14730 : ∀ j, Signs p14730 (bank14730 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14731 := params 10
abbrev ray14731 := rays 10
def bank14731 : Fin 1 → Cell := oneBank p14731 ray14731
theorem signs14731 : ∀ j, Signs p14731 (bank14731 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14732 := params 11
abbrev ray14732 := rays 11
def bank14732 : Fin 1 → Cell := oneBank p14732 ray14732
theorem signs14732 : ∀ j, Signs p14732 (bank14732 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14733 := params 12
abbrev ray14733 := rays 12
def bank14733 : Fin 1 → Cell := oneBank p14733 ray14733
theorem signs14733 : ∀ j, Signs p14733 (bank14733 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14734 := params 13
abbrev ray14734 := rays 13
def bank14734 : Fin 1 → Cell := oneBank p14734 ray14734
theorem signs14734 : ∀ j, Signs p14734 (bank14734 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14735 := params 14
abbrev ray14735 := rays 14
def bank14735 : Fin 1 → Cell := oneBank p14735 ray14735
theorem signs14735 : ∀ j, Signs p14735 (bank14735 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14736 := params 15
abbrev ray14736 := rays 15
def bank14736 : Fin 1 → Cell := oneBank p14736 ray14736
theorem signs14736 : ∀ j, Signs p14736 (bank14736 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14737 := params 16
abbrev ray14737 := rays 16
def bank14737 : Fin 1 → Cell := oneBank p14737 ray14737
theorem signs14737 : ∀ j, Signs p14737 (bank14737 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14738 := params 17
abbrev ray14738 := rays 17
def bank14738 : Fin 1 → Cell := oneBank p14738 ray14738
theorem signs14738 : ∀ j, Signs p14738 (bank14738 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14739 := params 18
abbrev ray14739 := rays 18
def bank14739 : Fin 1 → Cell := oneBank p14739 ray14739
theorem signs14739 : ∀ j, Signs p14739 (bank14739 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14740 := params 19
abbrev ray14740 := rays 19
def bank14740 : Fin 1 → Cell := oneBank p14740 ray14740
theorem signs14740 : ∀ j, Signs p14740 (bank14740 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14741 := params 20
abbrev ray14741 := rays 20
def bank14741 : Fin 1 → Cell := oneBank p14741 ray14741
theorem signs14741 : ∀ j, Signs p14741 (bank14741 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14742 := params 21
abbrev ray14742 := rays 21
def bank14742 : Fin 1 → Cell := oneBank p14742 ray14742
theorem signs14742 : ∀ j, Signs p14742 (bank14742 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14743 := params 22
abbrev ray14743 := rays 22
def bank14743 : Fin 1 → Cell := oneBank p14743 ray14743
theorem signs14743 : ∀ j, Signs p14743 (bank14743 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14744 := params 23
abbrev ray14744 := rays 23
def bank14744 : Fin 1 → Cell := oneBank p14744 ray14744
theorem signs14744 : ∀ j, Signs p14744 (bank14744 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14745 := params 24
abbrev ray14745 := rays 24
def bank14745 : Fin 1 → Cell := oneBank p14745 ray14745
theorem signs14745 : ∀ j, Signs p14745 (bank14745 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14746 := params 25
abbrev ray14746 := rays 25
def bank14746 : Fin 1 → Cell := oneBank p14746 ray14746
theorem signs14746 : ∀ j, Signs p14746 (bank14746 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14747 := params 26
abbrev ray14747 := rays 26
def bank14747 : Fin 1 → Cell := oneBank p14747 ray14747
theorem signs14747 : ∀ j, Signs p14747 (bank14747 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14748 := params 27
abbrev ray14748 := rays 27
def bank14748 : Fin 1 → Cell := oneBank p14748 ray14748
theorem signs14748 : ∀ j, Signs p14748 (bank14748 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14749 := params 28
abbrev ray14749 := rays 28
def bank14749 : Fin 1 → Cell := oneBank p14749 ray14749
theorem signs14749 : ∀ j, Signs p14749 (bank14749 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14750 := params 29
abbrev ray14750 := rays 29
def bank14750 : Fin 1 → Cell := oneBank p14750 ray14750
theorem signs14750 : ∀ j, Signs p14750 (bank14750 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14751 := params 30
abbrev ray14751 := rays 30
def bank14751 : Fin 1 → Cell := oneBank p14751 ray14751
theorem signs14751 : ∀ j, Signs p14751 (bank14751 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14752 := params 31
abbrev ray14752 := rays 31
def bank14752 : Fin 1 → Cell := oneBank p14752 ray14752
theorem signs14752 : ∀ j, Signs p14752 (bank14752 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14721_14752
