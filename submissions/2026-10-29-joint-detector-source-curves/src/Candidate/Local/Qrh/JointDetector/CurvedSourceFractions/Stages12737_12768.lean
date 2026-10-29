/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12737_12768
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96392283236382,96391862816317,96391442377200,96391021919031,96390601441810,96390180945538,96389760430215,96389339895841,96388919342417,96388498769943,96388078178420,96387657567848,96387236938227,96386816289558,96386395621841,96385974935077,96385554229266,96385133504408,96384712760504,96384291997554,96383871215558,96383450414517,96383029594431,96382608755301,96382187897127,96381767019910,96381346123650,96380925208347,96380504274001,96380083320613,96379662348184,96379241356714,96378820346203]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12736+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12737 := params 0
abbrev ray12737 := rays 0
def bank12737 : Fin 2 → Cell := twoBank p12737 ray12737
theorem signs12737 : ∀ j, Signs p12737 (bank12737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12738 := params 1
abbrev ray12738 := rays 1
def bank12738 : Fin 2 → Cell := twoBank p12738 ray12738
theorem signs12738 : ∀ j, Signs p12738 (bank12738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12739 := params 2
abbrev ray12739 := rays 2
def bank12739 : Fin 2 → Cell := twoBank p12739 ray12739
theorem signs12739 : ∀ j, Signs p12739 (bank12739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12740 := params 3
abbrev ray12740 := rays 3
def bank12740 : Fin 2 → Cell := twoBank p12740 ray12740
theorem signs12740 : ∀ j, Signs p12740 (bank12740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12741 := params 4
abbrev ray12741 := rays 4
def bank12741 : Fin 2 → Cell := twoBank p12741 ray12741
theorem signs12741 : ∀ j, Signs p12741 (bank12741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12742 := params 5
abbrev ray12742 := rays 5
def bank12742 : Fin 2 → Cell := twoBank p12742 ray12742
theorem signs12742 : ∀ j, Signs p12742 (bank12742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12743 := params 6
abbrev ray12743 := rays 6
def bank12743 : Fin 2 → Cell := twoBank p12743 ray12743
theorem signs12743 : ∀ j, Signs p12743 (bank12743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12744 := params 7
abbrev ray12744 := rays 7
def bank12744 : Fin 2 → Cell := twoBank p12744 ray12744
theorem signs12744 : ∀ j, Signs p12744 (bank12744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12745 := params 8
abbrev ray12745 := rays 8
def bank12745 : Fin 2 → Cell := twoBank p12745 ray12745
theorem signs12745 : ∀ j, Signs p12745 (bank12745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12746 := params 9
abbrev ray12746 := rays 9
def bank12746 : Fin 2 → Cell := twoBank p12746 ray12746
theorem signs12746 : ∀ j, Signs p12746 (bank12746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12747 := params 10
abbrev ray12747 := rays 10
def bank12747 : Fin 2 → Cell := twoBank p12747 ray12747
theorem signs12747 : ∀ j, Signs p12747 (bank12747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12748 := params 11
abbrev ray12748 := rays 11
def bank12748 : Fin 2 → Cell := twoBank p12748 ray12748
theorem signs12748 : ∀ j, Signs p12748 (bank12748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12749 := params 12
abbrev ray12749 := rays 12
def bank12749 : Fin 2 → Cell := twoBank p12749 ray12749
theorem signs12749 : ∀ j, Signs p12749 (bank12749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12750 := params 13
abbrev ray12750 := rays 13
def bank12750 : Fin 2 → Cell := twoBank p12750 ray12750
theorem signs12750 : ∀ j, Signs p12750 (bank12750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12751 := params 14
abbrev ray12751 := rays 14
def bank12751 : Fin 2 → Cell := twoBank p12751 ray12751
theorem signs12751 : ∀ j, Signs p12751 (bank12751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12752 := params 15
abbrev ray12752 := rays 15
def bank12752 : Fin 2 → Cell := twoBank p12752 ray12752
theorem signs12752 : ∀ j, Signs p12752 (bank12752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12753 := params 16
abbrev ray12753 := rays 16
def bank12753 : Fin 2 → Cell := twoBank p12753 ray12753
theorem signs12753 : ∀ j, Signs p12753 (bank12753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12754 := params 17
abbrev ray12754 := rays 17
def bank12754 : Fin 2 → Cell := twoBank p12754 ray12754
theorem signs12754 : ∀ j, Signs p12754 (bank12754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12755 := params 18
abbrev ray12755 := rays 18
def bank12755 : Fin 2 → Cell := twoBank p12755 ray12755
theorem signs12755 : ∀ j, Signs p12755 (bank12755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12756 := params 19
abbrev ray12756 := rays 19
def bank12756 : Fin 2 → Cell := twoBank p12756 ray12756
theorem signs12756 : ∀ j, Signs p12756 (bank12756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12757 := params 20
abbrev ray12757 := rays 20
def bank12757 : Fin 2 → Cell := twoBank p12757 ray12757
theorem signs12757 : ∀ j, Signs p12757 (bank12757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12758 := params 21
abbrev ray12758 := rays 21
def bank12758 : Fin 2 → Cell := twoBank p12758 ray12758
theorem signs12758 : ∀ j, Signs p12758 (bank12758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12759 := params 22
abbrev ray12759 := rays 22
def bank12759 : Fin 2 → Cell := twoBank p12759 ray12759
theorem signs12759 : ∀ j, Signs p12759 (bank12759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12760 := params 23
abbrev ray12760 := rays 23
def bank12760 : Fin 2 → Cell := twoBank p12760 ray12760
theorem signs12760 : ∀ j, Signs p12760 (bank12760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12761 := params 24
abbrev ray12761 := rays 24
def bank12761 : Fin 2 → Cell := twoBank p12761 ray12761
theorem signs12761 : ∀ j, Signs p12761 (bank12761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12762 := params 25
abbrev ray12762 := rays 25
def bank12762 : Fin 2 → Cell := twoBank p12762 ray12762
theorem signs12762 : ∀ j, Signs p12762 (bank12762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12763 := params 26
abbrev ray12763 := rays 26
def bank12763 : Fin 2 → Cell := twoBank p12763 ray12763
theorem signs12763 : ∀ j, Signs p12763 (bank12763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12764 := params 27
abbrev ray12764 := rays 27
def bank12764 : Fin 2 → Cell := twoBank p12764 ray12764
theorem signs12764 : ∀ j, Signs p12764 (bank12764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12765 := params 28
abbrev ray12765 := rays 28
def bank12765 : Fin 2 → Cell := twoBank p12765 ray12765
theorem signs12765 : ∀ j, Signs p12765 (bank12765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12766 := params 29
abbrev ray12766 := rays 29
def bank12766 : Fin 2 → Cell := twoBank p12766 ray12766
theorem signs12766 : ∀ j, Signs p12766 (bank12766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12767 := params 30
abbrev ray12767 := rays 30
def bank12767 : Fin 2 → Cell := twoBank p12767 ray12767
theorem signs12767 : ∀ j, Signs p12767 (bank12767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12768 := params 31
abbrev ray12768 := rays 31
def bank12768 : Fin 2 → Cell := twoBank p12768 ray12768
theorem signs12768 : ∀ j, Signs p12768 (bank12768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12737_12768
