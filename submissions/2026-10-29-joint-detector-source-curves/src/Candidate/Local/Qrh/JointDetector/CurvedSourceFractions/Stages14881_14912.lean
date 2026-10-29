/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14881_14912
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95453092627632,95452637202824,95452181761936,95451726304969,95451270831922,95450815342796,95450359837591,95449904316307,95449448778944,95448993225502,95448537655981,95448082070382,95447626468704,95447170850948,95446715217114,95446259567202,95445803901212,95445348219144,95444892520998,95444436806775,95443981076474,95443525330096,95443069567641,95442613789109,95442157994500,95441702183814,95441246357051,95440790514211,95440334655295,95439878780303,95439422889234,95438966982089,95438511058868]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14880+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14881 := params 0
abbrev ray14881 := rays 0
def bank14881 : Fin 1 → Cell := oneBank p14881 ray14881
theorem signs14881 : ∀ j, Signs p14881 (bank14881 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14882 := params 1
abbrev ray14882 := rays 1
def bank14882 : Fin 1 → Cell := oneBank p14882 ray14882
theorem signs14882 : ∀ j, Signs p14882 (bank14882 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14883 := params 2
abbrev ray14883 := rays 2
def bank14883 : Fin 1 → Cell := oneBank p14883 ray14883
theorem signs14883 : ∀ j, Signs p14883 (bank14883 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14884 := params 3
abbrev ray14884 := rays 3
def bank14884 : Fin 1 → Cell := oneBank p14884 ray14884
theorem signs14884 : ∀ j, Signs p14884 (bank14884 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14885 := params 4
abbrev ray14885 := rays 4
def bank14885 : Fin 1 → Cell := oneBank p14885 ray14885
theorem signs14885 : ∀ j, Signs p14885 (bank14885 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14886 := params 5
abbrev ray14886 := rays 5
def bank14886 : Fin 1 → Cell := oneBank p14886 ray14886
theorem signs14886 : ∀ j, Signs p14886 (bank14886 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14887 := params 6
abbrev ray14887 := rays 6
def bank14887 : Fin 1 → Cell := oneBank p14887 ray14887
theorem signs14887 : ∀ j, Signs p14887 (bank14887 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14888 := params 7
abbrev ray14888 := rays 7
def bank14888 : Fin 1 → Cell := oneBank p14888 ray14888
theorem signs14888 : ∀ j, Signs p14888 (bank14888 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14889 := params 8
abbrev ray14889 := rays 8
def bank14889 : Fin 1 → Cell := oneBank p14889 ray14889
theorem signs14889 : ∀ j, Signs p14889 (bank14889 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14890 := params 9
abbrev ray14890 := rays 9
def bank14890 : Fin 1 → Cell := oneBank p14890 ray14890
theorem signs14890 : ∀ j, Signs p14890 (bank14890 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14891 := params 10
abbrev ray14891 := rays 10
def bank14891 : Fin 1 → Cell := oneBank p14891 ray14891
theorem signs14891 : ∀ j, Signs p14891 (bank14891 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14892 := params 11
abbrev ray14892 := rays 11
def bank14892 : Fin 1 → Cell := oneBank p14892 ray14892
theorem signs14892 : ∀ j, Signs p14892 (bank14892 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14893 := params 12
abbrev ray14893 := rays 12
def bank14893 : Fin 1 → Cell := oneBank p14893 ray14893
theorem signs14893 : ∀ j, Signs p14893 (bank14893 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14894 := params 13
abbrev ray14894 := rays 13
def bank14894 : Fin 1 → Cell := oneBank p14894 ray14894
theorem signs14894 : ∀ j, Signs p14894 (bank14894 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14895 := params 14
abbrev ray14895 := rays 14
def bank14895 : Fin 1 → Cell := oneBank p14895 ray14895
theorem signs14895 : ∀ j, Signs p14895 (bank14895 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14896 := params 15
abbrev ray14896 := rays 15
def bank14896 : Fin 1 → Cell := oneBank p14896 ray14896
theorem signs14896 : ∀ j, Signs p14896 (bank14896 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14897 := params 16
abbrev ray14897 := rays 16
def bank14897 : Fin 1 → Cell := oneBank p14897 ray14897
theorem signs14897 : ∀ j, Signs p14897 (bank14897 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14898 := params 17
abbrev ray14898 := rays 17
def bank14898 : Fin 1 → Cell := oneBank p14898 ray14898
theorem signs14898 : ∀ j, Signs p14898 (bank14898 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14899 := params 18
abbrev ray14899 := rays 18
def bank14899 : Fin 1 → Cell := oneBank p14899 ray14899
theorem signs14899 : ∀ j, Signs p14899 (bank14899 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14900 := params 19
abbrev ray14900 := rays 19
def bank14900 : Fin 1 → Cell := oneBank p14900 ray14900
theorem signs14900 : ∀ j, Signs p14900 (bank14900 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14901 := params 20
abbrev ray14901 := rays 20
def bank14901 : Fin 1 → Cell := oneBank p14901 ray14901
theorem signs14901 : ∀ j, Signs p14901 (bank14901 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14902 := params 21
abbrev ray14902 := rays 21
def bank14902 : Fin 1 → Cell := oneBank p14902 ray14902
theorem signs14902 : ∀ j, Signs p14902 (bank14902 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14903 := params 22
abbrev ray14903 := rays 22
def bank14903 : Fin 1 → Cell := oneBank p14903 ray14903
theorem signs14903 : ∀ j, Signs p14903 (bank14903 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14904 := params 23
abbrev ray14904 := rays 23
def bank14904 : Fin 1 → Cell := oneBank p14904 ray14904
theorem signs14904 : ∀ j, Signs p14904 (bank14904 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14905 := params 24
abbrev ray14905 := rays 24
def bank14905 : Fin 1 → Cell := oneBank p14905 ray14905
theorem signs14905 : ∀ j, Signs p14905 (bank14905 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14906 := params 25
abbrev ray14906 := rays 25
def bank14906 : Fin 1 → Cell := oneBank p14906 ray14906
theorem signs14906 : ∀ j, Signs p14906 (bank14906 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14907 := params 26
abbrev ray14907 := rays 26
def bank14907 : Fin 1 → Cell := oneBank p14907 ray14907
theorem signs14907 : ∀ j, Signs p14907 (bank14907 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14908 := params 27
abbrev ray14908 := rays 27
def bank14908 : Fin 1 → Cell := oneBank p14908 ray14908
theorem signs14908 : ∀ j, Signs p14908 (bank14908 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14909 := params 28
abbrev ray14909 := rays 28
def bank14909 : Fin 1 → Cell := oneBank p14909 ray14909
theorem signs14909 : ∀ j, Signs p14909 (bank14909 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14910 := params 29
abbrev ray14910 := rays 29
def bank14910 : Fin 1 → Cell := oneBank p14910 ray14910
theorem signs14910 : ∀ j, Signs p14910 (bank14910 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14911 := params 30
abbrev ray14911 := rays 30
def bank14911 : Fin 1 → Cell := oneBank p14911 ray14911
theorem signs14911 : ∀ j, Signs p14911 (bank14911 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14912 := params 31
abbrev ray14912 := rays 31
def bank14912 : Fin 1 → Cell := oneBank p14912 ray14912
theorem signs14912 : ∀ j, Signs p14912 (bank14912 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14881_14912
