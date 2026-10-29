/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages17025_17046
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 23 → ℕ := ![94439853212286,94439363465526,94438873702771,94438383924021,94437894129276,94437404318536,94436914491801,94436424649071,94435934790346,94435444915626,94434955024911,94434465118201,94433975195496,94433485234362,94432995257234,94432505264113,94432015254998,94431525229890,94431035188788,94430545131693,94430055058604,94429564969522,94429074864446]
def b (i : Fin 23) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 22) : Params := point (17024+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 22 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p17025 := params 0
abbrev ray17025 := rays 0
def bank17025 : Fin 1 → Cell := oneBank p17025 ray17025
theorem signs17025 : ∀ j, Signs p17025 (bank17025 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17026 := params 1
abbrev ray17026 := rays 1
def bank17026 : Fin 1 → Cell := oneBank p17026 ray17026
theorem signs17026 : ∀ j, Signs p17026 (bank17026 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17027 := params 2
abbrev ray17027 := rays 2
def bank17027 : Fin 1 → Cell := oneBank p17027 ray17027
theorem signs17027 : ∀ j, Signs p17027 (bank17027 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17028 := params 3
abbrev ray17028 := rays 3
def bank17028 : Fin 1 → Cell := oneBank p17028 ray17028
theorem signs17028 : ∀ j, Signs p17028 (bank17028 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17029 := params 4
abbrev ray17029 := rays 4
def bank17029 : Fin 1 → Cell := oneBank p17029 ray17029
theorem signs17029 : ∀ j, Signs p17029 (bank17029 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17030 := params 5
abbrev ray17030 := rays 5
def bank17030 : Fin 1 → Cell := oneBank p17030 ray17030
theorem signs17030 : ∀ j, Signs p17030 (bank17030 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17031 := params 6
abbrev ray17031 := rays 6
def bank17031 : Fin 1 → Cell := oneBank p17031 ray17031
theorem signs17031 : ∀ j, Signs p17031 (bank17031 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17032 := params 7
abbrev ray17032 := rays 7
def bank17032 : Fin 1 → Cell := oneBank p17032 ray17032
theorem signs17032 : ∀ j, Signs p17032 (bank17032 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17033 := params 8
abbrev ray17033 := rays 8
def bank17033 : Fin 1 → Cell := oneBank p17033 ray17033
theorem signs17033 : ∀ j, Signs p17033 (bank17033 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17034 := params 9
abbrev ray17034 := rays 9
def bank17034 : Fin 1 → Cell := oneBank p17034 ray17034
theorem signs17034 : ∀ j, Signs p17034 (bank17034 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17035 := params 10
abbrev ray17035 := rays 10
def bank17035 : Fin 1 → Cell := oneBank p17035 ray17035
theorem signs17035 : ∀ j, Signs p17035 (bank17035 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17036 := params 11
abbrev ray17036 := rays 11
def bank17036 : Fin 1 → Cell := oneBank p17036 ray17036
theorem signs17036 : ∀ j, Signs p17036 (bank17036 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17037 := params 12
abbrev ray17037 := rays 12
def bank17037 : Fin 1 → Cell := oneBank p17037 ray17037
theorem signs17037 : ∀ j, Signs p17037 (bank17037 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17038 := params 13
abbrev ray17038 := rays 13
def bank17038 : Fin 1 → Cell := oneBank p17038 ray17038
theorem signs17038 : ∀ j, Signs p17038 (bank17038 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17039 := params 14
abbrev ray17039 := rays 14
def bank17039 : Fin 1 → Cell := oneBank p17039 ray17039
theorem signs17039 : ∀ j, Signs p17039 (bank17039 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17040 := params 15
abbrev ray17040 := rays 15
def bank17040 : Fin 1 → Cell := oneBank p17040 ray17040
theorem signs17040 : ∀ j, Signs p17040 (bank17040 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17041 := params 16
abbrev ray17041 := rays 16
def bank17041 : Fin 1 → Cell := oneBank p17041 ray17041
theorem signs17041 : ∀ j, Signs p17041 (bank17041 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17042 := params 17
abbrev ray17042 := rays 17
def bank17042 : Fin 1 → Cell := oneBank p17042 ray17042
theorem signs17042 : ∀ j, Signs p17042 (bank17042 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17043 := params 18
abbrev ray17043 := rays 18
def bank17043 : Fin 1 → Cell := oneBank p17043 ray17043
theorem signs17043 : ∀ j, Signs p17043 (bank17043 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17044 := params 19
abbrev ray17044 := rays 19
def bank17044 : Fin 1 → Cell := oneBank p17044 ray17044
theorem signs17044 : ∀ j, Signs p17044 (bank17044 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17045 := params 20
abbrev ray17045 := rays 20
def bank17045 : Fin 1 → Cell := oneBank p17045 ray17045
theorem signs17045 : ∀ j, Signs p17045 (bank17045 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17046 := params 21
abbrev ray17046 := rays 21
def bank17046 : Fin 1 → Cell := oneBank p17046 ray17046
theorem signs17046 : ∀ j, Signs p17046 (bank17046 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages17025_17046
