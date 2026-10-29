/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14017_14048
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95840556390699,95840114911396,95839673415883,95839231904159,95838790376225,95838348832080,95837907271725,95837465695161,95837024102387,95836582493403,95836140868210,95835699226808,95835257569197,95834815895377,95834374205349,95833932499112,95833490776667,95833049038014,95832607283153,95832165512085,95831723724809,95831281921326,95830840101636,95830398265739,95829956413635,95829514545325,95829072660808,95828630760085,95828188843156,95827746910021,95827304960681,95826862995135,95826421013384]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14016+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14017 := params 0
abbrev ray14017 := rays 0
def bank14017 : Fin 1 → Cell := oneBank p14017 ray14017
theorem signs14017 : ∀ j, Signs p14017 (bank14017 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14018 := params 1
abbrev ray14018 := rays 1
def bank14018 : Fin 1 → Cell := oneBank p14018 ray14018
theorem signs14018 : ∀ j, Signs p14018 (bank14018 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14019 := params 2
abbrev ray14019 := rays 2
def bank14019 : Fin 1 → Cell := oneBank p14019 ray14019
theorem signs14019 : ∀ j, Signs p14019 (bank14019 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14020 := params 3
abbrev ray14020 := rays 3
def bank14020 : Fin 1 → Cell := oneBank p14020 ray14020
theorem signs14020 : ∀ j, Signs p14020 (bank14020 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14021 := params 4
abbrev ray14021 := rays 4
def bank14021 : Fin 1 → Cell := oneBank p14021 ray14021
theorem signs14021 : ∀ j, Signs p14021 (bank14021 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14022 := params 5
abbrev ray14022 := rays 5
def bank14022 : Fin 1 → Cell := oneBank p14022 ray14022
theorem signs14022 : ∀ j, Signs p14022 (bank14022 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14023 := params 6
abbrev ray14023 := rays 6
def bank14023 : Fin 1 → Cell := oneBank p14023 ray14023
theorem signs14023 : ∀ j, Signs p14023 (bank14023 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14024 := params 7
abbrev ray14024 := rays 7
def bank14024 : Fin 1 → Cell := oneBank p14024 ray14024
theorem signs14024 : ∀ j, Signs p14024 (bank14024 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14025 := params 8
abbrev ray14025 := rays 8
def bank14025 : Fin 1 → Cell := oneBank p14025 ray14025
theorem signs14025 : ∀ j, Signs p14025 (bank14025 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14026 := params 9
abbrev ray14026 := rays 9
def bank14026 : Fin 1 → Cell := oneBank p14026 ray14026
theorem signs14026 : ∀ j, Signs p14026 (bank14026 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14027 := params 10
abbrev ray14027 := rays 10
def bank14027 : Fin 1 → Cell := oneBank p14027 ray14027
theorem signs14027 : ∀ j, Signs p14027 (bank14027 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14028 := params 11
abbrev ray14028 := rays 11
def bank14028 : Fin 1 → Cell := oneBank p14028 ray14028
theorem signs14028 : ∀ j, Signs p14028 (bank14028 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14029 := params 12
abbrev ray14029 := rays 12
def bank14029 : Fin 1 → Cell := oneBank p14029 ray14029
theorem signs14029 : ∀ j, Signs p14029 (bank14029 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14030 := params 13
abbrev ray14030 := rays 13
def bank14030 : Fin 1 → Cell := oneBank p14030 ray14030
theorem signs14030 : ∀ j, Signs p14030 (bank14030 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14031 := params 14
abbrev ray14031 := rays 14
def bank14031 : Fin 1 → Cell := oneBank p14031 ray14031
theorem signs14031 : ∀ j, Signs p14031 (bank14031 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14032 := params 15
abbrev ray14032 := rays 15
def bank14032 : Fin 1 → Cell := oneBank p14032 ray14032
theorem signs14032 : ∀ j, Signs p14032 (bank14032 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14033 := params 16
abbrev ray14033 := rays 16
def bank14033 : Fin 1 → Cell := oneBank p14033 ray14033
theorem signs14033 : ∀ j, Signs p14033 (bank14033 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14034 := params 17
abbrev ray14034 := rays 17
def bank14034 : Fin 1 → Cell := oneBank p14034 ray14034
theorem signs14034 : ∀ j, Signs p14034 (bank14034 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14035 := params 18
abbrev ray14035 := rays 18
def bank14035 : Fin 1 → Cell := oneBank p14035 ray14035
theorem signs14035 : ∀ j, Signs p14035 (bank14035 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14036 := params 19
abbrev ray14036 := rays 19
def bank14036 : Fin 1 → Cell := oneBank p14036 ray14036
theorem signs14036 : ∀ j, Signs p14036 (bank14036 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14037 := params 20
abbrev ray14037 := rays 20
def bank14037 : Fin 1 → Cell := oneBank p14037 ray14037
theorem signs14037 : ∀ j, Signs p14037 (bank14037 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14038 := params 21
abbrev ray14038 := rays 21
def bank14038 : Fin 1 → Cell := oneBank p14038 ray14038
theorem signs14038 : ∀ j, Signs p14038 (bank14038 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14039 := params 22
abbrev ray14039 := rays 22
def bank14039 : Fin 1 → Cell := oneBank p14039 ray14039
theorem signs14039 : ∀ j, Signs p14039 (bank14039 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14040 := params 23
abbrev ray14040 := rays 23
def bank14040 : Fin 1 → Cell := oneBank p14040 ray14040
theorem signs14040 : ∀ j, Signs p14040 (bank14040 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14041 := params 24
abbrev ray14041 := rays 24
def bank14041 : Fin 1 → Cell := oneBank p14041 ray14041
theorem signs14041 : ∀ j, Signs p14041 (bank14041 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14042 := params 25
abbrev ray14042 := rays 25
def bank14042 : Fin 1 → Cell := oneBank p14042 ray14042
theorem signs14042 : ∀ j, Signs p14042 (bank14042 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14043 := params 26
abbrev ray14043 := rays 26
def bank14043 : Fin 1 → Cell := oneBank p14043 ray14043
theorem signs14043 : ∀ j, Signs p14043 (bank14043 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14044 := params 27
abbrev ray14044 := rays 27
def bank14044 : Fin 1 → Cell := oneBank p14044 ray14044
theorem signs14044 : ∀ j, Signs p14044 (bank14044 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14045 := params 28
abbrev ray14045 := rays 28
def bank14045 : Fin 1 → Cell := oneBank p14045 ray14045
theorem signs14045 : ∀ j, Signs p14045 (bank14045 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14046 := params 29
abbrev ray14046 := rays 29
def bank14046 : Fin 1 → Cell := oneBank p14046 ray14046
theorem signs14046 : ∀ j, Signs p14046 (bank14046 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14047 := params 30
abbrev ray14047 := rays 30
def bank14047 : Fin 1 → Cell := oneBank p14047 ray14047
theorem signs14047 : ∀ j, Signs p14047 (bank14047 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14048 := params 31
abbrev ray14048 := rays 31
def bank14048 : Fin 1 → Cell := oneBank p14048 ray14048
theorem signs14048 : ∀ j, Signs p14048 (bank14048 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14017_14048
