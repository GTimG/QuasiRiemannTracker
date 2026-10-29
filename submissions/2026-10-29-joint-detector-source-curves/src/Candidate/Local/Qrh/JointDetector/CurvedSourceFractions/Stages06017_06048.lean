/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06017_06048
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98762398691299,98762118246127,98761837777806,98761557286337,98761276771721,98760996233959,98760715673052,98760435089001,98760154481806,98759873851469,98759593197990,98759312521370,98759031821610,98758751098711,98758470352674,98758189583500,98757908791189,98757627975743,98757347137162,98757066275448,98756785390601,98756504482622,98756223551512,98755942597271,98755661619901,98755380619403,98755099595777,98754818549024,98754537479146,98754256386143,98753975270016,98753694130766,98753412968393]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6016+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6017 := params 0
abbrev ray6017 := rays 0
def bank6017 : Fin 2 → Cell := twoBank p6017 ray6017
theorem signs6017 : ∀ j, Signs p6017 (bank6017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6018 := params 1
abbrev ray6018 := rays 1
def bank6018 : Fin 2 → Cell := twoBank p6018 ray6018
theorem signs6018 : ∀ j, Signs p6018 (bank6018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6019 := params 2
abbrev ray6019 := rays 2
def bank6019 : Fin 2 → Cell := twoBank p6019 ray6019
theorem signs6019 : ∀ j, Signs p6019 (bank6019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6020 := params 3
abbrev ray6020 := rays 3
def bank6020 : Fin 2 → Cell := twoBank p6020 ray6020
theorem signs6020 : ∀ j, Signs p6020 (bank6020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6021 := params 4
abbrev ray6021 := rays 4
def bank6021 : Fin 2 → Cell := twoBank p6021 ray6021
theorem signs6021 : ∀ j, Signs p6021 (bank6021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6022 := params 5
abbrev ray6022 := rays 5
def bank6022 : Fin 2 → Cell := twoBank p6022 ray6022
theorem signs6022 : ∀ j, Signs p6022 (bank6022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6023 := params 6
abbrev ray6023 := rays 6
def bank6023 : Fin 2 → Cell := twoBank p6023 ray6023
theorem signs6023 : ∀ j, Signs p6023 (bank6023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6024 := params 7
abbrev ray6024 := rays 7
def bank6024 : Fin 2 → Cell := twoBank p6024 ray6024
theorem signs6024 : ∀ j, Signs p6024 (bank6024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6025 := params 8
abbrev ray6025 := rays 8
def bank6025 : Fin 2 → Cell := twoBank p6025 ray6025
theorem signs6025 : ∀ j, Signs p6025 (bank6025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6026 := params 9
abbrev ray6026 := rays 9
def bank6026 : Fin 2 → Cell := twoBank p6026 ray6026
theorem signs6026 : ∀ j, Signs p6026 (bank6026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6027 := params 10
abbrev ray6027 := rays 10
def bank6027 : Fin 2 → Cell := twoBank p6027 ray6027
theorem signs6027 : ∀ j, Signs p6027 (bank6027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6028 := params 11
abbrev ray6028 := rays 11
def bank6028 : Fin 2 → Cell := twoBank p6028 ray6028
theorem signs6028 : ∀ j, Signs p6028 (bank6028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6029 := params 12
abbrev ray6029 := rays 12
def bank6029 : Fin 2 → Cell := twoBank p6029 ray6029
theorem signs6029 : ∀ j, Signs p6029 (bank6029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6030 := params 13
abbrev ray6030 := rays 13
def bank6030 : Fin 2 → Cell := twoBank p6030 ray6030
theorem signs6030 : ∀ j, Signs p6030 (bank6030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6031 := params 14
abbrev ray6031 := rays 14
def bank6031 : Fin 2 → Cell := twoBank p6031 ray6031
theorem signs6031 : ∀ j, Signs p6031 (bank6031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6032 := params 15
abbrev ray6032 := rays 15
def bank6032 : Fin 2 → Cell := twoBank p6032 ray6032
theorem signs6032 : ∀ j, Signs p6032 (bank6032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6033 := params 16
abbrev ray6033 := rays 16
def bank6033 : Fin 2 → Cell := twoBank p6033 ray6033
theorem signs6033 : ∀ j, Signs p6033 (bank6033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6034 := params 17
abbrev ray6034 := rays 17
def bank6034 : Fin 2 → Cell := twoBank p6034 ray6034
theorem signs6034 : ∀ j, Signs p6034 (bank6034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6035 := params 18
abbrev ray6035 := rays 18
def bank6035 : Fin 2 → Cell := twoBank p6035 ray6035
theorem signs6035 : ∀ j, Signs p6035 (bank6035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6036 := params 19
abbrev ray6036 := rays 19
def bank6036 : Fin 2 → Cell := twoBank p6036 ray6036
theorem signs6036 : ∀ j, Signs p6036 (bank6036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6037 := params 20
abbrev ray6037 := rays 20
def bank6037 : Fin 2 → Cell := twoBank p6037 ray6037
theorem signs6037 : ∀ j, Signs p6037 (bank6037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6038 := params 21
abbrev ray6038 := rays 21
def bank6038 : Fin 2 → Cell := twoBank p6038 ray6038
theorem signs6038 : ∀ j, Signs p6038 (bank6038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6039 := params 22
abbrev ray6039 := rays 22
def bank6039 : Fin 2 → Cell := twoBank p6039 ray6039
theorem signs6039 : ∀ j, Signs p6039 (bank6039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6040 := params 23
abbrev ray6040 := rays 23
def bank6040 : Fin 2 → Cell := twoBank p6040 ray6040
theorem signs6040 : ∀ j, Signs p6040 (bank6040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6041 := params 24
abbrev ray6041 := rays 24
def bank6041 : Fin 2 → Cell := twoBank p6041 ray6041
theorem signs6041 : ∀ j, Signs p6041 (bank6041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6042 := params 25
abbrev ray6042 := rays 25
def bank6042 : Fin 2 → Cell := twoBank p6042 ray6042
theorem signs6042 : ∀ j, Signs p6042 (bank6042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6043 := params 26
abbrev ray6043 := rays 26
def bank6043 : Fin 2 → Cell := twoBank p6043 ray6043
theorem signs6043 : ∀ j, Signs p6043 (bank6043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6044 := params 27
abbrev ray6044 := rays 27
def bank6044 : Fin 2 → Cell := twoBank p6044 ray6044
theorem signs6044 : ∀ j, Signs p6044 (bank6044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6045 := params 28
abbrev ray6045 := rays 28
def bank6045 : Fin 2 → Cell := twoBank p6045 ray6045
theorem signs6045 : ∀ j, Signs p6045 (bank6045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6046 := params 29
abbrev ray6046 := rays 29
def bank6046 : Fin 2 → Cell := twoBank p6046 ray6046
theorem signs6046 : ∀ j, Signs p6046 (bank6046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6047 := params 30
abbrev ray6047 := rays 30
def bank6047 : Fin 2 → Cell := twoBank p6047 ray6047
theorem signs6047 : ∀ j, Signs p6047 (bank6047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6048 := params 31
abbrev ray6048 := rays 31
def bank6048 : Fin 2 → Cell := twoBank p6048 ray6048
theorem signs6048 : ∀ j, Signs p6048 (bank6048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06017_06048
