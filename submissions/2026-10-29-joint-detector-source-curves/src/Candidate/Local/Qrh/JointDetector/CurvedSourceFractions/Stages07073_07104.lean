/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07073_07104
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98453521427686,98453217009671,98452912569384,98452608106827,98452303621999,98451999114902,98451694585537,98451390033904,98451085460004,98450780863838,98450476245406,98450171604710,98449866941750,98449562256527,98449257549041,98448952819294,98448648067286,98448343293018,98448038496491,98447733677706,98447428836663,98447123973363,98446819087807,98446514179996,98446209249930,98445904297611,98445599323039,98445294326215,98444989307139,98444684265813,98444379202237,98444074116412,98443769008338]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7072+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7073 := params 0
abbrev ray7073 := rays 0
def bank7073 : Fin 2 → Cell := twoBank p7073 ray7073
theorem signs7073 : ∀ j, Signs p7073 (bank7073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7074 := params 1
abbrev ray7074 := rays 1
def bank7074 : Fin 2 → Cell := twoBank p7074 ray7074
theorem signs7074 : ∀ j, Signs p7074 (bank7074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7075 := params 2
abbrev ray7075 := rays 2
def bank7075 : Fin 2 → Cell := twoBank p7075 ray7075
theorem signs7075 : ∀ j, Signs p7075 (bank7075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7076 := params 3
abbrev ray7076 := rays 3
def bank7076 : Fin 2 → Cell := twoBank p7076 ray7076
theorem signs7076 : ∀ j, Signs p7076 (bank7076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7077 := params 4
abbrev ray7077 := rays 4
def bank7077 : Fin 2 → Cell := twoBank p7077 ray7077
theorem signs7077 : ∀ j, Signs p7077 (bank7077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7078 := params 5
abbrev ray7078 := rays 5
def bank7078 : Fin 2 → Cell := twoBank p7078 ray7078
theorem signs7078 : ∀ j, Signs p7078 (bank7078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7079 := params 6
abbrev ray7079 := rays 6
def bank7079 : Fin 2 → Cell := twoBank p7079 ray7079
theorem signs7079 : ∀ j, Signs p7079 (bank7079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7080 := params 7
abbrev ray7080 := rays 7
def bank7080 : Fin 2 → Cell := twoBank p7080 ray7080
theorem signs7080 : ∀ j, Signs p7080 (bank7080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7081 := params 8
abbrev ray7081 := rays 8
def bank7081 : Fin 2 → Cell := twoBank p7081 ray7081
theorem signs7081 : ∀ j, Signs p7081 (bank7081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7082 := params 9
abbrev ray7082 := rays 9
def bank7082 : Fin 2 → Cell := twoBank p7082 ray7082
theorem signs7082 : ∀ j, Signs p7082 (bank7082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7083 := params 10
abbrev ray7083 := rays 10
def bank7083 : Fin 2 → Cell := twoBank p7083 ray7083
theorem signs7083 : ∀ j, Signs p7083 (bank7083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7084 := params 11
abbrev ray7084 := rays 11
def bank7084 : Fin 2 → Cell := twoBank p7084 ray7084
theorem signs7084 : ∀ j, Signs p7084 (bank7084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7085 := params 12
abbrev ray7085 := rays 12
def bank7085 : Fin 2 → Cell := twoBank p7085 ray7085
theorem signs7085 : ∀ j, Signs p7085 (bank7085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7086 := params 13
abbrev ray7086 := rays 13
def bank7086 : Fin 2 → Cell := twoBank p7086 ray7086
theorem signs7086 : ∀ j, Signs p7086 (bank7086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7087 := params 14
abbrev ray7087 := rays 14
def bank7087 : Fin 2 → Cell := twoBank p7087 ray7087
theorem signs7087 : ∀ j, Signs p7087 (bank7087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7088 := params 15
abbrev ray7088 := rays 15
def bank7088 : Fin 2 → Cell := twoBank p7088 ray7088
theorem signs7088 : ∀ j, Signs p7088 (bank7088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7089 := params 16
abbrev ray7089 := rays 16
def bank7089 : Fin 2 → Cell := twoBank p7089 ray7089
theorem signs7089 : ∀ j, Signs p7089 (bank7089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7090 := params 17
abbrev ray7090 := rays 17
def bank7090 : Fin 2 → Cell := twoBank p7090 ray7090
theorem signs7090 : ∀ j, Signs p7090 (bank7090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7091 := params 18
abbrev ray7091 := rays 18
def bank7091 : Fin 2 → Cell := twoBank p7091 ray7091
theorem signs7091 : ∀ j, Signs p7091 (bank7091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7092 := params 19
abbrev ray7092 := rays 19
def bank7092 : Fin 2 → Cell := twoBank p7092 ray7092
theorem signs7092 : ∀ j, Signs p7092 (bank7092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7093 := params 20
abbrev ray7093 := rays 20
def bank7093 : Fin 2 → Cell := twoBank p7093 ray7093
theorem signs7093 : ∀ j, Signs p7093 (bank7093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7094 := params 21
abbrev ray7094 := rays 21
def bank7094 : Fin 2 → Cell := twoBank p7094 ray7094
theorem signs7094 : ∀ j, Signs p7094 (bank7094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7095 := params 22
abbrev ray7095 := rays 22
def bank7095 : Fin 2 → Cell := twoBank p7095 ray7095
theorem signs7095 : ∀ j, Signs p7095 (bank7095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7096 := params 23
abbrev ray7096 := rays 23
def bank7096 : Fin 2 → Cell := twoBank p7096 ray7096
theorem signs7096 : ∀ j, Signs p7096 (bank7096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7097 := params 24
abbrev ray7097 := rays 24
def bank7097 : Fin 2 → Cell := twoBank p7097 ray7097
theorem signs7097 : ∀ j, Signs p7097 (bank7097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7098 := params 25
abbrev ray7098 := rays 25
def bank7098 : Fin 2 → Cell := twoBank p7098 ray7098
theorem signs7098 : ∀ j, Signs p7098 (bank7098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7099 := params 26
abbrev ray7099 := rays 26
def bank7099 : Fin 2 → Cell := twoBank p7099 ray7099
theorem signs7099 : ∀ j, Signs p7099 (bank7099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7100 := params 27
abbrev ray7100 := rays 27
def bank7100 : Fin 2 → Cell := twoBank p7100 ray7100
theorem signs7100 : ∀ j, Signs p7100 (bank7100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7101 := params 28
abbrev ray7101 := rays 28
def bank7101 : Fin 2 → Cell := twoBank p7101 ray7101
theorem signs7101 : ∀ j, Signs p7101 (bank7101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7102 := params 29
abbrev ray7102 := rays 29
def bank7102 : Fin 2 → Cell := twoBank p7102 ray7102
theorem signs7102 : ∀ j, Signs p7102 (bank7102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7103 := params 30
abbrev ray7103 := rays 30
def bank7103 : Fin 2 → Cell := twoBank p7103 ray7103
theorem signs7103 : ∀ j, Signs p7103 (bank7103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7104 := params 31
abbrev ray7104 := rays 31
def bank7104 : Fin 2 → Cell := twoBank p7104 ray7104
theorem signs7104 : ∀ j, Signs p7104 (bank7104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07073_07104
