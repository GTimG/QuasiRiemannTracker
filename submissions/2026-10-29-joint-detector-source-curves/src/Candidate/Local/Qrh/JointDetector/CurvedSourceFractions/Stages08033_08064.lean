/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08033_08064
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98151139609204,98150814156556,98150488682345,98150163186571,98149837669236,98149512130340,98149186569884,98148860987868,98148535384294,98148209759161,98147884112471,98147558444224,98147232754421,98146907043063,98146581310150,98146255555683,98145929779663,98145603982091,98145278162967,98144952322292,98144626460066,98144300576291,98143974670967,98143648744094,98143322795674,98142996825707,98142670834193,98142344821134,98142018786530,98141692730382,98141366652690,98141040553456,98140714432679]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8032+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8033 := params 0
abbrev ray8033 := rays 0
def bank8033 : Fin 2 → Cell := twoBank p8033 ray8033
theorem signs8033 : ∀ j, Signs p8033 (bank8033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8034 := params 1
abbrev ray8034 := rays 1
def bank8034 : Fin 2 → Cell := twoBank p8034 ray8034
theorem signs8034 : ∀ j, Signs p8034 (bank8034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8035 := params 2
abbrev ray8035 := rays 2
def bank8035 : Fin 2 → Cell := twoBank p8035 ray8035
theorem signs8035 : ∀ j, Signs p8035 (bank8035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8036 := params 3
abbrev ray8036 := rays 3
def bank8036 : Fin 2 → Cell := twoBank p8036 ray8036
theorem signs8036 : ∀ j, Signs p8036 (bank8036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8037 := params 4
abbrev ray8037 := rays 4
def bank8037 : Fin 2 → Cell := twoBank p8037 ray8037
theorem signs8037 : ∀ j, Signs p8037 (bank8037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8038 := params 5
abbrev ray8038 := rays 5
def bank8038 : Fin 2 → Cell := twoBank p8038 ray8038
theorem signs8038 : ∀ j, Signs p8038 (bank8038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8039 := params 6
abbrev ray8039 := rays 6
def bank8039 : Fin 2 → Cell := twoBank p8039 ray8039
theorem signs8039 : ∀ j, Signs p8039 (bank8039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8040 := params 7
abbrev ray8040 := rays 7
def bank8040 : Fin 2 → Cell := twoBank p8040 ray8040
theorem signs8040 : ∀ j, Signs p8040 (bank8040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8041 := params 8
abbrev ray8041 := rays 8
def bank8041 : Fin 2 → Cell := twoBank p8041 ray8041
theorem signs8041 : ∀ j, Signs p8041 (bank8041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8042 := params 9
abbrev ray8042 := rays 9
def bank8042 : Fin 2 → Cell := twoBank p8042 ray8042
theorem signs8042 : ∀ j, Signs p8042 (bank8042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8043 := params 10
abbrev ray8043 := rays 10
def bank8043 : Fin 2 → Cell := twoBank p8043 ray8043
theorem signs8043 : ∀ j, Signs p8043 (bank8043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8044 := params 11
abbrev ray8044 := rays 11
def bank8044 : Fin 2 → Cell := twoBank p8044 ray8044
theorem signs8044 : ∀ j, Signs p8044 (bank8044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8045 := params 12
abbrev ray8045 := rays 12
def bank8045 : Fin 2 → Cell := twoBank p8045 ray8045
theorem signs8045 : ∀ j, Signs p8045 (bank8045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8046 := params 13
abbrev ray8046 := rays 13
def bank8046 : Fin 2 → Cell := twoBank p8046 ray8046
theorem signs8046 : ∀ j, Signs p8046 (bank8046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8047 := params 14
abbrev ray8047 := rays 14
def bank8047 : Fin 2 → Cell := twoBank p8047 ray8047
theorem signs8047 : ∀ j, Signs p8047 (bank8047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8048 := params 15
abbrev ray8048 := rays 15
def bank8048 : Fin 2 → Cell := twoBank p8048 ray8048
theorem signs8048 : ∀ j, Signs p8048 (bank8048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8049 := params 16
abbrev ray8049 := rays 16
def bank8049 : Fin 2 → Cell := twoBank p8049 ray8049
theorem signs8049 : ∀ j, Signs p8049 (bank8049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8050 := params 17
abbrev ray8050 := rays 17
def bank8050 : Fin 2 → Cell := twoBank p8050 ray8050
theorem signs8050 : ∀ j, Signs p8050 (bank8050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8051 := params 18
abbrev ray8051 := rays 18
def bank8051 : Fin 2 → Cell := twoBank p8051 ray8051
theorem signs8051 : ∀ j, Signs p8051 (bank8051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8052 := params 19
abbrev ray8052 := rays 19
def bank8052 : Fin 2 → Cell := twoBank p8052 ray8052
theorem signs8052 : ∀ j, Signs p8052 (bank8052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8053 := params 20
abbrev ray8053 := rays 20
def bank8053 : Fin 2 → Cell := twoBank p8053 ray8053
theorem signs8053 : ∀ j, Signs p8053 (bank8053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8054 := params 21
abbrev ray8054 := rays 21
def bank8054 : Fin 2 → Cell := twoBank p8054 ray8054
theorem signs8054 : ∀ j, Signs p8054 (bank8054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8055 := params 22
abbrev ray8055 := rays 22
def bank8055 : Fin 2 → Cell := twoBank p8055 ray8055
theorem signs8055 : ∀ j, Signs p8055 (bank8055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8056 := params 23
abbrev ray8056 := rays 23
def bank8056 : Fin 2 → Cell := twoBank p8056 ray8056
theorem signs8056 : ∀ j, Signs p8056 (bank8056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8057 := params 24
abbrev ray8057 := rays 24
def bank8057 : Fin 2 → Cell := twoBank p8057 ray8057
theorem signs8057 : ∀ j, Signs p8057 (bank8057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8058 := params 25
abbrev ray8058 := rays 25
def bank8058 : Fin 2 → Cell := twoBank p8058 ray8058
theorem signs8058 : ∀ j, Signs p8058 (bank8058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8059 := params 26
abbrev ray8059 := rays 26
def bank8059 : Fin 2 → Cell := twoBank p8059 ray8059
theorem signs8059 : ∀ j, Signs p8059 (bank8059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8060 := params 27
abbrev ray8060 := rays 27
def bank8060 : Fin 2 → Cell := twoBank p8060 ray8060
theorem signs8060 : ∀ j, Signs p8060 (bank8060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8061 := params 28
abbrev ray8061 := rays 28
def bank8061 : Fin 2 → Cell := twoBank p8061 ray8061
theorem signs8061 : ∀ j, Signs p8061 (bank8061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8062 := params 29
abbrev ray8062 := rays 29
def bank8062 : Fin 2 → Cell := twoBank p8062 ray8062
theorem signs8062 : ∀ j, Signs p8062 (bank8062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8063 := params 30
abbrev ray8063 := rays 30
def bank8063 : Fin 2 → Cell := twoBank p8063 ray8063
theorem signs8063 : ∀ j, Signs p8063 (bank8063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8064 := params 31
abbrev ray8064 := rays 31
def bank8064 : Fin 2 → Cell := twoBank p8064 ray8064
theorem signs8064 : ∀ j, Signs p8064 (bank8064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08033_08064
