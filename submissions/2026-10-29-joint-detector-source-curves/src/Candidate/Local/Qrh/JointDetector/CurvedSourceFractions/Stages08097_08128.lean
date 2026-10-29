/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08097_08128
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98130267197765,98129940366489,98129613513695,98129286639383,98128959743554,98128632826208,98128305887347,98127978926971,98127651945080,98127324941676,98126997916759,98126670870329,98126343802388,98126016712936,98125689601974,98125362469502,98125035315521,98124708140032,98124380943036,98124053724533,98123726484524,98123399223010,98123071939991,98122744635468,98122417309442,98122089961913,98121762592882,98121435202350,98121107790318,98120780356786,98120452901755,98120125425225,98119797927197]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8096+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8097 := params 0
abbrev ray8097 := rays 0
def bank8097 : Fin 2 → Cell := twoBank p8097 ray8097
theorem signs8097 : ∀ j, Signs p8097 (bank8097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8098 := params 1
abbrev ray8098 := rays 1
def bank8098 : Fin 2 → Cell := twoBank p8098 ray8098
theorem signs8098 : ∀ j, Signs p8098 (bank8098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8099 := params 2
abbrev ray8099 := rays 2
def bank8099 : Fin 2 → Cell := twoBank p8099 ray8099
theorem signs8099 : ∀ j, Signs p8099 (bank8099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8100 := params 3
abbrev ray8100 := rays 3
def bank8100 : Fin 2 → Cell := twoBank p8100 ray8100
theorem signs8100 : ∀ j, Signs p8100 (bank8100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8101 := params 4
abbrev ray8101 := rays 4
def bank8101 : Fin 2 → Cell := twoBank p8101 ray8101
theorem signs8101 : ∀ j, Signs p8101 (bank8101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8102 := params 5
abbrev ray8102 := rays 5
def bank8102 : Fin 2 → Cell := twoBank p8102 ray8102
theorem signs8102 : ∀ j, Signs p8102 (bank8102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8103 := params 6
abbrev ray8103 := rays 6
def bank8103 : Fin 2 → Cell := twoBank p8103 ray8103
theorem signs8103 : ∀ j, Signs p8103 (bank8103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8104 := params 7
abbrev ray8104 := rays 7
def bank8104 : Fin 2 → Cell := twoBank p8104 ray8104
theorem signs8104 : ∀ j, Signs p8104 (bank8104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8105 := params 8
abbrev ray8105 := rays 8
def bank8105 : Fin 2 → Cell := twoBank p8105 ray8105
theorem signs8105 : ∀ j, Signs p8105 (bank8105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8106 := params 9
abbrev ray8106 := rays 9
def bank8106 : Fin 2 → Cell := twoBank p8106 ray8106
theorem signs8106 : ∀ j, Signs p8106 (bank8106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8107 := params 10
abbrev ray8107 := rays 10
def bank8107 : Fin 2 → Cell := twoBank p8107 ray8107
theorem signs8107 : ∀ j, Signs p8107 (bank8107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8108 := params 11
abbrev ray8108 := rays 11
def bank8108 : Fin 2 → Cell := twoBank p8108 ray8108
theorem signs8108 : ∀ j, Signs p8108 (bank8108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8109 := params 12
abbrev ray8109 := rays 12
def bank8109 : Fin 2 → Cell := twoBank p8109 ray8109
theorem signs8109 : ∀ j, Signs p8109 (bank8109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8110 := params 13
abbrev ray8110 := rays 13
def bank8110 : Fin 2 → Cell := twoBank p8110 ray8110
theorem signs8110 : ∀ j, Signs p8110 (bank8110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8111 := params 14
abbrev ray8111 := rays 14
def bank8111 : Fin 2 → Cell := twoBank p8111 ray8111
theorem signs8111 : ∀ j, Signs p8111 (bank8111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8112 := params 15
abbrev ray8112 := rays 15
def bank8112 : Fin 2 → Cell := twoBank p8112 ray8112
theorem signs8112 : ∀ j, Signs p8112 (bank8112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8113 := params 16
abbrev ray8113 := rays 16
def bank8113 : Fin 2 → Cell := twoBank p8113 ray8113
theorem signs8113 : ∀ j, Signs p8113 (bank8113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8114 := params 17
abbrev ray8114 := rays 17
def bank8114 : Fin 2 → Cell := twoBank p8114 ray8114
theorem signs8114 : ∀ j, Signs p8114 (bank8114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8115 := params 18
abbrev ray8115 := rays 18
def bank8115 : Fin 2 → Cell := twoBank p8115 ray8115
theorem signs8115 : ∀ j, Signs p8115 (bank8115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8116 := params 19
abbrev ray8116 := rays 19
def bank8116 : Fin 2 → Cell := twoBank p8116 ray8116
theorem signs8116 : ∀ j, Signs p8116 (bank8116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8117 := params 20
abbrev ray8117 := rays 20
def bank8117 : Fin 2 → Cell := twoBank p8117 ray8117
theorem signs8117 : ∀ j, Signs p8117 (bank8117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8118 := params 21
abbrev ray8118 := rays 21
def bank8118 : Fin 2 → Cell := twoBank p8118 ray8118
theorem signs8118 : ∀ j, Signs p8118 (bank8118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8119 := params 22
abbrev ray8119 := rays 22
def bank8119 : Fin 2 → Cell := twoBank p8119 ray8119
theorem signs8119 : ∀ j, Signs p8119 (bank8119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8120 := params 23
abbrev ray8120 := rays 23
def bank8120 : Fin 2 → Cell := twoBank p8120 ray8120
theorem signs8120 : ∀ j, Signs p8120 (bank8120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8121 := params 24
abbrev ray8121 := rays 24
def bank8121 : Fin 2 → Cell := twoBank p8121 ray8121
theorem signs8121 : ∀ j, Signs p8121 (bank8121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8122 := params 25
abbrev ray8122 := rays 25
def bank8122 : Fin 2 → Cell := twoBank p8122 ray8122
theorem signs8122 : ∀ j, Signs p8122 (bank8122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8123 := params 26
abbrev ray8123 := rays 26
def bank8123 : Fin 2 → Cell := twoBank p8123 ray8123
theorem signs8123 : ∀ j, Signs p8123 (bank8123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8124 := params 27
abbrev ray8124 := rays 27
def bank8124 : Fin 2 → Cell := twoBank p8124 ray8124
theorem signs8124 : ∀ j, Signs p8124 (bank8124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8125 := params 28
abbrev ray8125 := rays 28
def bank8125 : Fin 2 → Cell := twoBank p8125 ray8125
theorem signs8125 : ∀ j, Signs p8125 (bank8125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8126 := params 29
abbrev ray8126 := rays 29
def bank8126 : Fin 2 → Cell := twoBank p8126 ray8126
theorem signs8126 : ∀ j, Signs p8126 (bank8126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8127 := params 30
abbrev ray8127 := rays 30
def bank8127 : Fin 2 → Cell := twoBank p8127 ray8127
theorem signs8127 : ∀ j, Signs p8127 (bank8127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8128 := params 31
abbrev ray8128 := rays 31
def bank8128 : Fin 2 → Cell := twoBank p8128 ray8128
theorem signs8128 : ∀ j, Signs p8128 (bank8128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08097_08128
