/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08129_08160
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98119797927197,98119470407672,98119142866651,98118815304134,98118487720122,98118160114616,98117832487616,98117504839123,98117177169138,98116849477662,98116521764695,98116194030238,98115866274291,98115538496855,98115210697931,98114882877520,98114555035622,98114227172238,98113899287369,98113571381015,98113243453177,98112915503856,98112587533052,98112259540766,98111931526999,98111603491752,98111275435025,98110947356819,98110619257134,98110291135971,98109962993331,98109634829215,98109306643623]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8128+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8129 := params 0
abbrev ray8129 := rays 0
def bank8129 : Fin 2 → Cell := twoBank p8129 ray8129
theorem signs8129 : ∀ j, Signs p8129 (bank8129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8130 := params 1
abbrev ray8130 := rays 1
def bank8130 : Fin 2 → Cell := twoBank p8130 ray8130
theorem signs8130 : ∀ j, Signs p8130 (bank8130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8131 := params 2
abbrev ray8131 := rays 2
def bank8131 : Fin 2 → Cell := twoBank p8131 ray8131
theorem signs8131 : ∀ j, Signs p8131 (bank8131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8132 := params 3
abbrev ray8132 := rays 3
def bank8132 : Fin 2 → Cell := twoBank p8132 ray8132
theorem signs8132 : ∀ j, Signs p8132 (bank8132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8133 := params 4
abbrev ray8133 := rays 4
def bank8133 : Fin 2 → Cell := twoBank p8133 ray8133
theorem signs8133 : ∀ j, Signs p8133 (bank8133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8134 := params 5
abbrev ray8134 := rays 5
def bank8134 : Fin 2 → Cell := twoBank p8134 ray8134
theorem signs8134 : ∀ j, Signs p8134 (bank8134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8135 := params 6
abbrev ray8135 := rays 6
def bank8135 : Fin 2 → Cell := twoBank p8135 ray8135
theorem signs8135 : ∀ j, Signs p8135 (bank8135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8136 := params 7
abbrev ray8136 := rays 7
def bank8136 : Fin 2 → Cell := twoBank p8136 ray8136
theorem signs8136 : ∀ j, Signs p8136 (bank8136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8137 := params 8
abbrev ray8137 := rays 8
def bank8137 : Fin 2 → Cell := twoBank p8137 ray8137
theorem signs8137 : ∀ j, Signs p8137 (bank8137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8138 := params 9
abbrev ray8138 := rays 9
def bank8138 : Fin 2 → Cell := twoBank p8138 ray8138
theorem signs8138 : ∀ j, Signs p8138 (bank8138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8139 := params 10
abbrev ray8139 := rays 10
def bank8139 : Fin 2 → Cell := twoBank p8139 ray8139
theorem signs8139 : ∀ j, Signs p8139 (bank8139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8140 := params 11
abbrev ray8140 := rays 11
def bank8140 : Fin 2 → Cell := twoBank p8140 ray8140
theorem signs8140 : ∀ j, Signs p8140 (bank8140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8141 := params 12
abbrev ray8141 := rays 12
def bank8141 : Fin 2 → Cell := twoBank p8141 ray8141
theorem signs8141 : ∀ j, Signs p8141 (bank8141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8142 := params 13
abbrev ray8142 := rays 13
def bank8142 : Fin 2 → Cell := twoBank p8142 ray8142
theorem signs8142 : ∀ j, Signs p8142 (bank8142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8143 := params 14
abbrev ray8143 := rays 14
def bank8143 : Fin 2 → Cell := twoBank p8143 ray8143
theorem signs8143 : ∀ j, Signs p8143 (bank8143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8144 := params 15
abbrev ray8144 := rays 15
def bank8144 : Fin 2 → Cell := twoBank p8144 ray8144
theorem signs8144 : ∀ j, Signs p8144 (bank8144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8145 := params 16
abbrev ray8145 := rays 16
def bank8145 : Fin 2 → Cell := twoBank p8145 ray8145
theorem signs8145 : ∀ j, Signs p8145 (bank8145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8146 := params 17
abbrev ray8146 := rays 17
def bank8146 : Fin 2 → Cell := twoBank p8146 ray8146
theorem signs8146 : ∀ j, Signs p8146 (bank8146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8147 := params 18
abbrev ray8147 := rays 18
def bank8147 : Fin 2 → Cell := twoBank p8147 ray8147
theorem signs8147 : ∀ j, Signs p8147 (bank8147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8148 := params 19
abbrev ray8148 := rays 19
def bank8148 : Fin 2 → Cell := twoBank p8148 ray8148
theorem signs8148 : ∀ j, Signs p8148 (bank8148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8149 := params 20
abbrev ray8149 := rays 20
def bank8149 : Fin 2 → Cell := twoBank p8149 ray8149
theorem signs8149 : ∀ j, Signs p8149 (bank8149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8150 := params 21
abbrev ray8150 := rays 21
def bank8150 : Fin 2 → Cell := twoBank p8150 ray8150
theorem signs8150 : ∀ j, Signs p8150 (bank8150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8151 := params 22
abbrev ray8151 := rays 22
def bank8151 : Fin 2 → Cell := twoBank p8151 ray8151
theorem signs8151 : ∀ j, Signs p8151 (bank8151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8152 := params 23
abbrev ray8152 := rays 23
def bank8152 : Fin 2 → Cell := twoBank p8152 ray8152
theorem signs8152 : ∀ j, Signs p8152 (bank8152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8153 := params 24
abbrev ray8153 := rays 24
def bank8153 : Fin 2 → Cell := twoBank p8153 ray8153
theorem signs8153 : ∀ j, Signs p8153 (bank8153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8154 := params 25
abbrev ray8154 := rays 25
def bank8154 : Fin 2 → Cell := twoBank p8154 ray8154
theorem signs8154 : ∀ j, Signs p8154 (bank8154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8155 := params 26
abbrev ray8155 := rays 26
def bank8155 : Fin 2 → Cell := twoBank p8155 ray8155
theorem signs8155 : ∀ j, Signs p8155 (bank8155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8156 := params 27
abbrev ray8156 := rays 27
def bank8156 : Fin 2 → Cell := twoBank p8156 ray8156
theorem signs8156 : ∀ j, Signs p8156 (bank8156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8157 := params 28
abbrev ray8157 := rays 28
def bank8157 : Fin 2 → Cell := twoBank p8157 ray8157
theorem signs8157 : ∀ j, Signs p8157 (bank8157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8158 := params 29
abbrev ray8158 := rays 29
def bank8158 : Fin 2 → Cell := twoBank p8158 ray8158
theorem signs8158 : ∀ j, Signs p8158 (bank8158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8159 := params 30
abbrev ray8159 := rays 30
def bank8159 : Fin 2 → Cell := twoBank p8159 ray8159
theorem signs8159 : ∀ j, Signs p8159 (bank8159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8160 := params 31
abbrev ray8160 := rays 31
def bank8160 : Fin 2 → Cell := twoBank p8160 ray8160
theorem signs8160 : ∀ j, Signs p8160 (bank8160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08129_08160
