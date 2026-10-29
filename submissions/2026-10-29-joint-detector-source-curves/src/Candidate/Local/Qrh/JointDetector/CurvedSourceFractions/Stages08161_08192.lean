/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08161_08192
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98109306643623,98108978436556,98108650208015,98108321958000,98107993686512,98107665393552,98107337079120,98107008743217,98106680385844,98106352007002,98106023606691,98105695184912,98105366741665,98105038276951,98104709790771,98104381283126,98104052754016,98103724203442,98103395631405,98103067037905,98102738422943,98102409786520,98102081128636,98101752449292,98101423748489,98101095026228,98100766282509,98100437517332,98100108730699,98099779922610,98099451093066,98099122242068,98098793369616]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8160+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8161 := params 0
abbrev ray8161 := rays 0
def bank8161 : Fin 2 → Cell := twoBank p8161 ray8161
theorem signs8161 : ∀ j, Signs p8161 (bank8161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8162 := params 1
abbrev ray8162 := rays 1
def bank8162 : Fin 2 → Cell := twoBank p8162 ray8162
theorem signs8162 : ∀ j, Signs p8162 (bank8162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8163 := params 2
abbrev ray8163 := rays 2
def bank8163 : Fin 2 → Cell := twoBank p8163 ray8163
theorem signs8163 : ∀ j, Signs p8163 (bank8163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8164 := params 3
abbrev ray8164 := rays 3
def bank8164 : Fin 2 → Cell := twoBank p8164 ray8164
theorem signs8164 : ∀ j, Signs p8164 (bank8164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8165 := params 4
abbrev ray8165 := rays 4
def bank8165 : Fin 2 → Cell := twoBank p8165 ray8165
theorem signs8165 : ∀ j, Signs p8165 (bank8165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8166 := params 5
abbrev ray8166 := rays 5
def bank8166 : Fin 2 → Cell := twoBank p8166 ray8166
theorem signs8166 : ∀ j, Signs p8166 (bank8166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8167 := params 6
abbrev ray8167 := rays 6
def bank8167 : Fin 2 → Cell := twoBank p8167 ray8167
theorem signs8167 : ∀ j, Signs p8167 (bank8167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8168 := params 7
abbrev ray8168 := rays 7
def bank8168 : Fin 2 → Cell := twoBank p8168 ray8168
theorem signs8168 : ∀ j, Signs p8168 (bank8168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8169 := params 8
abbrev ray8169 := rays 8
def bank8169 : Fin 2 → Cell := twoBank p8169 ray8169
theorem signs8169 : ∀ j, Signs p8169 (bank8169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8170 := params 9
abbrev ray8170 := rays 9
def bank8170 : Fin 2 → Cell := twoBank p8170 ray8170
theorem signs8170 : ∀ j, Signs p8170 (bank8170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8171 := params 10
abbrev ray8171 := rays 10
def bank8171 : Fin 2 → Cell := twoBank p8171 ray8171
theorem signs8171 : ∀ j, Signs p8171 (bank8171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8172 := params 11
abbrev ray8172 := rays 11
def bank8172 : Fin 2 → Cell := twoBank p8172 ray8172
theorem signs8172 : ∀ j, Signs p8172 (bank8172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8173 := params 12
abbrev ray8173 := rays 12
def bank8173 : Fin 2 → Cell := twoBank p8173 ray8173
theorem signs8173 : ∀ j, Signs p8173 (bank8173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8174 := params 13
abbrev ray8174 := rays 13
def bank8174 : Fin 2 → Cell := twoBank p8174 ray8174
theorem signs8174 : ∀ j, Signs p8174 (bank8174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8175 := params 14
abbrev ray8175 := rays 14
def bank8175 : Fin 2 → Cell := twoBank p8175 ray8175
theorem signs8175 : ∀ j, Signs p8175 (bank8175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8176 := params 15
abbrev ray8176 := rays 15
def bank8176 : Fin 2 → Cell := twoBank p8176 ray8176
theorem signs8176 : ∀ j, Signs p8176 (bank8176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8177 := params 16
abbrev ray8177 := rays 16
def bank8177 : Fin 2 → Cell := twoBank p8177 ray8177
theorem signs8177 : ∀ j, Signs p8177 (bank8177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8178 := params 17
abbrev ray8178 := rays 17
def bank8178 : Fin 2 → Cell := twoBank p8178 ray8178
theorem signs8178 : ∀ j, Signs p8178 (bank8178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8179 := params 18
abbrev ray8179 := rays 18
def bank8179 : Fin 2 → Cell := twoBank p8179 ray8179
theorem signs8179 : ∀ j, Signs p8179 (bank8179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8180 := params 19
abbrev ray8180 := rays 19
def bank8180 : Fin 2 → Cell := twoBank p8180 ray8180
theorem signs8180 : ∀ j, Signs p8180 (bank8180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8181 := params 20
abbrev ray8181 := rays 20
def bank8181 : Fin 2 → Cell := twoBank p8181 ray8181
theorem signs8181 : ∀ j, Signs p8181 (bank8181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8182 := params 21
abbrev ray8182 := rays 21
def bank8182 : Fin 2 → Cell := twoBank p8182 ray8182
theorem signs8182 : ∀ j, Signs p8182 (bank8182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8183 := params 22
abbrev ray8183 := rays 22
def bank8183 : Fin 2 → Cell := twoBank p8183 ray8183
theorem signs8183 : ∀ j, Signs p8183 (bank8183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8184 := params 23
abbrev ray8184 := rays 23
def bank8184 : Fin 2 → Cell := twoBank p8184 ray8184
theorem signs8184 : ∀ j, Signs p8184 (bank8184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8185 := params 24
abbrev ray8185 := rays 24
def bank8185 : Fin 2 → Cell := twoBank p8185 ray8185
theorem signs8185 : ∀ j, Signs p8185 (bank8185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8186 := params 25
abbrev ray8186 := rays 25
def bank8186 : Fin 2 → Cell := twoBank p8186 ray8186
theorem signs8186 : ∀ j, Signs p8186 (bank8186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8187 := params 26
abbrev ray8187 := rays 26
def bank8187 : Fin 2 → Cell := twoBank p8187 ray8187
theorem signs8187 : ∀ j, Signs p8187 (bank8187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8188 := params 27
abbrev ray8188 := rays 27
def bank8188 : Fin 2 → Cell := twoBank p8188 ray8188
theorem signs8188 : ∀ j, Signs p8188 (bank8188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8189 := params 28
abbrev ray8189 := rays 28
def bank8189 : Fin 2 → Cell := twoBank p8189 ray8189
theorem signs8189 : ∀ j, Signs p8189 (bank8189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8190 := params 29
abbrev ray8190 := rays 29
def bank8190 : Fin 2 → Cell := twoBank p8190 ray8190
theorem signs8190 : ∀ j, Signs p8190 (bank8190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8191 := params 30
abbrev ray8191 := rays 30
def bank8191 : Fin 2 → Cell := twoBank p8191 ray8191
theorem signs8191 : ∀ j, Signs p8191 (bank8191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8192 := params 31
abbrev ray8192 := rays 31
def bank8192 : Fin 2 → Cell := twoBank p8192 ray8192
theorem signs8192 : ∀ j, Signs p8192 (bank8192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08161_08192
