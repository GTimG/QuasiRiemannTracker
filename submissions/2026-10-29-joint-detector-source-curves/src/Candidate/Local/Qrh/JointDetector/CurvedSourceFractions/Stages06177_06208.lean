/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06177_06208
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98717233600808,98716949463003,98716665302189,98716381118367,98716096911538,98715812681703,98715528428863,98715244153019,98714959854171,98714675532320,98714391187467,98714106819614,98713822428760,98713538014907,98713253578056,98712969118207,98712684635362,98712400129521,98712115600685,98711831048855,98711546474032,98711261876217,98710977255410,98710692611613,98710407944826,98710123255050,98709838542286,98709553806535,98709269047798,98708984266075,98708699461368,98708414633677,98708129783003]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6176+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6177 := params 0
abbrev ray6177 := rays 0
def bank6177 : Fin 2 → Cell := twoBank p6177 ray6177
theorem signs6177 : ∀ j, Signs p6177 (bank6177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6178 := params 1
abbrev ray6178 := rays 1
def bank6178 : Fin 2 → Cell := twoBank p6178 ray6178
theorem signs6178 : ∀ j, Signs p6178 (bank6178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6179 := params 2
abbrev ray6179 := rays 2
def bank6179 : Fin 2 → Cell := twoBank p6179 ray6179
theorem signs6179 : ∀ j, Signs p6179 (bank6179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6180 := params 3
abbrev ray6180 := rays 3
def bank6180 : Fin 2 → Cell := twoBank p6180 ray6180
theorem signs6180 : ∀ j, Signs p6180 (bank6180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6181 := params 4
abbrev ray6181 := rays 4
def bank6181 : Fin 2 → Cell := twoBank p6181 ray6181
theorem signs6181 : ∀ j, Signs p6181 (bank6181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6182 := params 5
abbrev ray6182 := rays 5
def bank6182 : Fin 2 → Cell := twoBank p6182 ray6182
theorem signs6182 : ∀ j, Signs p6182 (bank6182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6183 := params 6
abbrev ray6183 := rays 6
def bank6183 : Fin 2 → Cell := twoBank p6183 ray6183
theorem signs6183 : ∀ j, Signs p6183 (bank6183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6184 := params 7
abbrev ray6184 := rays 7
def bank6184 : Fin 2 → Cell := twoBank p6184 ray6184
theorem signs6184 : ∀ j, Signs p6184 (bank6184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6185 := params 8
abbrev ray6185 := rays 8
def bank6185 : Fin 2 → Cell := twoBank p6185 ray6185
theorem signs6185 : ∀ j, Signs p6185 (bank6185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6186 := params 9
abbrev ray6186 := rays 9
def bank6186 : Fin 2 → Cell := twoBank p6186 ray6186
theorem signs6186 : ∀ j, Signs p6186 (bank6186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6187 := params 10
abbrev ray6187 := rays 10
def bank6187 : Fin 2 → Cell := twoBank p6187 ray6187
theorem signs6187 : ∀ j, Signs p6187 (bank6187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6188 := params 11
abbrev ray6188 := rays 11
def bank6188 : Fin 2 → Cell := twoBank p6188 ray6188
theorem signs6188 : ∀ j, Signs p6188 (bank6188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6189 := params 12
abbrev ray6189 := rays 12
def bank6189 : Fin 2 → Cell := twoBank p6189 ray6189
theorem signs6189 : ∀ j, Signs p6189 (bank6189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6190 := params 13
abbrev ray6190 := rays 13
def bank6190 : Fin 2 → Cell := twoBank p6190 ray6190
theorem signs6190 : ∀ j, Signs p6190 (bank6190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6191 := params 14
abbrev ray6191 := rays 14
def bank6191 : Fin 2 → Cell := twoBank p6191 ray6191
theorem signs6191 : ∀ j, Signs p6191 (bank6191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6192 := params 15
abbrev ray6192 := rays 15
def bank6192 : Fin 2 → Cell := twoBank p6192 ray6192
theorem signs6192 : ∀ j, Signs p6192 (bank6192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6193 := params 16
abbrev ray6193 := rays 16
def bank6193 : Fin 2 → Cell := twoBank p6193 ray6193
theorem signs6193 : ∀ j, Signs p6193 (bank6193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6194 := params 17
abbrev ray6194 := rays 17
def bank6194 : Fin 2 → Cell := twoBank p6194 ray6194
theorem signs6194 : ∀ j, Signs p6194 (bank6194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6195 := params 18
abbrev ray6195 := rays 18
def bank6195 : Fin 2 → Cell := twoBank p6195 ray6195
theorem signs6195 : ∀ j, Signs p6195 (bank6195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6196 := params 19
abbrev ray6196 := rays 19
def bank6196 : Fin 2 → Cell := twoBank p6196 ray6196
theorem signs6196 : ∀ j, Signs p6196 (bank6196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6197 := params 20
abbrev ray6197 := rays 20
def bank6197 : Fin 2 → Cell := twoBank p6197 ray6197
theorem signs6197 : ∀ j, Signs p6197 (bank6197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6198 := params 21
abbrev ray6198 := rays 21
def bank6198 : Fin 2 → Cell := twoBank p6198 ray6198
theorem signs6198 : ∀ j, Signs p6198 (bank6198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6199 := params 22
abbrev ray6199 := rays 22
def bank6199 : Fin 2 → Cell := twoBank p6199 ray6199
theorem signs6199 : ∀ j, Signs p6199 (bank6199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6200 := params 23
abbrev ray6200 := rays 23
def bank6200 : Fin 2 → Cell := twoBank p6200 ray6200
theorem signs6200 : ∀ j, Signs p6200 (bank6200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6201 := params 24
abbrev ray6201 := rays 24
def bank6201 : Fin 2 → Cell := twoBank p6201 ray6201
theorem signs6201 : ∀ j, Signs p6201 (bank6201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6202 := params 25
abbrev ray6202 := rays 25
def bank6202 : Fin 2 → Cell := twoBank p6202 ray6202
theorem signs6202 : ∀ j, Signs p6202 (bank6202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6203 := params 26
abbrev ray6203 := rays 26
def bank6203 : Fin 2 → Cell := twoBank p6203 ray6203
theorem signs6203 : ∀ j, Signs p6203 (bank6203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6204 := params 27
abbrev ray6204 := rays 27
def bank6204 : Fin 2 → Cell := twoBank p6204 ray6204
theorem signs6204 : ∀ j, Signs p6204 (bank6204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6205 := params 28
abbrev ray6205 := rays 28
def bank6205 : Fin 2 → Cell := twoBank p6205 ray6205
theorem signs6205 : ∀ j, Signs p6205 (bank6205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6206 := params 29
abbrev ray6206 := rays 29
def bank6206 : Fin 2 → Cell := twoBank p6206 ray6206
theorem signs6206 : ∀ j, Signs p6206 (bank6206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6207 := params 30
abbrev ray6207 := rays 30
def bank6207 : Fin 2 → Cell := twoBank p6207 ray6207
theorem signs6207 : ∀ j, Signs p6207 (bank6207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6208 := params 31
abbrev ray6208 := rays 31
def bank6208 : Fin 2 → Cell := twoBank p6208 ray6208
theorem signs6208 : ∀ j, Signs p6208 (bank6208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06177_06208
