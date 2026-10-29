/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09185_09216
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97762093931070,97761744080364,97761394208847,97761044316520,97760694403383,97760344469437,97759994514683,97759644539121,97759294542751,97758944525575,97758594487592,97758244428804,97757894349211,97757544248814,97757194127613,97756843985609,97756493822803,97756143639195,97755793434785,97755443209575,97755092963565,97754742696755,97754392409147,97754042100740,97753691771536,97753341421535,97752991050737,97752640659144,97752290246755,97751939813572,97751589359595,97751238884825,97750888389262]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9184+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9185 := params 0
abbrev ray9185 := rays 0
def bank9185 : Fin 2 → Cell := twoBank p9185 ray9185
theorem signs9185 : ∀ j, Signs p9185 (bank9185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9186 := params 1
abbrev ray9186 := rays 1
def bank9186 : Fin 2 → Cell := twoBank p9186 ray9186
theorem signs9186 : ∀ j, Signs p9186 (bank9186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9187 := params 2
abbrev ray9187 := rays 2
def bank9187 : Fin 2 → Cell := twoBank p9187 ray9187
theorem signs9187 : ∀ j, Signs p9187 (bank9187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9188 := params 3
abbrev ray9188 := rays 3
def bank9188 : Fin 2 → Cell := twoBank p9188 ray9188
theorem signs9188 : ∀ j, Signs p9188 (bank9188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9189 := params 4
abbrev ray9189 := rays 4
def bank9189 : Fin 2 → Cell := twoBank p9189 ray9189
theorem signs9189 : ∀ j, Signs p9189 (bank9189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9190 := params 5
abbrev ray9190 := rays 5
def bank9190 : Fin 2 → Cell := twoBank p9190 ray9190
theorem signs9190 : ∀ j, Signs p9190 (bank9190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9191 := params 6
abbrev ray9191 := rays 6
def bank9191 : Fin 2 → Cell := twoBank p9191 ray9191
theorem signs9191 : ∀ j, Signs p9191 (bank9191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9192 := params 7
abbrev ray9192 := rays 7
def bank9192 : Fin 2 → Cell := twoBank p9192 ray9192
theorem signs9192 : ∀ j, Signs p9192 (bank9192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9193 := params 8
abbrev ray9193 := rays 8
def bank9193 : Fin 2 → Cell := twoBank p9193 ray9193
theorem signs9193 : ∀ j, Signs p9193 (bank9193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9194 := params 9
abbrev ray9194 := rays 9
def bank9194 : Fin 2 → Cell := twoBank p9194 ray9194
theorem signs9194 : ∀ j, Signs p9194 (bank9194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9195 := params 10
abbrev ray9195 := rays 10
def bank9195 : Fin 2 → Cell := twoBank p9195 ray9195
theorem signs9195 : ∀ j, Signs p9195 (bank9195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9196 := params 11
abbrev ray9196 := rays 11
def bank9196 : Fin 2 → Cell := twoBank p9196 ray9196
theorem signs9196 : ∀ j, Signs p9196 (bank9196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9197 := params 12
abbrev ray9197 := rays 12
def bank9197 : Fin 2 → Cell := twoBank p9197 ray9197
theorem signs9197 : ∀ j, Signs p9197 (bank9197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9198 := params 13
abbrev ray9198 := rays 13
def bank9198 : Fin 2 → Cell := twoBank p9198 ray9198
theorem signs9198 : ∀ j, Signs p9198 (bank9198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9199 := params 14
abbrev ray9199 := rays 14
def bank9199 : Fin 2 → Cell := twoBank p9199 ray9199
theorem signs9199 : ∀ j, Signs p9199 (bank9199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9200 := params 15
abbrev ray9200 := rays 15
def bank9200 : Fin 2 → Cell := twoBank p9200 ray9200
theorem signs9200 : ∀ j, Signs p9200 (bank9200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9201 := params 16
abbrev ray9201 := rays 16
def bank9201 : Fin 2 → Cell := twoBank p9201 ray9201
theorem signs9201 : ∀ j, Signs p9201 (bank9201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9202 := params 17
abbrev ray9202 := rays 17
def bank9202 : Fin 2 → Cell := twoBank p9202 ray9202
theorem signs9202 : ∀ j, Signs p9202 (bank9202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9203 := params 18
abbrev ray9203 := rays 18
def bank9203 : Fin 2 → Cell := twoBank p9203 ray9203
theorem signs9203 : ∀ j, Signs p9203 (bank9203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9204 := params 19
abbrev ray9204 := rays 19
def bank9204 : Fin 2 → Cell := twoBank p9204 ray9204
theorem signs9204 : ∀ j, Signs p9204 (bank9204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9205 := params 20
abbrev ray9205 := rays 20
def bank9205 : Fin 2 → Cell := twoBank p9205 ray9205
theorem signs9205 : ∀ j, Signs p9205 (bank9205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9206 := params 21
abbrev ray9206 := rays 21
def bank9206 : Fin 2 → Cell := twoBank p9206 ray9206
theorem signs9206 : ∀ j, Signs p9206 (bank9206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9207 := params 22
abbrev ray9207 := rays 22
def bank9207 : Fin 2 → Cell := twoBank p9207 ray9207
theorem signs9207 : ∀ j, Signs p9207 (bank9207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9208 := params 23
abbrev ray9208 := rays 23
def bank9208 : Fin 2 → Cell := twoBank p9208 ray9208
theorem signs9208 : ∀ j, Signs p9208 (bank9208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9209 := params 24
abbrev ray9209 := rays 24
def bank9209 : Fin 2 → Cell := twoBank p9209 ray9209
theorem signs9209 : ∀ j, Signs p9209 (bank9209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9210 := params 25
abbrev ray9210 := rays 25
def bank9210 : Fin 2 → Cell := twoBank p9210 ray9210
theorem signs9210 : ∀ j, Signs p9210 (bank9210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9211 := params 26
abbrev ray9211 := rays 26
def bank9211 : Fin 2 → Cell := twoBank p9211 ray9211
theorem signs9211 : ∀ j, Signs p9211 (bank9211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9212 := params 27
abbrev ray9212 := rays 27
def bank9212 : Fin 2 → Cell := twoBank p9212 ray9212
theorem signs9212 : ∀ j, Signs p9212 (bank9212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9213 := params 28
abbrev ray9213 := rays 28
def bank9213 : Fin 2 → Cell := twoBank p9213 ray9213
theorem signs9213 : ∀ j, Signs p9213 (bank9213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9214 := params 29
abbrev ray9214 := rays 29
def bank9214 : Fin 2 → Cell := twoBank p9214 ray9214
theorem signs9214 : ∀ j, Signs p9214 (bank9214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9215 := params 30
abbrev ray9215 := rays 30
def bank9215 : Fin 2 → Cell := twoBank p9215 ray9215
theorem signs9215 : ∀ j, Signs p9215 (bank9215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9216 := params 31
abbrev ray9216 := rays 31
def bank9216 : Fin 2 → Cell := twoBank p9216 ray9216
theorem signs9216 : ∀ j, Signs p9216 (bank9216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09185_09216
