/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09249_09280
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97739661556313,97739310374930,97738959172775,97738607949848,97738256706151,97737905441683,97737554156446,97737202850439,97736851523664,97736500176121,97736148807811,97735797418734,97735446008891,97735094578283,97734743126910,97734391654773,97734040161872,97733688648208,97733337113781,97732985558593,97732633982643,97732282385933,97731930768463,97731579130233,97731227471244,97730875791497,97730524090993,97730172369732,97729820627714,97729468864940,97729117081411,97728765277128,97728413452091]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9248+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9249 := params 0
abbrev ray9249 := rays 0
def bank9249 : Fin 2 → Cell := twoBank p9249 ray9249
theorem signs9249 : ∀ j, Signs p9249 (bank9249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9250 := params 1
abbrev ray9250 := rays 1
def bank9250 : Fin 2 → Cell := twoBank p9250 ray9250
theorem signs9250 : ∀ j, Signs p9250 (bank9250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9251 := params 2
abbrev ray9251 := rays 2
def bank9251 : Fin 2 → Cell := twoBank p9251 ray9251
theorem signs9251 : ∀ j, Signs p9251 (bank9251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9252 := params 3
abbrev ray9252 := rays 3
def bank9252 : Fin 2 → Cell := twoBank p9252 ray9252
theorem signs9252 : ∀ j, Signs p9252 (bank9252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9253 := params 4
abbrev ray9253 := rays 4
def bank9253 : Fin 2 → Cell := twoBank p9253 ray9253
theorem signs9253 : ∀ j, Signs p9253 (bank9253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9254 := params 5
abbrev ray9254 := rays 5
def bank9254 : Fin 2 → Cell := twoBank p9254 ray9254
theorem signs9254 : ∀ j, Signs p9254 (bank9254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9255 := params 6
abbrev ray9255 := rays 6
def bank9255 : Fin 2 → Cell := twoBank p9255 ray9255
theorem signs9255 : ∀ j, Signs p9255 (bank9255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9256 := params 7
abbrev ray9256 := rays 7
def bank9256 : Fin 2 → Cell := twoBank p9256 ray9256
theorem signs9256 : ∀ j, Signs p9256 (bank9256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9257 := params 8
abbrev ray9257 := rays 8
def bank9257 : Fin 2 → Cell := twoBank p9257 ray9257
theorem signs9257 : ∀ j, Signs p9257 (bank9257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9258 := params 9
abbrev ray9258 := rays 9
def bank9258 : Fin 2 → Cell := twoBank p9258 ray9258
theorem signs9258 : ∀ j, Signs p9258 (bank9258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9259 := params 10
abbrev ray9259 := rays 10
def bank9259 : Fin 2 → Cell := twoBank p9259 ray9259
theorem signs9259 : ∀ j, Signs p9259 (bank9259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9260 := params 11
abbrev ray9260 := rays 11
def bank9260 : Fin 2 → Cell := twoBank p9260 ray9260
theorem signs9260 : ∀ j, Signs p9260 (bank9260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9261 := params 12
abbrev ray9261 := rays 12
def bank9261 : Fin 2 → Cell := twoBank p9261 ray9261
theorem signs9261 : ∀ j, Signs p9261 (bank9261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9262 := params 13
abbrev ray9262 := rays 13
def bank9262 : Fin 2 → Cell := twoBank p9262 ray9262
theorem signs9262 : ∀ j, Signs p9262 (bank9262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9263 := params 14
abbrev ray9263 := rays 14
def bank9263 : Fin 2 → Cell := twoBank p9263 ray9263
theorem signs9263 : ∀ j, Signs p9263 (bank9263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9264 := params 15
abbrev ray9264 := rays 15
def bank9264 : Fin 2 → Cell := twoBank p9264 ray9264
theorem signs9264 : ∀ j, Signs p9264 (bank9264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9265 := params 16
abbrev ray9265 := rays 16
def bank9265 : Fin 2 → Cell := twoBank p9265 ray9265
theorem signs9265 : ∀ j, Signs p9265 (bank9265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9266 := params 17
abbrev ray9266 := rays 17
def bank9266 : Fin 2 → Cell := twoBank p9266 ray9266
theorem signs9266 : ∀ j, Signs p9266 (bank9266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9267 := params 18
abbrev ray9267 := rays 18
def bank9267 : Fin 2 → Cell := twoBank p9267 ray9267
theorem signs9267 : ∀ j, Signs p9267 (bank9267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9268 := params 19
abbrev ray9268 := rays 19
def bank9268 : Fin 2 → Cell := twoBank p9268 ray9268
theorem signs9268 : ∀ j, Signs p9268 (bank9268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9269 := params 20
abbrev ray9269 := rays 20
def bank9269 : Fin 2 → Cell := twoBank p9269 ray9269
theorem signs9269 : ∀ j, Signs p9269 (bank9269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9270 := params 21
abbrev ray9270 := rays 21
def bank9270 : Fin 2 → Cell := twoBank p9270 ray9270
theorem signs9270 : ∀ j, Signs p9270 (bank9270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9271 := params 22
abbrev ray9271 := rays 22
def bank9271 : Fin 2 → Cell := twoBank p9271 ray9271
theorem signs9271 : ∀ j, Signs p9271 (bank9271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9272 := params 23
abbrev ray9272 := rays 23
def bank9272 : Fin 2 → Cell := twoBank p9272 ray9272
theorem signs9272 : ∀ j, Signs p9272 (bank9272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9273 := params 24
abbrev ray9273 := rays 24
def bank9273 : Fin 2 → Cell := twoBank p9273 ray9273
theorem signs9273 : ∀ j, Signs p9273 (bank9273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9274 := params 25
abbrev ray9274 := rays 25
def bank9274 : Fin 2 → Cell := twoBank p9274 ray9274
theorem signs9274 : ∀ j, Signs p9274 (bank9274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9275 := params 26
abbrev ray9275 := rays 26
def bank9275 : Fin 2 → Cell := twoBank p9275 ray9275
theorem signs9275 : ∀ j, Signs p9275 (bank9275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9276 := params 27
abbrev ray9276 := rays 27
def bank9276 : Fin 2 → Cell := twoBank p9276 ray9276
theorem signs9276 : ∀ j, Signs p9276 (bank9276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9277 := params 28
abbrev ray9277 := rays 28
def bank9277 : Fin 2 → Cell := twoBank p9277 ray9277
theorem signs9277 : ∀ j, Signs p9277 (bank9277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9278 := params 29
abbrev ray9278 := rays 29
def bank9278 : Fin 2 → Cell := twoBank p9278 ray9278
theorem signs9278 : ∀ j, Signs p9278 (bank9278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9279 := params 30
abbrev ray9279 := rays 30
def bank9279 : Fin 2 → Cell := twoBank p9279 ray9279
theorem signs9279 : ∀ j, Signs p9279 (bank9279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9280 := params 31
abbrev ray9280 := rays 31
def bank9280 : Fin 2 → Cell := twoBank p9280 ray9280
theorem signs9280 : ∀ j, Signs p9280 (bank9280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09249_09280
