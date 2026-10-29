/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05281_05312
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98962467805186,98962204644106,98961941459198,98961678250463,98961415017902,98961151761516,98960888481306,98960625177273,98960361849418,98960098497742,98959835122245,98959571722929,98959308299795,98959044852844,98958781382076,98958517887493,98958254369096,98957990826885,98957727260862,98957463671027,98957200057382,98956936419927,98956672758663,98956409073592,98956145364714,98955881632030,98955617875542,98955354095250,98955090291155,98954826463258,98954562611560,98954298736062,98954034836765]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5280+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5281 := params 0
abbrev ray5281 := rays 0
def bank5281 : Fin 2 → Cell := twoBank p5281 ray5281
theorem signs5281 : ∀ j, Signs p5281 (bank5281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5282 := params 1
abbrev ray5282 := rays 1
def bank5282 : Fin 2 → Cell := twoBank p5282 ray5282
theorem signs5282 : ∀ j, Signs p5282 (bank5282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5283 := params 2
abbrev ray5283 := rays 2
def bank5283 : Fin 2 → Cell := twoBank p5283 ray5283
theorem signs5283 : ∀ j, Signs p5283 (bank5283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5284 := params 3
abbrev ray5284 := rays 3
def bank5284 : Fin 2 → Cell := twoBank p5284 ray5284
theorem signs5284 : ∀ j, Signs p5284 (bank5284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5285 := params 4
abbrev ray5285 := rays 4
def bank5285 : Fin 2 → Cell := twoBank p5285 ray5285
theorem signs5285 : ∀ j, Signs p5285 (bank5285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5286 := params 5
abbrev ray5286 := rays 5
def bank5286 : Fin 2 → Cell := twoBank p5286 ray5286
theorem signs5286 : ∀ j, Signs p5286 (bank5286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5287 := params 6
abbrev ray5287 := rays 6
def bank5287 : Fin 2 → Cell := twoBank p5287 ray5287
theorem signs5287 : ∀ j, Signs p5287 (bank5287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5288 := params 7
abbrev ray5288 := rays 7
def bank5288 : Fin 2 → Cell := twoBank p5288 ray5288
theorem signs5288 : ∀ j, Signs p5288 (bank5288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5289 := params 8
abbrev ray5289 := rays 8
def bank5289 : Fin 2 → Cell := twoBank p5289 ray5289
theorem signs5289 : ∀ j, Signs p5289 (bank5289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5290 := params 9
abbrev ray5290 := rays 9
def bank5290 : Fin 2 → Cell := twoBank p5290 ray5290
theorem signs5290 : ∀ j, Signs p5290 (bank5290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5291 := params 10
abbrev ray5291 := rays 10
def bank5291 : Fin 2 → Cell := twoBank p5291 ray5291
theorem signs5291 : ∀ j, Signs p5291 (bank5291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5292 := params 11
abbrev ray5292 := rays 11
def bank5292 : Fin 2 → Cell := twoBank p5292 ray5292
theorem signs5292 : ∀ j, Signs p5292 (bank5292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5293 := params 12
abbrev ray5293 := rays 12
def bank5293 : Fin 2 → Cell := twoBank p5293 ray5293
theorem signs5293 : ∀ j, Signs p5293 (bank5293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5294 := params 13
abbrev ray5294 := rays 13
def bank5294 : Fin 2 → Cell := twoBank p5294 ray5294
theorem signs5294 : ∀ j, Signs p5294 (bank5294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5295 := params 14
abbrev ray5295 := rays 14
def bank5295 : Fin 2 → Cell := twoBank p5295 ray5295
theorem signs5295 : ∀ j, Signs p5295 (bank5295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5296 := params 15
abbrev ray5296 := rays 15
def bank5296 : Fin 2 → Cell := twoBank p5296 ray5296
theorem signs5296 : ∀ j, Signs p5296 (bank5296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5297 := params 16
abbrev ray5297 := rays 16
def bank5297 : Fin 2 → Cell := twoBank p5297 ray5297
theorem signs5297 : ∀ j, Signs p5297 (bank5297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5298 := params 17
abbrev ray5298 := rays 17
def bank5298 : Fin 2 → Cell := twoBank p5298 ray5298
theorem signs5298 : ∀ j, Signs p5298 (bank5298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5299 := params 18
abbrev ray5299 := rays 18
def bank5299 : Fin 2 → Cell := twoBank p5299 ray5299
theorem signs5299 : ∀ j, Signs p5299 (bank5299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5300 := params 19
abbrev ray5300 := rays 19
def bank5300 : Fin 2 → Cell := twoBank p5300 ray5300
theorem signs5300 : ∀ j, Signs p5300 (bank5300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5301 := params 20
abbrev ray5301 := rays 20
def bank5301 : Fin 2 → Cell := twoBank p5301 ray5301
theorem signs5301 : ∀ j, Signs p5301 (bank5301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5302 := params 21
abbrev ray5302 := rays 21
def bank5302 : Fin 2 → Cell := twoBank p5302 ray5302
theorem signs5302 : ∀ j, Signs p5302 (bank5302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5303 := params 22
abbrev ray5303 := rays 22
def bank5303 : Fin 2 → Cell := twoBank p5303 ray5303
theorem signs5303 : ∀ j, Signs p5303 (bank5303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5304 := params 23
abbrev ray5304 := rays 23
def bank5304 : Fin 2 → Cell := twoBank p5304 ray5304
theorem signs5304 : ∀ j, Signs p5304 (bank5304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5305 := params 24
abbrev ray5305 := rays 24
def bank5305 : Fin 2 → Cell := twoBank p5305 ray5305
theorem signs5305 : ∀ j, Signs p5305 (bank5305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5306 := params 25
abbrev ray5306 := rays 25
def bank5306 : Fin 2 → Cell := twoBank p5306 ray5306
theorem signs5306 : ∀ j, Signs p5306 (bank5306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5307 := params 26
abbrev ray5307 := rays 26
def bank5307 : Fin 2 → Cell := twoBank p5307 ray5307
theorem signs5307 : ∀ j, Signs p5307 (bank5307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5308 := params 27
abbrev ray5308 := rays 27
def bank5308 : Fin 2 → Cell := twoBank p5308 ray5308
theorem signs5308 : ∀ j, Signs p5308 (bank5308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5309 := params 28
abbrev ray5309 := rays 28
def bank5309 : Fin 2 → Cell := twoBank p5309 ray5309
theorem signs5309 : ∀ j, Signs p5309 (bank5309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5310 := params 29
abbrev ray5310 := rays 29
def bank5310 : Fin 2 → Cell := twoBank p5310 ray5310
theorem signs5310 : ∀ j, Signs p5310 (bank5310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5311 := params 30
abbrev ray5311 := rays 30
def bank5311 : Fin 2 → Cell := twoBank p5311 ray5311
theorem signs5311 : ∀ j, Signs p5311 (bank5311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5312 := params 31
abbrev ray5312 := rays 31
def bank5312 : Fin 2 → Cell := twoBank p5312 ray5312
theorem signs5312 : ∀ j, Signs p5312 (bank5312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05281_05312
