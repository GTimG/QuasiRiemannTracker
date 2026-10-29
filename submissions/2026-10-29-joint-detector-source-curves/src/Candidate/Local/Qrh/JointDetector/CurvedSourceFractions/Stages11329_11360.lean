/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11329_11360
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96965144570567,96964751389848,96964358189471,96963964969437,96963571729746,96963178470398,96962785191394,96962391892734,96961998574419,96961605236449,96961211878825,96960818501548,96960425104617,96960031688033,96959638251797,96959244795909,96958851320370,96958457825180,96958064310340,96957670775850,96957277221710,96956883647921,96956490054483,96956096441397,96955702808664,96955309156284,96954915484257,96954521792584,96954128081265,96953734350301,96953340599692,96952946829438,96952553039541]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11328+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11329 := params 0
abbrev ray11329 := rays 0
def bank11329 : Fin 2 → Cell := twoBank p11329 ray11329
theorem signs11329 : ∀ j, Signs p11329 (bank11329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11330 := params 1
abbrev ray11330 := rays 1
def bank11330 : Fin 2 → Cell := twoBank p11330 ray11330
theorem signs11330 : ∀ j, Signs p11330 (bank11330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11331 := params 2
abbrev ray11331 := rays 2
def bank11331 : Fin 2 → Cell := twoBank p11331 ray11331
theorem signs11331 : ∀ j, Signs p11331 (bank11331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11332 := params 3
abbrev ray11332 := rays 3
def bank11332 : Fin 2 → Cell := twoBank p11332 ray11332
theorem signs11332 : ∀ j, Signs p11332 (bank11332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11333 := params 4
abbrev ray11333 := rays 4
def bank11333 : Fin 2 → Cell := twoBank p11333 ray11333
theorem signs11333 : ∀ j, Signs p11333 (bank11333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11334 := params 5
abbrev ray11334 := rays 5
def bank11334 : Fin 2 → Cell := twoBank p11334 ray11334
theorem signs11334 : ∀ j, Signs p11334 (bank11334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11335 := params 6
abbrev ray11335 := rays 6
def bank11335 : Fin 2 → Cell := twoBank p11335 ray11335
theorem signs11335 : ∀ j, Signs p11335 (bank11335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11336 := params 7
abbrev ray11336 := rays 7
def bank11336 : Fin 2 → Cell := twoBank p11336 ray11336
theorem signs11336 : ∀ j, Signs p11336 (bank11336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11337 := params 8
abbrev ray11337 := rays 8
def bank11337 : Fin 2 → Cell := twoBank p11337 ray11337
theorem signs11337 : ∀ j, Signs p11337 (bank11337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11338 := params 9
abbrev ray11338 := rays 9
def bank11338 : Fin 2 → Cell := twoBank p11338 ray11338
theorem signs11338 : ∀ j, Signs p11338 (bank11338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11339 := params 10
abbrev ray11339 := rays 10
def bank11339 : Fin 2 → Cell := twoBank p11339 ray11339
theorem signs11339 : ∀ j, Signs p11339 (bank11339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11340 := params 11
abbrev ray11340 := rays 11
def bank11340 : Fin 2 → Cell := twoBank p11340 ray11340
theorem signs11340 : ∀ j, Signs p11340 (bank11340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11341 := params 12
abbrev ray11341 := rays 12
def bank11341 : Fin 2 → Cell := twoBank p11341 ray11341
theorem signs11341 : ∀ j, Signs p11341 (bank11341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11342 := params 13
abbrev ray11342 := rays 13
def bank11342 : Fin 2 → Cell := twoBank p11342 ray11342
theorem signs11342 : ∀ j, Signs p11342 (bank11342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11343 := params 14
abbrev ray11343 := rays 14
def bank11343 : Fin 2 → Cell := twoBank p11343 ray11343
theorem signs11343 : ∀ j, Signs p11343 (bank11343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11344 := params 15
abbrev ray11344 := rays 15
def bank11344 : Fin 2 → Cell := twoBank p11344 ray11344
theorem signs11344 : ∀ j, Signs p11344 (bank11344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11345 := params 16
abbrev ray11345 := rays 16
def bank11345 : Fin 2 → Cell := twoBank p11345 ray11345
theorem signs11345 : ∀ j, Signs p11345 (bank11345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11346 := params 17
abbrev ray11346 := rays 17
def bank11346 : Fin 2 → Cell := twoBank p11346 ray11346
theorem signs11346 : ∀ j, Signs p11346 (bank11346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11347 := params 18
abbrev ray11347 := rays 18
def bank11347 : Fin 2 → Cell := twoBank p11347 ray11347
theorem signs11347 : ∀ j, Signs p11347 (bank11347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11348 := params 19
abbrev ray11348 := rays 19
def bank11348 : Fin 2 → Cell := twoBank p11348 ray11348
theorem signs11348 : ∀ j, Signs p11348 (bank11348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11349 := params 20
abbrev ray11349 := rays 20
def bank11349 : Fin 2 → Cell := twoBank p11349 ray11349
theorem signs11349 : ∀ j, Signs p11349 (bank11349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11350 := params 21
abbrev ray11350 := rays 21
def bank11350 : Fin 2 → Cell := twoBank p11350 ray11350
theorem signs11350 : ∀ j, Signs p11350 (bank11350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11351 := params 22
abbrev ray11351 := rays 22
def bank11351 : Fin 2 → Cell := twoBank p11351 ray11351
theorem signs11351 : ∀ j, Signs p11351 (bank11351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11352 := params 23
abbrev ray11352 := rays 23
def bank11352 : Fin 2 → Cell := twoBank p11352 ray11352
theorem signs11352 : ∀ j, Signs p11352 (bank11352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11353 := params 24
abbrev ray11353 := rays 24
def bank11353 : Fin 2 → Cell := twoBank p11353 ray11353
theorem signs11353 : ∀ j, Signs p11353 (bank11353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11354 := params 25
abbrev ray11354 := rays 25
def bank11354 : Fin 2 → Cell := twoBank p11354 ray11354
theorem signs11354 : ∀ j, Signs p11354 (bank11354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11355 := params 26
abbrev ray11355 := rays 26
def bank11355 : Fin 2 → Cell := twoBank p11355 ray11355
theorem signs11355 : ∀ j, Signs p11355 (bank11355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11356 := params 27
abbrev ray11356 := rays 27
def bank11356 : Fin 2 → Cell := twoBank p11356 ray11356
theorem signs11356 : ∀ j, Signs p11356 (bank11356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11357 := params 28
abbrev ray11357 := rays 28
def bank11357 : Fin 2 → Cell := twoBank p11357 ray11357
theorem signs11357 : ∀ j, Signs p11357 (bank11357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11358 := params 29
abbrev ray11358 := rays 29
def bank11358 : Fin 2 → Cell := twoBank p11358 ray11358
theorem signs11358 : ∀ j, Signs p11358 (bank11358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11359 := params 30
abbrev ray11359 := rays 30
def bank11359 : Fin 2 → Cell := twoBank p11359 ray11359
theorem signs11359 : ∀ j, Signs p11359 (bank11359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11360 := params 31
abbrev ray11360 := rays 31
def bank11360 : Fin 2 → Cell := twoBank p11360 ray11360
theorem signs11360 : ∀ j, Signs p11360 (bank11360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11329_11360
