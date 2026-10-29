/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07361_07392
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98364931645379,98364620845019,98364310022608,98363999178148,98363688311638,98363377423080,98363066512474,98362755579821,98362444625122,98362133648378,98361822649589,98361511628756,98361200585880,98360889520962,98360578434002,98360267325002,98359956193961,98359645040881,98359333865762,98359022668606,98358711449413,98358400208183,98358088944918,98357777659618,98357466352284,98357155022916,98356843671516,98356532298084,98356220902621,98355909485128,98355598045605,98355286584053,98354975100473]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7360+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7361 := params 0
abbrev ray7361 := rays 0
def bank7361 : Fin 2 → Cell := twoBank p7361 ray7361
theorem signs7361 : ∀ j, Signs p7361 (bank7361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7362 := params 1
abbrev ray7362 := rays 1
def bank7362 : Fin 2 → Cell := twoBank p7362 ray7362
theorem signs7362 : ∀ j, Signs p7362 (bank7362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7363 := params 2
abbrev ray7363 := rays 2
def bank7363 : Fin 2 → Cell := twoBank p7363 ray7363
theorem signs7363 : ∀ j, Signs p7363 (bank7363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7364 := params 3
abbrev ray7364 := rays 3
def bank7364 : Fin 2 → Cell := twoBank p7364 ray7364
theorem signs7364 : ∀ j, Signs p7364 (bank7364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7365 := params 4
abbrev ray7365 := rays 4
def bank7365 : Fin 2 → Cell := twoBank p7365 ray7365
theorem signs7365 : ∀ j, Signs p7365 (bank7365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7366 := params 5
abbrev ray7366 := rays 5
def bank7366 : Fin 2 → Cell := twoBank p7366 ray7366
theorem signs7366 : ∀ j, Signs p7366 (bank7366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7367 := params 6
abbrev ray7367 := rays 6
def bank7367 : Fin 2 → Cell := twoBank p7367 ray7367
theorem signs7367 : ∀ j, Signs p7367 (bank7367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7368 := params 7
abbrev ray7368 := rays 7
def bank7368 : Fin 2 → Cell := twoBank p7368 ray7368
theorem signs7368 : ∀ j, Signs p7368 (bank7368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7369 := params 8
abbrev ray7369 := rays 8
def bank7369 : Fin 2 → Cell := twoBank p7369 ray7369
theorem signs7369 : ∀ j, Signs p7369 (bank7369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7370 := params 9
abbrev ray7370 := rays 9
def bank7370 : Fin 2 → Cell := twoBank p7370 ray7370
theorem signs7370 : ∀ j, Signs p7370 (bank7370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7371 := params 10
abbrev ray7371 := rays 10
def bank7371 : Fin 2 → Cell := twoBank p7371 ray7371
theorem signs7371 : ∀ j, Signs p7371 (bank7371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7372 := params 11
abbrev ray7372 := rays 11
def bank7372 : Fin 2 → Cell := twoBank p7372 ray7372
theorem signs7372 : ∀ j, Signs p7372 (bank7372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7373 := params 12
abbrev ray7373 := rays 12
def bank7373 : Fin 2 → Cell := twoBank p7373 ray7373
theorem signs7373 : ∀ j, Signs p7373 (bank7373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7374 := params 13
abbrev ray7374 := rays 13
def bank7374 : Fin 2 → Cell := twoBank p7374 ray7374
theorem signs7374 : ∀ j, Signs p7374 (bank7374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7375 := params 14
abbrev ray7375 := rays 14
def bank7375 : Fin 2 → Cell := twoBank p7375 ray7375
theorem signs7375 : ∀ j, Signs p7375 (bank7375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7376 := params 15
abbrev ray7376 := rays 15
def bank7376 : Fin 2 → Cell := twoBank p7376 ray7376
theorem signs7376 : ∀ j, Signs p7376 (bank7376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7377 := params 16
abbrev ray7377 := rays 16
def bank7377 : Fin 2 → Cell := twoBank p7377 ray7377
theorem signs7377 : ∀ j, Signs p7377 (bank7377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7378 := params 17
abbrev ray7378 := rays 17
def bank7378 : Fin 2 → Cell := twoBank p7378 ray7378
theorem signs7378 : ∀ j, Signs p7378 (bank7378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7379 := params 18
abbrev ray7379 := rays 18
def bank7379 : Fin 2 → Cell := twoBank p7379 ray7379
theorem signs7379 : ∀ j, Signs p7379 (bank7379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7380 := params 19
abbrev ray7380 := rays 19
def bank7380 : Fin 2 → Cell := twoBank p7380 ray7380
theorem signs7380 : ∀ j, Signs p7380 (bank7380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7381 := params 20
abbrev ray7381 := rays 20
def bank7381 : Fin 2 → Cell := twoBank p7381 ray7381
theorem signs7381 : ∀ j, Signs p7381 (bank7381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7382 := params 21
abbrev ray7382 := rays 21
def bank7382 : Fin 2 → Cell := twoBank p7382 ray7382
theorem signs7382 : ∀ j, Signs p7382 (bank7382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7383 := params 22
abbrev ray7383 := rays 22
def bank7383 : Fin 2 → Cell := twoBank p7383 ray7383
theorem signs7383 : ∀ j, Signs p7383 (bank7383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7384 := params 23
abbrev ray7384 := rays 23
def bank7384 : Fin 2 → Cell := twoBank p7384 ray7384
theorem signs7384 : ∀ j, Signs p7384 (bank7384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7385 := params 24
abbrev ray7385 := rays 24
def bank7385 : Fin 2 → Cell := twoBank p7385 ray7385
theorem signs7385 : ∀ j, Signs p7385 (bank7385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7386 := params 25
abbrev ray7386 := rays 25
def bank7386 : Fin 2 → Cell := twoBank p7386 ray7386
theorem signs7386 : ∀ j, Signs p7386 (bank7386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7387 := params 26
abbrev ray7387 := rays 26
def bank7387 : Fin 2 → Cell := twoBank p7387 ray7387
theorem signs7387 : ∀ j, Signs p7387 (bank7387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7388 := params 27
abbrev ray7388 := rays 27
def bank7388 : Fin 2 → Cell := twoBank p7388 ray7388
theorem signs7388 : ∀ j, Signs p7388 (bank7388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7389 := params 28
abbrev ray7389 := rays 28
def bank7389 : Fin 2 → Cell := twoBank p7389 ray7389
theorem signs7389 : ∀ j, Signs p7389 (bank7389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7390 := params 29
abbrev ray7390 := rays 29
def bank7390 : Fin 2 → Cell := twoBank p7390 ray7390
theorem signs7390 : ∀ j, Signs p7390 (bank7390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7391 := params 30
abbrev ray7391 := rays 30
def bank7391 : Fin 2 → Cell := twoBank p7391 ray7391
theorem signs7391 : ∀ j, Signs p7391 (bank7391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7392 := params 31
abbrev ray7392 := rays 31
def bank7392 : Fin 2 → Cell := twoBank p7392 ray7392
theorem signs7392 : ∀ j, Signs p7392 (bank7392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07361_07392
