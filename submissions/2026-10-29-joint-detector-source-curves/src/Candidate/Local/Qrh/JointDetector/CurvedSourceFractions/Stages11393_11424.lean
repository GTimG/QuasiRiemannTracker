/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11393_11424
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96939941393659,96939546955776,96939152498265,96938758021127,96938363524362,96937969007970,96937574471952,96937179916308,96936785341039,96936390746145,96935996131627,96935601497485,96935206843720,96934812170332,96934417477322,96934022764690,96933628032436,96933233280561,96932838509066,96932443717951,96932048907216,96931654076862,96931259226889,96930864357298,96930469468089,96930074559263,96929679630820,96929284682761,96928889715086,96928494727796,96928099720891,96927704694371,96927309648237]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11392+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11393 := params 0
abbrev ray11393 := rays 0
def bank11393 : Fin 2 → Cell := twoBank p11393 ray11393
theorem signs11393 : ∀ j, Signs p11393 (bank11393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11394 := params 1
abbrev ray11394 := rays 1
def bank11394 : Fin 2 → Cell := twoBank p11394 ray11394
theorem signs11394 : ∀ j, Signs p11394 (bank11394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11395 := params 2
abbrev ray11395 := rays 2
def bank11395 : Fin 2 → Cell := twoBank p11395 ray11395
theorem signs11395 : ∀ j, Signs p11395 (bank11395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11396 := params 3
abbrev ray11396 := rays 3
def bank11396 : Fin 2 → Cell := twoBank p11396 ray11396
theorem signs11396 : ∀ j, Signs p11396 (bank11396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11397 := params 4
abbrev ray11397 := rays 4
def bank11397 : Fin 2 → Cell := twoBank p11397 ray11397
theorem signs11397 : ∀ j, Signs p11397 (bank11397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11398 := params 5
abbrev ray11398 := rays 5
def bank11398 : Fin 2 → Cell := twoBank p11398 ray11398
theorem signs11398 : ∀ j, Signs p11398 (bank11398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11399 := params 6
abbrev ray11399 := rays 6
def bank11399 : Fin 2 → Cell := twoBank p11399 ray11399
theorem signs11399 : ∀ j, Signs p11399 (bank11399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11400 := params 7
abbrev ray11400 := rays 7
def bank11400 : Fin 2 → Cell := twoBank p11400 ray11400
theorem signs11400 : ∀ j, Signs p11400 (bank11400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11401 := params 8
abbrev ray11401 := rays 8
def bank11401 : Fin 2 → Cell := twoBank p11401 ray11401
theorem signs11401 : ∀ j, Signs p11401 (bank11401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11402 := params 9
abbrev ray11402 := rays 9
def bank11402 : Fin 2 → Cell := twoBank p11402 ray11402
theorem signs11402 : ∀ j, Signs p11402 (bank11402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11403 := params 10
abbrev ray11403 := rays 10
def bank11403 : Fin 2 → Cell := twoBank p11403 ray11403
theorem signs11403 : ∀ j, Signs p11403 (bank11403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11404 := params 11
abbrev ray11404 := rays 11
def bank11404 : Fin 2 → Cell := twoBank p11404 ray11404
theorem signs11404 : ∀ j, Signs p11404 (bank11404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11405 := params 12
abbrev ray11405 := rays 12
def bank11405 : Fin 2 → Cell := twoBank p11405 ray11405
theorem signs11405 : ∀ j, Signs p11405 (bank11405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11406 := params 13
abbrev ray11406 := rays 13
def bank11406 : Fin 2 → Cell := twoBank p11406 ray11406
theorem signs11406 : ∀ j, Signs p11406 (bank11406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11407 := params 14
abbrev ray11407 := rays 14
def bank11407 : Fin 2 → Cell := twoBank p11407 ray11407
theorem signs11407 : ∀ j, Signs p11407 (bank11407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11408 := params 15
abbrev ray11408 := rays 15
def bank11408 : Fin 2 → Cell := twoBank p11408 ray11408
theorem signs11408 : ∀ j, Signs p11408 (bank11408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11409 := params 16
abbrev ray11409 := rays 16
def bank11409 : Fin 2 → Cell := twoBank p11409 ray11409
theorem signs11409 : ∀ j, Signs p11409 (bank11409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11410 := params 17
abbrev ray11410 := rays 17
def bank11410 : Fin 2 → Cell := twoBank p11410 ray11410
theorem signs11410 : ∀ j, Signs p11410 (bank11410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11411 := params 18
abbrev ray11411 := rays 18
def bank11411 : Fin 2 → Cell := twoBank p11411 ray11411
theorem signs11411 : ∀ j, Signs p11411 (bank11411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11412 := params 19
abbrev ray11412 := rays 19
def bank11412 : Fin 2 → Cell := twoBank p11412 ray11412
theorem signs11412 : ∀ j, Signs p11412 (bank11412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11413 := params 20
abbrev ray11413 := rays 20
def bank11413 : Fin 2 → Cell := twoBank p11413 ray11413
theorem signs11413 : ∀ j, Signs p11413 (bank11413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11414 := params 21
abbrev ray11414 := rays 21
def bank11414 : Fin 2 → Cell := twoBank p11414 ray11414
theorem signs11414 : ∀ j, Signs p11414 (bank11414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11415 := params 22
abbrev ray11415 := rays 22
def bank11415 : Fin 2 → Cell := twoBank p11415 ray11415
theorem signs11415 : ∀ j, Signs p11415 (bank11415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11416 := params 23
abbrev ray11416 := rays 23
def bank11416 : Fin 2 → Cell := twoBank p11416 ray11416
theorem signs11416 : ∀ j, Signs p11416 (bank11416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11417 := params 24
abbrev ray11417 := rays 24
def bank11417 : Fin 2 → Cell := twoBank p11417 ray11417
theorem signs11417 : ∀ j, Signs p11417 (bank11417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11418 := params 25
abbrev ray11418 := rays 25
def bank11418 : Fin 2 → Cell := twoBank p11418 ray11418
theorem signs11418 : ∀ j, Signs p11418 (bank11418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11419 := params 26
abbrev ray11419 := rays 26
def bank11419 : Fin 2 → Cell := twoBank p11419 ray11419
theorem signs11419 : ∀ j, Signs p11419 (bank11419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11420 := params 27
abbrev ray11420 := rays 27
def bank11420 : Fin 2 → Cell := twoBank p11420 ray11420
theorem signs11420 : ∀ j, Signs p11420 (bank11420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11421 := params 28
abbrev ray11421 := rays 28
def bank11421 : Fin 2 → Cell := twoBank p11421 ray11421
theorem signs11421 : ∀ j, Signs p11421 (bank11421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11422 := params 29
abbrev ray11422 := rays 29
def bank11422 : Fin 2 → Cell := twoBank p11422 ray11422
theorem signs11422 : ∀ j, Signs p11422 (bank11422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11423 := params 30
abbrev ray11423 := rays 30
def bank11423 : Fin 2 → Cell := twoBank p11423 ray11423
theorem signs11423 : ∀ j, Signs p11423 (bank11423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11424 := params 31
abbrev ray11424 := rays 31
def bank11424 : Fin 2 → Cell := twoBank p11424 ray11424
theorem signs11424 : ∀ j, Signs p11424 (bank11424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11393_11424
