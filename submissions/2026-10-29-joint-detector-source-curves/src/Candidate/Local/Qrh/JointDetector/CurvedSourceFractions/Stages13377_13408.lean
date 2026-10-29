/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13377_13408
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96119769387523,96119338324145,96118907244423,96118476148358,96118045035949,96117613907197,96117182762102,96116751600664,96116320422883,96115889228760,96115458018295,96115026791488,96114595548340,96114164288850,96113733013019,96113301720847,96112870412334,96112439087481,96112007746288,96111576388755,96111145014882,96110713624669,96110282218117,96109850795226,96109419355996,96108987900427,96108556428520,96108124940275,96107693435692,96107261914771,96106830377513,96106398823917,96105967253984]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13376+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13377 := params 0
abbrev ray13377 := rays 0
def bank13377 : Fin 1 → Cell := oneBank p13377 ray13377
theorem signs13377 : ∀ j, Signs p13377 (bank13377 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13378 := params 1
abbrev ray13378 := rays 1
def bank13378 : Fin 1 → Cell := oneBank p13378 ray13378
theorem signs13378 : ∀ j, Signs p13378 (bank13378 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13379 := params 2
abbrev ray13379 := rays 2
def bank13379 : Fin 1 → Cell := oneBank p13379 ray13379
theorem signs13379 : ∀ j, Signs p13379 (bank13379 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13380 := params 3
abbrev ray13380 := rays 3
def bank13380 : Fin 1 → Cell := oneBank p13380 ray13380
theorem signs13380 : ∀ j, Signs p13380 (bank13380 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13381 := params 4
abbrev ray13381 := rays 4
def bank13381 : Fin 1 → Cell := oneBank p13381 ray13381
theorem signs13381 : ∀ j, Signs p13381 (bank13381 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13382 := params 5
abbrev ray13382 := rays 5
def bank13382 : Fin 1 → Cell := oneBank p13382 ray13382
theorem signs13382 : ∀ j, Signs p13382 (bank13382 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13383 := params 6
abbrev ray13383 := rays 6
def bank13383 : Fin 1 → Cell := oneBank p13383 ray13383
theorem signs13383 : ∀ j, Signs p13383 (bank13383 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13384 := params 7
abbrev ray13384 := rays 7
def bank13384 : Fin 1 → Cell := oneBank p13384 ray13384
theorem signs13384 : ∀ j, Signs p13384 (bank13384 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13385 := params 8
abbrev ray13385 := rays 8
def bank13385 : Fin 1 → Cell := oneBank p13385 ray13385
theorem signs13385 : ∀ j, Signs p13385 (bank13385 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13386 := params 9
abbrev ray13386 := rays 9
def bank13386 : Fin 1 → Cell := oneBank p13386 ray13386
theorem signs13386 : ∀ j, Signs p13386 (bank13386 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13387 := params 10
abbrev ray13387 := rays 10
def bank13387 : Fin 1 → Cell := oneBank p13387 ray13387
theorem signs13387 : ∀ j, Signs p13387 (bank13387 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13388 := params 11
abbrev ray13388 := rays 11
def bank13388 : Fin 1 → Cell := oneBank p13388 ray13388
theorem signs13388 : ∀ j, Signs p13388 (bank13388 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13389 := params 12
abbrev ray13389 := rays 12
def bank13389 : Fin 1 → Cell := oneBank p13389 ray13389
theorem signs13389 : ∀ j, Signs p13389 (bank13389 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13390 := params 13
abbrev ray13390 := rays 13
def bank13390 : Fin 1 → Cell := oneBank p13390 ray13390
theorem signs13390 : ∀ j, Signs p13390 (bank13390 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13391 := params 14
abbrev ray13391 := rays 14
def bank13391 : Fin 1 → Cell := oneBank p13391 ray13391
theorem signs13391 : ∀ j, Signs p13391 (bank13391 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13392 := params 15
abbrev ray13392 := rays 15
def bank13392 : Fin 1 → Cell := oneBank p13392 ray13392
theorem signs13392 : ∀ j, Signs p13392 (bank13392 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13393 := params 16
abbrev ray13393 := rays 16
def bank13393 : Fin 1 → Cell := oneBank p13393 ray13393
theorem signs13393 : ∀ j, Signs p13393 (bank13393 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13394 := params 17
abbrev ray13394 := rays 17
def bank13394 : Fin 1 → Cell := oneBank p13394 ray13394
theorem signs13394 : ∀ j, Signs p13394 (bank13394 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13395 := params 18
abbrev ray13395 := rays 18
def bank13395 : Fin 1 → Cell := oneBank p13395 ray13395
theorem signs13395 : ∀ j, Signs p13395 (bank13395 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13396 := params 19
abbrev ray13396 := rays 19
def bank13396 : Fin 1 → Cell := oneBank p13396 ray13396
theorem signs13396 : ∀ j, Signs p13396 (bank13396 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13397 := params 20
abbrev ray13397 := rays 20
def bank13397 : Fin 1 → Cell := oneBank p13397 ray13397
theorem signs13397 : ∀ j, Signs p13397 (bank13397 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13398 := params 21
abbrev ray13398 := rays 21
def bank13398 : Fin 1 → Cell := oneBank p13398 ray13398
theorem signs13398 : ∀ j, Signs p13398 (bank13398 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13399 := params 22
abbrev ray13399 := rays 22
def bank13399 : Fin 1 → Cell := oneBank p13399 ray13399
theorem signs13399 : ∀ j, Signs p13399 (bank13399 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13400 := params 23
abbrev ray13400 := rays 23
def bank13400 : Fin 1 → Cell := oneBank p13400 ray13400
theorem signs13400 : ∀ j, Signs p13400 (bank13400 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13401 := params 24
abbrev ray13401 := rays 24
def bank13401 : Fin 1 → Cell := oneBank p13401 ray13401
theorem signs13401 : ∀ j, Signs p13401 (bank13401 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13402 := params 25
abbrev ray13402 := rays 25
def bank13402 : Fin 1 → Cell := oneBank p13402 ray13402
theorem signs13402 : ∀ j, Signs p13402 (bank13402 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13403 := params 26
abbrev ray13403 := rays 26
def bank13403 : Fin 1 → Cell := oneBank p13403 ray13403
theorem signs13403 : ∀ j, Signs p13403 (bank13403 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13404 := params 27
abbrev ray13404 := rays 27
def bank13404 : Fin 1 → Cell := oneBank p13404 ray13404
theorem signs13404 : ∀ j, Signs p13404 (bank13404 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13405 := params 28
abbrev ray13405 := rays 28
def bank13405 : Fin 1 → Cell := oneBank p13405 ray13405
theorem signs13405 : ∀ j, Signs p13405 (bank13405 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13406 := params 29
abbrev ray13406 := rays 29
def bank13406 : Fin 1 → Cell := oneBank p13406 ray13406
theorem signs13406 : ∀ j, Signs p13406 (bank13406 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13407 := params 30
abbrev ray13407 := rays 30
def bank13407 : Fin 1 → Cell := oneBank p13407 ray13407
theorem signs13407 : ∀ j, Signs p13407 (bank13407 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13408 := params 31
abbrev ray13408 := rays 31
def bank13408 : Fin 1 → Cell := oneBank p13408 ray13408
theorem signs13408 : ∀ j, Signs p13408 (bank13408 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13377_13408
