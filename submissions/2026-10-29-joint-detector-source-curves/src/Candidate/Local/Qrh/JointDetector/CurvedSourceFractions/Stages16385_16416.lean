/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16385_16416
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94750011591442,94749532076110,94749052544794,94748572997495,94748093434212,94747613854945,94747134259695,94746654648461,94746175021243,94745695378042,94745215718857,94744736043688,94744256352536,94743776645400,94743296922280,94742817183177,94742337428090,94741857657019,94741377869965,94740898066927,94740418247905,94739938412900,94739458561911,94738978694939,94738498811983,94738018913043,94737538998120,94737059067213,94736579120323,94736099157449,94735619178592,94735139183751,94734659172926]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16384+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16385 := params 0
abbrev ray16385 := rays 0
def bank16385 : Fin 1 → Cell := oneBank p16385 ray16385
theorem signs16385 : ∀ j, Signs p16385 (bank16385 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16386 := params 1
abbrev ray16386 := rays 1
def bank16386 : Fin 1 → Cell := oneBank p16386 ray16386
theorem signs16386 : ∀ j, Signs p16386 (bank16386 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16387 := params 2
abbrev ray16387 := rays 2
def bank16387 : Fin 1 → Cell := oneBank p16387 ray16387
theorem signs16387 : ∀ j, Signs p16387 (bank16387 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16388 := params 3
abbrev ray16388 := rays 3
def bank16388 : Fin 1 → Cell := oneBank p16388 ray16388
theorem signs16388 : ∀ j, Signs p16388 (bank16388 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16389 := params 4
abbrev ray16389 := rays 4
def bank16389 : Fin 1 → Cell := oneBank p16389 ray16389
theorem signs16389 : ∀ j, Signs p16389 (bank16389 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16390 := params 5
abbrev ray16390 := rays 5
def bank16390 : Fin 1 → Cell := oneBank p16390 ray16390
theorem signs16390 : ∀ j, Signs p16390 (bank16390 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16391 := params 6
abbrev ray16391 := rays 6
def bank16391 : Fin 1 → Cell := oneBank p16391 ray16391
theorem signs16391 : ∀ j, Signs p16391 (bank16391 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16392 := params 7
abbrev ray16392 := rays 7
def bank16392 : Fin 1 → Cell := oneBank p16392 ray16392
theorem signs16392 : ∀ j, Signs p16392 (bank16392 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16393 := params 8
abbrev ray16393 := rays 8
def bank16393 : Fin 1 → Cell := oneBank p16393 ray16393
theorem signs16393 : ∀ j, Signs p16393 (bank16393 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16394 := params 9
abbrev ray16394 := rays 9
def bank16394 : Fin 1 → Cell := oneBank p16394 ray16394
theorem signs16394 : ∀ j, Signs p16394 (bank16394 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16395 := params 10
abbrev ray16395 := rays 10
def bank16395 : Fin 1 → Cell := oneBank p16395 ray16395
theorem signs16395 : ∀ j, Signs p16395 (bank16395 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16396 := params 11
abbrev ray16396 := rays 11
def bank16396 : Fin 1 → Cell := oneBank p16396 ray16396
theorem signs16396 : ∀ j, Signs p16396 (bank16396 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16397 := params 12
abbrev ray16397 := rays 12
def bank16397 : Fin 1 → Cell := oneBank p16397 ray16397
theorem signs16397 : ∀ j, Signs p16397 (bank16397 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16398 := params 13
abbrev ray16398 := rays 13
def bank16398 : Fin 1 → Cell := oneBank p16398 ray16398
theorem signs16398 : ∀ j, Signs p16398 (bank16398 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16399 := params 14
abbrev ray16399 := rays 14
def bank16399 : Fin 1 → Cell := oneBank p16399 ray16399
theorem signs16399 : ∀ j, Signs p16399 (bank16399 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16400 := params 15
abbrev ray16400 := rays 15
def bank16400 : Fin 1 → Cell := oneBank p16400 ray16400
theorem signs16400 : ∀ j, Signs p16400 (bank16400 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16401 := params 16
abbrev ray16401 := rays 16
def bank16401 : Fin 1 → Cell := oneBank p16401 ray16401
theorem signs16401 : ∀ j, Signs p16401 (bank16401 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16402 := params 17
abbrev ray16402 := rays 17
def bank16402 : Fin 1 → Cell := oneBank p16402 ray16402
theorem signs16402 : ∀ j, Signs p16402 (bank16402 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16403 := params 18
abbrev ray16403 := rays 18
def bank16403 : Fin 1 → Cell := oneBank p16403 ray16403
theorem signs16403 : ∀ j, Signs p16403 (bank16403 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16404 := params 19
abbrev ray16404 := rays 19
def bank16404 : Fin 1 → Cell := oneBank p16404 ray16404
theorem signs16404 : ∀ j, Signs p16404 (bank16404 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16405 := params 20
abbrev ray16405 := rays 20
def bank16405 : Fin 1 → Cell := oneBank p16405 ray16405
theorem signs16405 : ∀ j, Signs p16405 (bank16405 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16406 := params 21
abbrev ray16406 := rays 21
def bank16406 : Fin 1 → Cell := oneBank p16406 ray16406
theorem signs16406 : ∀ j, Signs p16406 (bank16406 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16407 := params 22
abbrev ray16407 := rays 22
def bank16407 : Fin 1 → Cell := oneBank p16407 ray16407
theorem signs16407 : ∀ j, Signs p16407 (bank16407 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16408 := params 23
abbrev ray16408 := rays 23
def bank16408 : Fin 1 → Cell := oneBank p16408 ray16408
theorem signs16408 : ∀ j, Signs p16408 (bank16408 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16409 := params 24
abbrev ray16409 := rays 24
def bank16409 : Fin 1 → Cell := oneBank p16409 ray16409
theorem signs16409 : ∀ j, Signs p16409 (bank16409 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16410 := params 25
abbrev ray16410 := rays 25
def bank16410 : Fin 1 → Cell := oneBank p16410 ray16410
theorem signs16410 : ∀ j, Signs p16410 (bank16410 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16411 := params 26
abbrev ray16411 := rays 26
def bank16411 : Fin 1 → Cell := oneBank p16411 ray16411
theorem signs16411 : ∀ j, Signs p16411 (bank16411 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16412 := params 27
abbrev ray16412 := rays 27
def bank16412 : Fin 1 → Cell := oneBank p16412 ray16412
theorem signs16412 : ∀ j, Signs p16412 (bank16412 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16413 := params 28
abbrev ray16413 := rays 28
def bank16413 : Fin 1 → Cell := oneBank p16413 ray16413
theorem signs16413 : ∀ j, Signs p16413 (bank16413 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16414 := params 29
abbrev ray16414 := rays 29
def bank16414 : Fin 1 → Cell := oneBank p16414 ray16414
theorem signs16414 : ∀ j, Signs p16414 (bank16414 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16415 := params 30
abbrev ray16415 := rays 30
def bank16415 : Fin 1 → Cell := oneBank p16415 ray16415
theorem signs16415 : ∀ j, Signs p16415 (bank16415 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16416 := params 31
abbrev ray16416 := rays 31
def bank16416 : Fin 1 → Cell := oneBank p16416 ray16416
theorem signs16416 : ∀ j, Signs p16416 (bank16416 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16385_16416
