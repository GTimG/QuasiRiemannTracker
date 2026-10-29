/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15361_15392
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95232642237487,95232179106864,95231715960210,95231252797525,95230789618810,95230326424065,95229863213289,95229399986483,95228936743647,95228473484781,95228010209885,95227546918959,95227083612003,95226620289017,95226156950001,95225693594956,95225230223881,95224766836777,95224303433643,95223840014480,95223376579288,95222913128067,95222449660817,95221986177538,95221522678230,95221059162893,95220595631527,95220132084133,95219668520710,95219204941259,95218741345779,95218277734271,95217814106735]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15360+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15361 := params 0
abbrev ray15361 := rays 0
def bank15361 : Fin 1 → Cell := oneBank p15361 ray15361
theorem signs15361 : ∀ j, Signs p15361 (bank15361 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15362 := params 1
abbrev ray15362 := rays 1
def bank15362 : Fin 1 → Cell := oneBank p15362 ray15362
theorem signs15362 : ∀ j, Signs p15362 (bank15362 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15363 := params 2
abbrev ray15363 := rays 2
def bank15363 : Fin 1 → Cell := oneBank p15363 ray15363
theorem signs15363 : ∀ j, Signs p15363 (bank15363 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15364 := params 3
abbrev ray15364 := rays 3
def bank15364 : Fin 1 → Cell := oneBank p15364 ray15364
theorem signs15364 : ∀ j, Signs p15364 (bank15364 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15365 := params 4
abbrev ray15365 := rays 4
def bank15365 : Fin 1 → Cell := oneBank p15365 ray15365
theorem signs15365 : ∀ j, Signs p15365 (bank15365 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15366 := params 5
abbrev ray15366 := rays 5
def bank15366 : Fin 1 → Cell := oneBank p15366 ray15366
theorem signs15366 : ∀ j, Signs p15366 (bank15366 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15367 := params 6
abbrev ray15367 := rays 6
def bank15367 : Fin 1 → Cell := oneBank p15367 ray15367
theorem signs15367 : ∀ j, Signs p15367 (bank15367 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15368 := params 7
abbrev ray15368 := rays 7
def bank15368 : Fin 1 → Cell := oneBank p15368 ray15368
theorem signs15368 : ∀ j, Signs p15368 (bank15368 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15369 := params 8
abbrev ray15369 := rays 8
def bank15369 : Fin 1 → Cell := oneBank p15369 ray15369
theorem signs15369 : ∀ j, Signs p15369 (bank15369 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15370 := params 9
abbrev ray15370 := rays 9
def bank15370 : Fin 1 → Cell := oneBank p15370 ray15370
theorem signs15370 : ∀ j, Signs p15370 (bank15370 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15371 := params 10
abbrev ray15371 := rays 10
def bank15371 : Fin 1 → Cell := oneBank p15371 ray15371
theorem signs15371 : ∀ j, Signs p15371 (bank15371 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15372 := params 11
abbrev ray15372 := rays 11
def bank15372 : Fin 1 → Cell := oneBank p15372 ray15372
theorem signs15372 : ∀ j, Signs p15372 (bank15372 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15373 := params 12
abbrev ray15373 := rays 12
def bank15373 : Fin 1 → Cell := oneBank p15373 ray15373
theorem signs15373 : ∀ j, Signs p15373 (bank15373 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15374 := params 13
abbrev ray15374 := rays 13
def bank15374 : Fin 1 → Cell := oneBank p15374 ray15374
theorem signs15374 : ∀ j, Signs p15374 (bank15374 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15375 := params 14
abbrev ray15375 := rays 14
def bank15375 : Fin 1 → Cell := oneBank p15375 ray15375
theorem signs15375 : ∀ j, Signs p15375 (bank15375 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15376 := params 15
abbrev ray15376 := rays 15
def bank15376 : Fin 1 → Cell := oneBank p15376 ray15376
theorem signs15376 : ∀ j, Signs p15376 (bank15376 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15377 := params 16
abbrev ray15377 := rays 16
def bank15377 : Fin 1 → Cell := oneBank p15377 ray15377
theorem signs15377 : ∀ j, Signs p15377 (bank15377 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15378 := params 17
abbrev ray15378 := rays 17
def bank15378 : Fin 1 → Cell := oneBank p15378 ray15378
theorem signs15378 : ∀ j, Signs p15378 (bank15378 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15379 := params 18
abbrev ray15379 := rays 18
def bank15379 : Fin 1 → Cell := oneBank p15379 ray15379
theorem signs15379 : ∀ j, Signs p15379 (bank15379 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15380 := params 19
abbrev ray15380 := rays 19
def bank15380 : Fin 1 → Cell := oneBank p15380 ray15380
theorem signs15380 : ∀ j, Signs p15380 (bank15380 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15381 := params 20
abbrev ray15381 := rays 20
def bank15381 : Fin 1 → Cell := oneBank p15381 ray15381
theorem signs15381 : ∀ j, Signs p15381 (bank15381 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15382 := params 21
abbrev ray15382 := rays 21
def bank15382 : Fin 1 → Cell := oneBank p15382 ray15382
theorem signs15382 : ∀ j, Signs p15382 (bank15382 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15383 := params 22
abbrev ray15383 := rays 22
def bank15383 : Fin 1 → Cell := oneBank p15383 ray15383
theorem signs15383 : ∀ j, Signs p15383 (bank15383 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15384 := params 23
abbrev ray15384 := rays 23
def bank15384 : Fin 1 → Cell := oneBank p15384 ray15384
theorem signs15384 : ∀ j, Signs p15384 (bank15384 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15385 := params 24
abbrev ray15385 := rays 24
def bank15385 : Fin 1 → Cell := oneBank p15385 ray15385
theorem signs15385 : ∀ j, Signs p15385 (bank15385 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15386 := params 25
abbrev ray15386 := rays 25
def bank15386 : Fin 1 → Cell := oneBank p15386 ray15386
theorem signs15386 : ∀ j, Signs p15386 (bank15386 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15387 := params 26
abbrev ray15387 := rays 26
def bank15387 : Fin 1 → Cell := oneBank p15387 ray15387
theorem signs15387 : ∀ j, Signs p15387 (bank15387 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15388 := params 27
abbrev ray15388 := rays 27
def bank15388 : Fin 1 → Cell := oneBank p15388 ray15388
theorem signs15388 : ∀ j, Signs p15388 (bank15388 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15389 := params 28
abbrev ray15389 := rays 28
def bank15389 : Fin 1 → Cell := oneBank p15389 ray15389
theorem signs15389 : ∀ j, Signs p15389 (bank15389 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15390 := params 29
abbrev ray15390 := rays 29
def bank15390 : Fin 1 → Cell := oneBank p15390 ray15390
theorem signs15390 : ∀ j, Signs p15390 (bank15390 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15391 := params 30
abbrev ray15391 := rays 30
def bank15391 : Fin 1 → Cell := oneBank p15391 ray15391
theorem signs15391 : ∀ j, Signs p15391 (bank15391 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15392 := params 31
abbrev ray15392 := rays 31
def bank15392 : Fin 1 → Cell := oneBank p15392 ray15392
theorem signs15392 : ∀ j, Signs p15392 (bank15392 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15361_15392
