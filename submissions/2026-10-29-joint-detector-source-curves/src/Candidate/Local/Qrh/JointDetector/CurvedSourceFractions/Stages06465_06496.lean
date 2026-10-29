/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06465_06496
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98634454393404,98634163664497,98633872912826,98633582138393,98633291341198,98633000521242,98632709678526,98632418813051,98632127924818,98631837013827,98631546080080,98631255123577,98630964144319,98630673142307,98630382117542,98630091070024,98629799999755,98629508906735,98629217790965,98628926652446,98628635491178,98628344307163,98628053100401,98627761870894,98627470618642,98627179343646,98626888045906,98626596725424,98626305382200,98626014016236,98625722627532,98625431216089,98625139781907]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6464+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6465 := params 0
abbrev ray6465 := rays 0
def bank6465 : Fin 2 → Cell := twoBank p6465 ray6465
theorem signs6465 : ∀ j, Signs p6465 (bank6465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6466 := params 1
abbrev ray6466 := rays 1
def bank6466 : Fin 2 → Cell := twoBank p6466 ray6466
theorem signs6466 : ∀ j, Signs p6466 (bank6466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6467 := params 2
abbrev ray6467 := rays 2
def bank6467 : Fin 2 → Cell := twoBank p6467 ray6467
theorem signs6467 : ∀ j, Signs p6467 (bank6467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6468 := params 3
abbrev ray6468 := rays 3
def bank6468 : Fin 2 → Cell := twoBank p6468 ray6468
theorem signs6468 : ∀ j, Signs p6468 (bank6468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6469 := params 4
abbrev ray6469 := rays 4
def bank6469 : Fin 2 → Cell := twoBank p6469 ray6469
theorem signs6469 : ∀ j, Signs p6469 (bank6469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6470 := params 5
abbrev ray6470 := rays 5
def bank6470 : Fin 2 → Cell := twoBank p6470 ray6470
theorem signs6470 : ∀ j, Signs p6470 (bank6470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6471 := params 6
abbrev ray6471 := rays 6
def bank6471 : Fin 2 → Cell := twoBank p6471 ray6471
theorem signs6471 : ∀ j, Signs p6471 (bank6471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6472 := params 7
abbrev ray6472 := rays 7
def bank6472 : Fin 2 → Cell := twoBank p6472 ray6472
theorem signs6472 : ∀ j, Signs p6472 (bank6472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6473 := params 8
abbrev ray6473 := rays 8
def bank6473 : Fin 2 → Cell := twoBank p6473 ray6473
theorem signs6473 : ∀ j, Signs p6473 (bank6473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6474 := params 9
abbrev ray6474 := rays 9
def bank6474 : Fin 2 → Cell := twoBank p6474 ray6474
theorem signs6474 : ∀ j, Signs p6474 (bank6474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6475 := params 10
abbrev ray6475 := rays 10
def bank6475 : Fin 2 → Cell := twoBank p6475 ray6475
theorem signs6475 : ∀ j, Signs p6475 (bank6475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6476 := params 11
abbrev ray6476 := rays 11
def bank6476 : Fin 2 → Cell := twoBank p6476 ray6476
theorem signs6476 : ∀ j, Signs p6476 (bank6476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6477 := params 12
abbrev ray6477 := rays 12
def bank6477 : Fin 2 → Cell := twoBank p6477 ray6477
theorem signs6477 : ∀ j, Signs p6477 (bank6477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6478 := params 13
abbrev ray6478 := rays 13
def bank6478 : Fin 2 → Cell := twoBank p6478 ray6478
theorem signs6478 : ∀ j, Signs p6478 (bank6478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6479 := params 14
abbrev ray6479 := rays 14
def bank6479 : Fin 2 → Cell := twoBank p6479 ray6479
theorem signs6479 : ∀ j, Signs p6479 (bank6479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6480 := params 15
abbrev ray6480 := rays 15
def bank6480 : Fin 2 → Cell := twoBank p6480 ray6480
theorem signs6480 : ∀ j, Signs p6480 (bank6480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6481 := params 16
abbrev ray6481 := rays 16
def bank6481 : Fin 2 → Cell := twoBank p6481 ray6481
theorem signs6481 : ∀ j, Signs p6481 (bank6481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6482 := params 17
abbrev ray6482 := rays 17
def bank6482 : Fin 2 → Cell := twoBank p6482 ray6482
theorem signs6482 : ∀ j, Signs p6482 (bank6482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6483 := params 18
abbrev ray6483 := rays 18
def bank6483 : Fin 2 → Cell := twoBank p6483 ray6483
theorem signs6483 : ∀ j, Signs p6483 (bank6483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6484 := params 19
abbrev ray6484 := rays 19
def bank6484 : Fin 2 → Cell := twoBank p6484 ray6484
theorem signs6484 : ∀ j, Signs p6484 (bank6484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6485 := params 20
abbrev ray6485 := rays 20
def bank6485 : Fin 2 → Cell := twoBank p6485 ray6485
theorem signs6485 : ∀ j, Signs p6485 (bank6485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6486 := params 21
abbrev ray6486 := rays 21
def bank6486 : Fin 2 → Cell := twoBank p6486 ray6486
theorem signs6486 : ∀ j, Signs p6486 (bank6486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6487 := params 22
abbrev ray6487 := rays 22
def bank6487 : Fin 2 → Cell := twoBank p6487 ray6487
theorem signs6487 : ∀ j, Signs p6487 (bank6487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6488 := params 23
abbrev ray6488 := rays 23
def bank6488 : Fin 2 → Cell := twoBank p6488 ray6488
theorem signs6488 : ∀ j, Signs p6488 (bank6488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6489 := params 24
abbrev ray6489 := rays 24
def bank6489 : Fin 2 → Cell := twoBank p6489 ray6489
theorem signs6489 : ∀ j, Signs p6489 (bank6489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6490 := params 25
abbrev ray6490 := rays 25
def bank6490 : Fin 2 → Cell := twoBank p6490 ray6490
theorem signs6490 : ∀ j, Signs p6490 (bank6490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6491 := params 26
abbrev ray6491 := rays 26
def bank6491 : Fin 2 → Cell := twoBank p6491 ray6491
theorem signs6491 : ∀ j, Signs p6491 (bank6491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6492 := params 27
abbrev ray6492 := rays 27
def bank6492 : Fin 2 → Cell := twoBank p6492 ray6492
theorem signs6492 : ∀ j, Signs p6492 (bank6492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6493 := params 28
abbrev ray6493 := rays 28
def bank6493 : Fin 2 → Cell := twoBank p6493 ray6493
theorem signs6493 : ∀ j, Signs p6493 (bank6493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6494 := params 29
abbrev ray6494 := rays 29
def bank6494 : Fin 2 → Cell := twoBank p6494 ray6494
theorem signs6494 : ∀ j, Signs p6494 (bank6494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6495 := params 30
abbrev ray6495 := rays 30
def bank6495 : Fin 2 → Cell := twoBank p6495 ray6495
theorem signs6495 : ∀ j, Signs p6495 (bank6495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6496 := params 31
abbrev ray6496 := rays 31
def bank6496 : Fin 2 → Cell := twoBank p6496 ray6496
theorem signs6496 : ∀ j, Signs p6496 (bank6496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06465_06496
