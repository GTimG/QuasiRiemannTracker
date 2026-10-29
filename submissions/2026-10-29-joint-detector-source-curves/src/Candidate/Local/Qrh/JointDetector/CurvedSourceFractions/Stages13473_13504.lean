/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13473_13504
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96078312807755,96077880176406,96077447528735,96077014864742,96076582184427,96076149487791,96075716774834,96075284045556,96074851299958,96074418538039,96073985759800,96073552965241,96073120154362,96072687327164,96072254483646,96071821623809,96071388747653,96070955855179,96070522946386,96070090021275,96069657079846,96069224122099,96068791148035,96068358157654,96067925150956,96067492127941,96067059088609,96066626032961,96066192960997,96065759872717,96065326768121,96064893647209,96064460509982]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13472+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13473 := params 0
abbrev ray13473 := rays 0
def bank13473 : Fin 1 → Cell := oneBank p13473 ray13473
theorem signs13473 : ∀ j, Signs p13473 (bank13473 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13474 := params 1
abbrev ray13474 := rays 1
def bank13474 : Fin 1 → Cell := oneBank p13474 ray13474
theorem signs13474 : ∀ j, Signs p13474 (bank13474 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13475 := params 2
abbrev ray13475 := rays 2
def bank13475 : Fin 1 → Cell := oneBank p13475 ray13475
theorem signs13475 : ∀ j, Signs p13475 (bank13475 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13476 := params 3
abbrev ray13476 := rays 3
def bank13476 : Fin 1 → Cell := oneBank p13476 ray13476
theorem signs13476 : ∀ j, Signs p13476 (bank13476 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13477 := params 4
abbrev ray13477 := rays 4
def bank13477 : Fin 1 → Cell := oneBank p13477 ray13477
theorem signs13477 : ∀ j, Signs p13477 (bank13477 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13478 := params 5
abbrev ray13478 := rays 5
def bank13478 : Fin 1 → Cell := oneBank p13478 ray13478
theorem signs13478 : ∀ j, Signs p13478 (bank13478 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13479 := params 6
abbrev ray13479 := rays 6
def bank13479 : Fin 1 → Cell := oneBank p13479 ray13479
theorem signs13479 : ∀ j, Signs p13479 (bank13479 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13480 := params 7
abbrev ray13480 := rays 7
def bank13480 : Fin 1 → Cell := oneBank p13480 ray13480
theorem signs13480 : ∀ j, Signs p13480 (bank13480 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13481 := params 8
abbrev ray13481 := rays 8
def bank13481 : Fin 1 → Cell := oneBank p13481 ray13481
theorem signs13481 : ∀ j, Signs p13481 (bank13481 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13482 := params 9
abbrev ray13482 := rays 9
def bank13482 : Fin 1 → Cell := oneBank p13482 ray13482
theorem signs13482 : ∀ j, Signs p13482 (bank13482 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13483 := params 10
abbrev ray13483 := rays 10
def bank13483 : Fin 1 → Cell := oneBank p13483 ray13483
theorem signs13483 : ∀ j, Signs p13483 (bank13483 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13484 := params 11
abbrev ray13484 := rays 11
def bank13484 : Fin 1 → Cell := oneBank p13484 ray13484
theorem signs13484 : ∀ j, Signs p13484 (bank13484 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13485 := params 12
abbrev ray13485 := rays 12
def bank13485 : Fin 1 → Cell := oneBank p13485 ray13485
theorem signs13485 : ∀ j, Signs p13485 (bank13485 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13486 := params 13
abbrev ray13486 := rays 13
def bank13486 : Fin 1 → Cell := oneBank p13486 ray13486
theorem signs13486 : ∀ j, Signs p13486 (bank13486 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13487 := params 14
abbrev ray13487 := rays 14
def bank13487 : Fin 1 → Cell := oneBank p13487 ray13487
theorem signs13487 : ∀ j, Signs p13487 (bank13487 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13488 := params 15
abbrev ray13488 := rays 15
def bank13488 : Fin 1 → Cell := oneBank p13488 ray13488
theorem signs13488 : ∀ j, Signs p13488 (bank13488 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13489 := params 16
abbrev ray13489 := rays 16
def bank13489 : Fin 1 → Cell := oneBank p13489 ray13489
theorem signs13489 : ∀ j, Signs p13489 (bank13489 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13490 := params 17
abbrev ray13490 := rays 17
def bank13490 : Fin 1 → Cell := oneBank p13490 ray13490
theorem signs13490 : ∀ j, Signs p13490 (bank13490 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13491 := params 18
abbrev ray13491 := rays 18
def bank13491 : Fin 1 → Cell := oneBank p13491 ray13491
theorem signs13491 : ∀ j, Signs p13491 (bank13491 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13492 := params 19
abbrev ray13492 := rays 19
def bank13492 : Fin 1 → Cell := oneBank p13492 ray13492
theorem signs13492 : ∀ j, Signs p13492 (bank13492 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13493 := params 20
abbrev ray13493 := rays 20
def bank13493 : Fin 1 → Cell := oneBank p13493 ray13493
theorem signs13493 : ∀ j, Signs p13493 (bank13493 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13494 := params 21
abbrev ray13494 := rays 21
def bank13494 : Fin 1 → Cell := oneBank p13494 ray13494
theorem signs13494 : ∀ j, Signs p13494 (bank13494 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13495 := params 22
abbrev ray13495 := rays 22
def bank13495 : Fin 1 → Cell := oneBank p13495 ray13495
theorem signs13495 : ∀ j, Signs p13495 (bank13495 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13496 := params 23
abbrev ray13496 := rays 23
def bank13496 : Fin 1 → Cell := oneBank p13496 ray13496
theorem signs13496 : ∀ j, Signs p13496 (bank13496 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13497 := params 24
abbrev ray13497 := rays 24
def bank13497 : Fin 1 → Cell := oneBank p13497 ray13497
theorem signs13497 : ∀ j, Signs p13497 (bank13497 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13498 := params 25
abbrev ray13498 := rays 25
def bank13498 : Fin 1 → Cell := oneBank p13498 ray13498
theorem signs13498 : ∀ j, Signs p13498 (bank13498 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13499 := params 26
abbrev ray13499 := rays 26
def bank13499 : Fin 1 → Cell := oneBank p13499 ray13499
theorem signs13499 : ∀ j, Signs p13499 (bank13499 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13500 := params 27
abbrev ray13500 := rays 27
def bank13500 : Fin 1 → Cell := oneBank p13500 ray13500
theorem signs13500 : ∀ j, Signs p13500 (bank13500 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13501 := params 28
abbrev ray13501 := rays 28
def bank13501 : Fin 1 → Cell := oneBank p13501 ray13501
theorem signs13501 : ∀ j, Signs p13501 (bank13501 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13502 := params 29
abbrev ray13502 := rays 29
def bank13502 : Fin 1 → Cell := oneBank p13502 ray13502
theorem signs13502 : ∀ j, Signs p13502 (bank13502 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13503 := params 30
abbrev ray13503 := rays 30
def bank13503 : Fin 1 → Cell := oneBank p13503 ray13503
theorem signs13503 : ∀ j, Signs p13503 (bank13503 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13504 := params 31
abbrev ray13504 := rays 31
def bank13504 : Fin 1 → Cell := oneBank p13504 ray13504
theorem signs13504 : ∀ j, Signs p13504 (bank13504 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13473_13504
