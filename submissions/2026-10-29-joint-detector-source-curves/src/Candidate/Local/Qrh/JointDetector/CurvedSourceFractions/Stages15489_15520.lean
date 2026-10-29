/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15489_15520
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95173231248114,95172766066219,95172300868304,95171835654368,95171370424412,95170905178436,95170439916439,95169974638422,95169509344385,95169044034328,95168578708251,95168113366154,95167648008038,95167182633902,95166717243746,95166251837571,95165786415376,95165320977162,95164855522928,95164390052675,95163924566403,95163459064112,95162993545802,95162528011473,95162062461125,95161596894758,95161131312372,95160665713967,95160200099544,95159734469102,95159268822642,95158803160163,95158337481666]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15488+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15489 := params 0
abbrev ray15489 := rays 0
def bank15489 : Fin 1 → Cell := oneBank p15489 ray15489
theorem signs15489 : ∀ j, Signs p15489 (bank15489 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15490 := params 1
abbrev ray15490 := rays 1
def bank15490 : Fin 1 → Cell := oneBank p15490 ray15490
theorem signs15490 : ∀ j, Signs p15490 (bank15490 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15491 := params 2
abbrev ray15491 := rays 2
def bank15491 : Fin 1 → Cell := oneBank p15491 ray15491
theorem signs15491 : ∀ j, Signs p15491 (bank15491 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15492 := params 3
abbrev ray15492 := rays 3
def bank15492 : Fin 1 → Cell := oneBank p15492 ray15492
theorem signs15492 : ∀ j, Signs p15492 (bank15492 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15493 := params 4
abbrev ray15493 := rays 4
def bank15493 : Fin 1 → Cell := oneBank p15493 ray15493
theorem signs15493 : ∀ j, Signs p15493 (bank15493 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15494 := params 5
abbrev ray15494 := rays 5
def bank15494 : Fin 1 → Cell := oneBank p15494 ray15494
theorem signs15494 : ∀ j, Signs p15494 (bank15494 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15495 := params 6
abbrev ray15495 := rays 6
def bank15495 : Fin 1 → Cell := oneBank p15495 ray15495
theorem signs15495 : ∀ j, Signs p15495 (bank15495 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15496 := params 7
abbrev ray15496 := rays 7
def bank15496 : Fin 1 → Cell := oneBank p15496 ray15496
theorem signs15496 : ∀ j, Signs p15496 (bank15496 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15497 := params 8
abbrev ray15497 := rays 8
def bank15497 : Fin 1 → Cell := oneBank p15497 ray15497
theorem signs15497 : ∀ j, Signs p15497 (bank15497 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15498 := params 9
abbrev ray15498 := rays 9
def bank15498 : Fin 1 → Cell := oneBank p15498 ray15498
theorem signs15498 : ∀ j, Signs p15498 (bank15498 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15499 := params 10
abbrev ray15499 := rays 10
def bank15499 : Fin 1 → Cell := oneBank p15499 ray15499
theorem signs15499 : ∀ j, Signs p15499 (bank15499 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15500 := params 11
abbrev ray15500 := rays 11
def bank15500 : Fin 1 → Cell := oneBank p15500 ray15500
theorem signs15500 : ∀ j, Signs p15500 (bank15500 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15501 := params 12
abbrev ray15501 := rays 12
def bank15501 : Fin 1 → Cell := oneBank p15501 ray15501
theorem signs15501 : ∀ j, Signs p15501 (bank15501 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15502 := params 13
abbrev ray15502 := rays 13
def bank15502 : Fin 1 → Cell := oneBank p15502 ray15502
theorem signs15502 : ∀ j, Signs p15502 (bank15502 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15503 := params 14
abbrev ray15503 := rays 14
def bank15503 : Fin 1 → Cell := oneBank p15503 ray15503
theorem signs15503 : ∀ j, Signs p15503 (bank15503 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15504 := params 15
abbrev ray15504 := rays 15
def bank15504 : Fin 1 → Cell := oneBank p15504 ray15504
theorem signs15504 : ∀ j, Signs p15504 (bank15504 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15505 := params 16
abbrev ray15505 := rays 16
def bank15505 : Fin 1 → Cell := oneBank p15505 ray15505
theorem signs15505 : ∀ j, Signs p15505 (bank15505 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15506 := params 17
abbrev ray15506 := rays 17
def bank15506 : Fin 1 → Cell := oneBank p15506 ray15506
theorem signs15506 : ∀ j, Signs p15506 (bank15506 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15507 := params 18
abbrev ray15507 := rays 18
def bank15507 : Fin 1 → Cell := oneBank p15507 ray15507
theorem signs15507 : ∀ j, Signs p15507 (bank15507 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15508 := params 19
abbrev ray15508 := rays 19
def bank15508 : Fin 1 → Cell := oneBank p15508 ray15508
theorem signs15508 : ∀ j, Signs p15508 (bank15508 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15509 := params 20
abbrev ray15509 := rays 20
def bank15509 : Fin 1 → Cell := oneBank p15509 ray15509
theorem signs15509 : ∀ j, Signs p15509 (bank15509 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15510 := params 21
abbrev ray15510 := rays 21
def bank15510 : Fin 1 → Cell := oneBank p15510 ray15510
theorem signs15510 : ∀ j, Signs p15510 (bank15510 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15511 := params 22
abbrev ray15511 := rays 22
def bank15511 : Fin 1 → Cell := oneBank p15511 ray15511
theorem signs15511 : ∀ j, Signs p15511 (bank15511 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15512 := params 23
abbrev ray15512 := rays 23
def bank15512 : Fin 1 → Cell := oneBank p15512 ray15512
theorem signs15512 : ∀ j, Signs p15512 (bank15512 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15513 := params 24
abbrev ray15513 := rays 24
def bank15513 : Fin 1 → Cell := oneBank p15513 ray15513
theorem signs15513 : ∀ j, Signs p15513 (bank15513 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15514 := params 25
abbrev ray15514 := rays 25
def bank15514 : Fin 1 → Cell := oneBank p15514 ray15514
theorem signs15514 : ∀ j, Signs p15514 (bank15514 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15515 := params 26
abbrev ray15515 := rays 26
def bank15515 : Fin 1 → Cell := oneBank p15515 ray15515
theorem signs15515 : ∀ j, Signs p15515 (bank15515 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15516 := params 27
abbrev ray15516 := rays 27
def bank15516 : Fin 1 → Cell := oneBank p15516 ray15516
theorem signs15516 : ∀ j, Signs p15516 (bank15516 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15517 := params 28
abbrev ray15517 := rays 28
def bank15517 : Fin 1 → Cell := oneBank p15517 ray15517
theorem signs15517 : ∀ j, Signs p15517 (bank15517 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15518 := params 29
abbrev ray15518 := rays 29
def bank15518 : Fin 1 → Cell := oneBank p15518 ray15518
theorem signs15518 : ∀ j, Signs p15518 (bank15518 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15519 := params 30
abbrev ray15519 := rays 30
def bank15519 : Fin 1 → Cell := oneBank p15519 ray15519
theorem signs15519 : ∀ j, Signs p15519 (bank15519 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15520 := params 31
abbrev ray15520 := rays 31
def bank15520 : Fin 1 → Cell := oneBank p15520 ray15520
theorem signs15520 : ∀ j, Signs p15520 (bank15520 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15489_15520
