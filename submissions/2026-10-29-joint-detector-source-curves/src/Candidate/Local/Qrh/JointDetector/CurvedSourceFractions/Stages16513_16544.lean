/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16513_16544
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94688503714836,94688022153619,94687540576419,94687058983235,94686577374068,94686095748917,94685614107783,94685132450666,94684650777565,94684169088481,94683687383413,94683205662362,94682723925327,94682242172309,94681760403307,94681278618322,94680796817353,94680315000401,94679833167466,94679351318547,94678869453645,94678387572759,94677905675890,94677423763037,94676941834201,94676459889381,94675977928578,94675495951791,94675013959021,94674531950267,94674049925530,94673567884809,94673085828104]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16512+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16513 := params 0
abbrev ray16513 := rays 0
def bank16513 : Fin 1 → Cell := oneBank p16513 ray16513
theorem signs16513 : ∀ j, Signs p16513 (bank16513 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16514 := params 1
abbrev ray16514 := rays 1
def bank16514 : Fin 1 → Cell := oneBank p16514 ray16514
theorem signs16514 : ∀ j, Signs p16514 (bank16514 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16515 := params 2
abbrev ray16515 := rays 2
def bank16515 : Fin 1 → Cell := oneBank p16515 ray16515
theorem signs16515 : ∀ j, Signs p16515 (bank16515 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16516 := params 3
abbrev ray16516 := rays 3
def bank16516 : Fin 1 → Cell := oneBank p16516 ray16516
theorem signs16516 : ∀ j, Signs p16516 (bank16516 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16517 := params 4
abbrev ray16517 := rays 4
def bank16517 : Fin 1 → Cell := oneBank p16517 ray16517
theorem signs16517 : ∀ j, Signs p16517 (bank16517 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16518 := params 5
abbrev ray16518 := rays 5
def bank16518 : Fin 1 → Cell := oneBank p16518 ray16518
theorem signs16518 : ∀ j, Signs p16518 (bank16518 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16519 := params 6
abbrev ray16519 := rays 6
def bank16519 : Fin 1 → Cell := oneBank p16519 ray16519
theorem signs16519 : ∀ j, Signs p16519 (bank16519 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16520 := params 7
abbrev ray16520 := rays 7
def bank16520 : Fin 1 → Cell := oneBank p16520 ray16520
theorem signs16520 : ∀ j, Signs p16520 (bank16520 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16521 := params 8
abbrev ray16521 := rays 8
def bank16521 : Fin 1 → Cell := oneBank p16521 ray16521
theorem signs16521 : ∀ j, Signs p16521 (bank16521 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16522 := params 9
abbrev ray16522 := rays 9
def bank16522 : Fin 1 → Cell := oneBank p16522 ray16522
theorem signs16522 : ∀ j, Signs p16522 (bank16522 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16523 := params 10
abbrev ray16523 := rays 10
def bank16523 : Fin 1 → Cell := oneBank p16523 ray16523
theorem signs16523 : ∀ j, Signs p16523 (bank16523 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16524 := params 11
abbrev ray16524 := rays 11
def bank16524 : Fin 1 → Cell := oneBank p16524 ray16524
theorem signs16524 : ∀ j, Signs p16524 (bank16524 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16525 := params 12
abbrev ray16525 := rays 12
def bank16525 : Fin 1 → Cell := oneBank p16525 ray16525
theorem signs16525 : ∀ j, Signs p16525 (bank16525 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16526 := params 13
abbrev ray16526 := rays 13
def bank16526 : Fin 1 → Cell := oneBank p16526 ray16526
theorem signs16526 : ∀ j, Signs p16526 (bank16526 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16527 := params 14
abbrev ray16527 := rays 14
def bank16527 : Fin 1 → Cell := oneBank p16527 ray16527
theorem signs16527 : ∀ j, Signs p16527 (bank16527 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16528 := params 15
abbrev ray16528 := rays 15
def bank16528 : Fin 1 → Cell := oneBank p16528 ray16528
theorem signs16528 : ∀ j, Signs p16528 (bank16528 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16529 := params 16
abbrev ray16529 := rays 16
def bank16529 : Fin 1 → Cell := oneBank p16529 ray16529
theorem signs16529 : ∀ j, Signs p16529 (bank16529 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16530 := params 17
abbrev ray16530 := rays 17
def bank16530 : Fin 1 → Cell := oneBank p16530 ray16530
theorem signs16530 : ∀ j, Signs p16530 (bank16530 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16531 := params 18
abbrev ray16531 := rays 18
def bank16531 : Fin 1 → Cell := oneBank p16531 ray16531
theorem signs16531 : ∀ j, Signs p16531 (bank16531 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16532 := params 19
abbrev ray16532 := rays 19
def bank16532 : Fin 1 → Cell := oneBank p16532 ray16532
theorem signs16532 : ∀ j, Signs p16532 (bank16532 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16533 := params 20
abbrev ray16533 := rays 20
def bank16533 : Fin 1 → Cell := oneBank p16533 ray16533
theorem signs16533 : ∀ j, Signs p16533 (bank16533 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16534 := params 21
abbrev ray16534 := rays 21
def bank16534 : Fin 1 → Cell := oneBank p16534 ray16534
theorem signs16534 : ∀ j, Signs p16534 (bank16534 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16535 := params 22
abbrev ray16535 := rays 22
def bank16535 : Fin 1 → Cell := oneBank p16535 ray16535
theorem signs16535 : ∀ j, Signs p16535 (bank16535 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16536 := params 23
abbrev ray16536 := rays 23
def bank16536 : Fin 1 → Cell := oneBank p16536 ray16536
theorem signs16536 : ∀ j, Signs p16536 (bank16536 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16537 := params 24
abbrev ray16537 := rays 24
def bank16537 : Fin 1 → Cell := oneBank p16537 ray16537
theorem signs16537 : ∀ j, Signs p16537 (bank16537 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16538 := params 25
abbrev ray16538 := rays 25
def bank16538 : Fin 1 → Cell := oneBank p16538 ray16538
theorem signs16538 : ∀ j, Signs p16538 (bank16538 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16539 := params 26
abbrev ray16539 := rays 26
def bank16539 : Fin 1 → Cell := oneBank p16539 ray16539
theorem signs16539 : ∀ j, Signs p16539 (bank16539 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16540 := params 27
abbrev ray16540 := rays 27
def bank16540 : Fin 1 → Cell := oneBank p16540 ray16540
theorem signs16540 : ∀ j, Signs p16540 (bank16540 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16541 := params 28
abbrev ray16541 := rays 28
def bank16541 : Fin 1 → Cell := oneBank p16541 ray16541
theorem signs16541 : ∀ j, Signs p16541 (bank16541 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16542 := params 29
abbrev ray16542 := rays 29
def bank16542 : Fin 1 → Cell := oneBank p16542 ray16542
theorem signs16542 : ∀ j, Signs p16542 (bank16542 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16543 := params 30
abbrev ray16543 := rays 30
def bank16543 : Fin 1 → Cell := oneBank p16543 ray16543
theorem signs16543 : ∀ j, Signs p16543 (bank16543 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16544 := params 31
abbrev ray16544 := rays 31
def bank16544 : Fin 1 → Cell := oneBank p16544 ray16544
theorem signs16544 : ∀ j, Signs p16544 (bank16544 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16513_16544
