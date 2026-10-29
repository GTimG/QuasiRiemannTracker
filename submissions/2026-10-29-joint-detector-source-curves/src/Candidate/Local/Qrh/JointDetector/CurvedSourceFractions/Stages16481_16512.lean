/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16481_16512
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94703905234540,94703424184792,94702943119060,94702462037345,94701980939647,94701499825965,94701018696300,94700537550651,94700056389019,94699575211404,94699094017805,94698612808223,94698131582658,94697650341109,94697169083577,94696687810061,94696206520562,94695725215080,94695243893614,94694762556165,94694281202732,94693799833316,94693318447917,94692837046534,94692355629168,94691874195818,94691392746485,94690911281169,94690429799869,94689948302586,94689466789319,94688985260069,94688503714836]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16480+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16481 := params 0
abbrev ray16481 := rays 0
def bank16481 : Fin 1 → Cell := oneBank p16481 ray16481
theorem signs16481 : ∀ j, Signs p16481 (bank16481 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16482 := params 1
abbrev ray16482 := rays 1
def bank16482 : Fin 1 → Cell := oneBank p16482 ray16482
theorem signs16482 : ∀ j, Signs p16482 (bank16482 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16483 := params 2
abbrev ray16483 := rays 2
def bank16483 : Fin 1 → Cell := oneBank p16483 ray16483
theorem signs16483 : ∀ j, Signs p16483 (bank16483 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16484 := params 3
abbrev ray16484 := rays 3
def bank16484 : Fin 1 → Cell := oneBank p16484 ray16484
theorem signs16484 : ∀ j, Signs p16484 (bank16484 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16485 := params 4
abbrev ray16485 := rays 4
def bank16485 : Fin 1 → Cell := oneBank p16485 ray16485
theorem signs16485 : ∀ j, Signs p16485 (bank16485 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16486 := params 5
abbrev ray16486 := rays 5
def bank16486 : Fin 1 → Cell := oneBank p16486 ray16486
theorem signs16486 : ∀ j, Signs p16486 (bank16486 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16487 := params 6
abbrev ray16487 := rays 6
def bank16487 : Fin 1 → Cell := oneBank p16487 ray16487
theorem signs16487 : ∀ j, Signs p16487 (bank16487 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16488 := params 7
abbrev ray16488 := rays 7
def bank16488 : Fin 1 → Cell := oneBank p16488 ray16488
theorem signs16488 : ∀ j, Signs p16488 (bank16488 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16489 := params 8
abbrev ray16489 := rays 8
def bank16489 : Fin 1 → Cell := oneBank p16489 ray16489
theorem signs16489 : ∀ j, Signs p16489 (bank16489 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16490 := params 9
abbrev ray16490 := rays 9
def bank16490 : Fin 1 → Cell := oneBank p16490 ray16490
theorem signs16490 : ∀ j, Signs p16490 (bank16490 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16491 := params 10
abbrev ray16491 := rays 10
def bank16491 : Fin 1 → Cell := oneBank p16491 ray16491
theorem signs16491 : ∀ j, Signs p16491 (bank16491 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16492 := params 11
abbrev ray16492 := rays 11
def bank16492 : Fin 1 → Cell := oneBank p16492 ray16492
theorem signs16492 : ∀ j, Signs p16492 (bank16492 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16493 := params 12
abbrev ray16493 := rays 12
def bank16493 : Fin 1 → Cell := oneBank p16493 ray16493
theorem signs16493 : ∀ j, Signs p16493 (bank16493 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16494 := params 13
abbrev ray16494 := rays 13
def bank16494 : Fin 1 → Cell := oneBank p16494 ray16494
theorem signs16494 : ∀ j, Signs p16494 (bank16494 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16495 := params 14
abbrev ray16495 := rays 14
def bank16495 : Fin 1 → Cell := oneBank p16495 ray16495
theorem signs16495 : ∀ j, Signs p16495 (bank16495 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16496 := params 15
abbrev ray16496 := rays 15
def bank16496 : Fin 1 → Cell := oneBank p16496 ray16496
theorem signs16496 : ∀ j, Signs p16496 (bank16496 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16497 := params 16
abbrev ray16497 := rays 16
def bank16497 : Fin 1 → Cell := oneBank p16497 ray16497
theorem signs16497 : ∀ j, Signs p16497 (bank16497 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16498 := params 17
abbrev ray16498 := rays 17
def bank16498 : Fin 1 → Cell := oneBank p16498 ray16498
theorem signs16498 : ∀ j, Signs p16498 (bank16498 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16499 := params 18
abbrev ray16499 := rays 18
def bank16499 : Fin 1 → Cell := oneBank p16499 ray16499
theorem signs16499 : ∀ j, Signs p16499 (bank16499 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16500 := params 19
abbrev ray16500 := rays 19
def bank16500 : Fin 1 → Cell := oneBank p16500 ray16500
theorem signs16500 : ∀ j, Signs p16500 (bank16500 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16501 := params 20
abbrev ray16501 := rays 20
def bank16501 : Fin 1 → Cell := oneBank p16501 ray16501
theorem signs16501 : ∀ j, Signs p16501 (bank16501 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16502 := params 21
abbrev ray16502 := rays 21
def bank16502 : Fin 1 → Cell := oneBank p16502 ray16502
theorem signs16502 : ∀ j, Signs p16502 (bank16502 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16503 := params 22
abbrev ray16503 := rays 22
def bank16503 : Fin 1 → Cell := oneBank p16503 ray16503
theorem signs16503 : ∀ j, Signs p16503 (bank16503 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16504 := params 23
abbrev ray16504 := rays 23
def bank16504 : Fin 1 → Cell := oneBank p16504 ray16504
theorem signs16504 : ∀ j, Signs p16504 (bank16504 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16505 := params 24
abbrev ray16505 := rays 24
def bank16505 : Fin 1 → Cell := oneBank p16505 ray16505
theorem signs16505 : ∀ j, Signs p16505 (bank16505 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16506 := params 25
abbrev ray16506 := rays 25
def bank16506 : Fin 1 → Cell := oneBank p16506 ray16506
theorem signs16506 : ∀ j, Signs p16506 (bank16506 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16507 := params 26
abbrev ray16507 := rays 26
def bank16507 : Fin 1 → Cell := oneBank p16507 ray16507
theorem signs16507 : ∀ j, Signs p16507 (bank16507 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16508 := params 27
abbrev ray16508 := rays 27
def bank16508 : Fin 1 → Cell := oneBank p16508 ray16508
theorem signs16508 : ∀ j, Signs p16508 (bank16508 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16509 := params 28
abbrev ray16509 := rays 28
def bank16509 : Fin 1 → Cell := oneBank p16509 ray16509
theorem signs16509 : ∀ j, Signs p16509 (bank16509 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16510 := params 29
abbrev ray16510 := rays 29
def bank16510 : Fin 1 → Cell := oneBank p16510 ray16510
theorem signs16510 : ∀ j, Signs p16510 (bank16510 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16511 := params 30
abbrev ray16511 := rays 30
def bank16511 : Fin 1 → Cell := oneBank p16511 ray16511
theorem signs16511 : ∀ j, Signs p16511 (bank16511 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16512 := params 31
abbrev ray16512 := rays 31
def bank16512 : Fin 1 → Cell := oneBank p16512 ray16512
theorem signs16512 : ∀ j, Signs p16512 (bank16512 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16481_16512
