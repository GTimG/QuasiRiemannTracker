/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03489_03520
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99394794381534,99394575585899,99394356764508,99394137917362,99393919044463,99393700145811,99393481221408,99393262271255,99393043295353,99392824293703,99392605266307,99392386213165,99392167134279,99391948029650,99391728899280,99391509743169,99391290561319,99391071353731,99390852120406,99390632861345,99390413576550,99390194266021,99389974929760,99389755567768,99389536180046,99389316766596,99389097327419,99388877862515,99388658371886,99388438855534,99388219313459,99387999745663,99387780152147]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3488+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3489 := params 0
abbrev ray3489 := rays 0
def bank3489 : Fin 2 → Cell := twoBank p3489 ray3489
theorem signs3489 : ∀ j, Signs p3489 (bank3489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3490 := params 1
abbrev ray3490 := rays 1
def bank3490 : Fin 2 → Cell := twoBank p3490 ray3490
theorem signs3490 : ∀ j, Signs p3490 (bank3490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3491 := params 2
abbrev ray3491 := rays 2
def bank3491 : Fin 2 → Cell := twoBank p3491 ray3491
theorem signs3491 : ∀ j, Signs p3491 (bank3491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3492 := params 3
abbrev ray3492 := rays 3
def bank3492 : Fin 2 → Cell := twoBank p3492 ray3492
theorem signs3492 : ∀ j, Signs p3492 (bank3492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3493 := params 4
abbrev ray3493 := rays 4
def bank3493 : Fin 2 → Cell := twoBank p3493 ray3493
theorem signs3493 : ∀ j, Signs p3493 (bank3493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3494 := params 5
abbrev ray3494 := rays 5
def bank3494 : Fin 2 → Cell := twoBank p3494 ray3494
theorem signs3494 : ∀ j, Signs p3494 (bank3494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3495 := params 6
abbrev ray3495 := rays 6
def bank3495 : Fin 2 → Cell := twoBank p3495 ray3495
theorem signs3495 : ∀ j, Signs p3495 (bank3495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3496 := params 7
abbrev ray3496 := rays 7
def bank3496 : Fin 2 → Cell := twoBank p3496 ray3496
theorem signs3496 : ∀ j, Signs p3496 (bank3496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3497 := params 8
abbrev ray3497 := rays 8
def bank3497 : Fin 2 → Cell := twoBank p3497 ray3497
theorem signs3497 : ∀ j, Signs p3497 (bank3497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3498 := params 9
abbrev ray3498 := rays 9
def bank3498 : Fin 2 → Cell := twoBank p3498 ray3498
theorem signs3498 : ∀ j, Signs p3498 (bank3498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3499 := params 10
abbrev ray3499 := rays 10
def bank3499 : Fin 2 → Cell := twoBank p3499 ray3499
theorem signs3499 : ∀ j, Signs p3499 (bank3499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3500 := params 11
abbrev ray3500 := rays 11
def bank3500 : Fin 2 → Cell := twoBank p3500 ray3500
theorem signs3500 : ∀ j, Signs p3500 (bank3500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3501 := params 12
abbrev ray3501 := rays 12
def bank3501 : Fin 2 → Cell := twoBank p3501 ray3501
theorem signs3501 : ∀ j, Signs p3501 (bank3501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3502 := params 13
abbrev ray3502 := rays 13
def bank3502 : Fin 2 → Cell := twoBank p3502 ray3502
theorem signs3502 : ∀ j, Signs p3502 (bank3502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3503 := params 14
abbrev ray3503 := rays 14
def bank3503 : Fin 2 → Cell := twoBank p3503 ray3503
theorem signs3503 : ∀ j, Signs p3503 (bank3503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3504 := params 15
abbrev ray3504 := rays 15
def bank3504 : Fin 2 → Cell := twoBank p3504 ray3504
theorem signs3504 : ∀ j, Signs p3504 (bank3504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3505 := params 16
abbrev ray3505 := rays 16
def bank3505 : Fin 2 → Cell := twoBank p3505 ray3505
theorem signs3505 : ∀ j, Signs p3505 (bank3505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3506 := params 17
abbrev ray3506 := rays 17
def bank3506 : Fin 2 → Cell := twoBank p3506 ray3506
theorem signs3506 : ∀ j, Signs p3506 (bank3506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3507 := params 18
abbrev ray3507 := rays 18
def bank3507 : Fin 2 → Cell := twoBank p3507 ray3507
theorem signs3507 : ∀ j, Signs p3507 (bank3507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3508 := params 19
abbrev ray3508 := rays 19
def bank3508 : Fin 2 → Cell := twoBank p3508 ray3508
theorem signs3508 : ∀ j, Signs p3508 (bank3508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3509 := params 20
abbrev ray3509 := rays 20
def bank3509 : Fin 2 → Cell := twoBank p3509 ray3509
theorem signs3509 : ∀ j, Signs p3509 (bank3509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3510 := params 21
abbrev ray3510 := rays 21
def bank3510 : Fin 2 → Cell := twoBank p3510 ray3510
theorem signs3510 : ∀ j, Signs p3510 (bank3510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3511 := params 22
abbrev ray3511 := rays 22
def bank3511 : Fin 2 → Cell := twoBank p3511 ray3511
theorem signs3511 : ∀ j, Signs p3511 (bank3511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3512 := params 23
abbrev ray3512 := rays 23
def bank3512 : Fin 2 → Cell := twoBank p3512 ray3512
theorem signs3512 : ∀ j, Signs p3512 (bank3512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3513 := params 24
abbrev ray3513 := rays 24
def bank3513 : Fin 2 → Cell := twoBank p3513 ray3513
theorem signs3513 : ∀ j, Signs p3513 (bank3513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3514 := params 25
abbrev ray3514 := rays 25
def bank3514 : Fin 2 → Cell := twoBank p3514 ray3514
theorem signs3514 : ∀ j, Signs p3514 (bank3514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3515 := params 26
abbrev ray3515 := rays 26
def bank3515 : Fin 2 → Cell := twoBank p3515 ray3515
theorem signs3515 : ∀ j, Signs p3515 (bank3515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3516 := params 27
abbrev ray3516 := rays 27
def bank3516 : Fin 2 → Cell := twoBank p3516 ray3516
theorem signs3516 : ∀ j, Signs p3516 (bank3516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3517 := params 28
abbrev ray3517 := rays 28
def bank3517 : Fin 2 → Cell := twoBank p3517 ray3517
theorem signs3517 : ∀ j, Signs p3517 (bank3517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3518 := params 29
abbrev ray3518 := rays 29
def bank3518 : Fin 2 → Cell := twoBank p3518 ray3518
theorem signs3518 : ∀ j, Signs p3518 (bank3518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3519 := params 30
abbrev ray3519 := rays 30
def bank3519 : Fin 2 → Cell := twoBank p3519 ray3519
theorem signs3519 : ∀ j, Signs p3519 (bank3519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3520 := params 31
abbrev ray3520 := rays 31
def bank3520 : Fin 2 → Cell := twoBank p3520 ray3520
theorem signs3520 : ∀ j, Signs p3520 (bank3520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03489_03520
