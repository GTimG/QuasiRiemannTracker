/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04481_04512
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99165277659059,99165033879153,99164790074610,99164546245431,99164302391617,99164058513169,99163814610088,99163570682375,99163326730032,99163082753059,99162838751458,99162594725229,99162350674374,99162106598893,99161862498788,99161618374060,99161374224710,99161130050738,99160885852146,99160641628935,99160397381106,99160153108661,99159908811600,99159664489924,99159420143634,99159175772732,99158931377218,99158686957093,99158442512359,99158198043016,99157953549066,99157709030510,99157464487349]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4480+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4481 := params 0
abbrev ray4481 := rays 0
def bank4481 : Fin 2 → Cell := twoBank p4481 ray4481
theorem signs4481 : ∀ j, Signs p4481 (bank4481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4482 := params 1
abbrev ray4482 := rays 1
def bank4482 : Fin 2 → Cell := twoBank p4482 ray4482
theorem signs4482 : ∀ j, Signs p4482 (bank4482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4483 := params 2
abbrev ray4483 := rays 2
def bank4483 : Fin 2 → Cell := twoBank p4483 ray4483
theorem signs4483 : ∀ j, Signs p4483 (bank4483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4484 := params 3
abbrev ray4484 := rays 3
def bank4484 : Fin 2 → Cell := twoBank p4484 ray4484
theorem signs4484 : ∀ j, Signs p4484 (bank4484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4485 := params 4
abbrev ray4485 := rays 4
def bank4485 : Fin 2 → Cell := twoBank p4485 ray4485
theorem signs4485 : ∀ j, Signs p4485 (bank4485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4486 := params 5
abbrev ray4486 := rays 5
def bank4486 : Fin 2 → Cell := twoBank p4486 ray4486
theorem signs4486 : ∀ j, Signs p4486 (bank4486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4487 := params 6
abbrev ray4487 := rays 6
def bank4487 : Fin 2 → Cell := twoBank p4487 ray4487
theorem signs4487 : ∀ j, Signs p4487 (bank4487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4488 := params 7
abbrev ray4488 := rays 7
def bank4488 : Fin 2 → Cell := twoBank p4488 ray4488
theorem signs4488 : ∀ j, Signs p4488 (bank4488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4489 := params 8
abbrev ray4489 := rays 8
def bank4489 : Fin 2 → Cell := twoBank p4489 ray4489
theorem signs4489 : ∀ j, Signs p4489 (bank4489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4490 := params 9
abbrev ray4490 := rays 9
def bank4490 : Fin 2 → Cell := twoBank p4490 ray4490
theorem signs4490 : ∀ j, Signs p4490 (bank4490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4491 := params 10
abbrev ray4491 := rays 10
def bank4491 : Fin 2 → Cell := twoBank p4491 ray4491
theorem signs4491 : ∀ j, Signs p4491 (bank4491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4492 := params 11
abbrev ray4492 := rays 11
def bank4492 : Fin 2 → Cell := twoBank p4492 ray4492
theorem signs4492 : ∀ j, Signs p4492 (bank4492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4493 := params 12
abbrev ray4493 := rays 12
def bank4493 : Fin 2 → Cell := twoBank p4493 ray4493
theorem signs4493 : ∀ j, Signs p4493 (bank4493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4494 := params 13
abbrev ray4494 := rays 13
def bank4494 : Fin 2 → Cell := twoBank p4494 ray4494
theorem signs4494 : ∀ j, Signs p4494 (bank4494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4495 := params 14
abbrev ray4495 := rays 14
def bank4495 : Fin 2 → Cell := twoBank p4495 ray4495
theorem signs4495 : ∀ j, Signs p4495 (bank4495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4496 := params 15
abbrev ray4496 := rays 15
def bank4496 : Fin 2 → Cell := twoBank p4496 ray4496
theorem signs4496 : ∀ j, Signs p4496 (bank4496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4497 := params 16
abbrev ray4497 := rays 16
def bank4497 : Fin 2 → Cell := twoBank p4497 ray4497
theorem signs4497 : ∀ j, Signs p4497 (bank4497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4498 := params 17
abbrev ray4498 := rays 17
def bank4498 : Fin 2 → Cell := twoBank p4498 ray4498
theorem signs4498 : ∀ j, Signs p4498 (bank4498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4499 := params 18
abbrev ray4499 := rays 18
def bank4499 : Fin 2 → Cell := twoBank p4499 ray4499
theorem signs4499 : ∀ j, Signs p4499 (bank4499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4500 := params 19
abbrev ray4500 := rays 19
def bank4500 : Fin 2 → Cell := twoBank p4500 ray4500
theorem signs4500 : ∀ j, Signs p4500 (bank4500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4501 := params 20
abbrev ray4501 := rays 20
def bank4501 : Fin 2 → Cell := twoBank p4501 ray4501
theorem signs4501 : ∀ j, Signs p4501 (bank4501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4502 := params 21
abbrev ray4502 := rays 21
def bank4502 : Fin 2 → Cell := twoBank p4502 ray4502
theorem signs4502 : ∀ j, Signs p4502 (bank4502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4503 := params 22
abbrev ray4503 := rays 22
def bank4503 : Fin 2 → Cell := twoBank p4503 ray4503
theorem signs4503 : ∀ j, Signs p4503 (bank4503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4504 := params 23
abbrev ray4504 := rays 23
def bank4504 : Fin 2 → Cell := twoBank p4504 ray4504
theorem signs4504 : ∀ j, Signs p4504 (bank4504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4505 := params 24
abbrev ray4505 := rays 24
def bank4505 : Fin 2 → Cell := twoBank p4505 ray4505
theorem signs4505 : ∀ j, Signs p4505 (bank4505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4506 := params 25
abbrev ray4506 := rays 25
def bank4506 : Fin 2 → Cell := twoBank p4506 ray4506
theorem signs4506 : ∀ j, Signs p4506 (bank4506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4507 := params 26
abbrev ray4507 := rays 26
def bank4507 : Fin 2 → Cell := twoBank p4507 ray4507
theorem signs4507 : ∀ j, Signs p4507 (bank4507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4508 := params 27
abbrev ray4508 := rays 27
def bank4508 : Fin 2 → Cell := twoBank p4508 ray4508
theorem signs4508 : ∀ j, Signs p4508 (bank4508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4509 := params 28
abbrev ray4509 := rays 28
def bank4509 : Fin 2 → Cell := twoBank p4509 ray4509
theorem signs4509 : ∀ j, Signs p4509 (bank4509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4510 := params 29
abbrev ray4510 := rays 29
def bank4510 : Fin 2 → Cell := twoBank p4510 ray4510
theorem signs4510 : ∀ j, Signs p4510 (bank4510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4511 := params 30
abbrev ray4511 := rays 30
def bank4511 : Fin 2 → Cell := twoBank p4511 ray4511
theorem signs4511 : ∀ j, Signs p4511 (bank4511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4512 := params 31
abbrev ray4512 := rays 31
def bank4512 : Fin 2 → Cell := twoBank p4512 ray4512
theorem signs4512 : ∀ j, Signs p4512 (bank4512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04481_04512
