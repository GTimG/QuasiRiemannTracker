/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04513_04544
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99157464487349,99157219919583,99156975327214,99156730710243,99156486068671,99156241402499,99155996711728,99155751996359,99155507256394,99155262491833,99155017702677,99154772888928,99154528050586,99154283187652,99154038300128,99153793388015,99153548451313,99153303490024,99153058504149,99152813493688,99152568458643,99152323399015,99152078314805,99151833206014,99151588072643,99151342914693,99151097732166,99150852525062,99150607293382,99150362037128,99150116756300,99149871450899,99149626120927]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4512+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4513 := params 0
abbrev ray4513 := rays 0
def bank4513 : Fin 2 → Cell := twoBank p4513 ray4513
theorem signs4513 : ∀ j, Signs p4513 (bank4513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4514 := params 1
abbrev ray4514 := rays 1
def bank4514 : Fin 2 → Cell := twoBank p4514 ray4514
theorem signs4514 : ∀ j, Signs p4514 (bank4514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4515 := params 2
abbrev ray4515 := rays 2
def bank4515 : Fin 2 → Cell := twoBank p4515 ray4515
theorem signs4515 : ∀ j, Signs p4515 (bank4515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4516 := params 3
abbrev ray4516 := rays 3
def bank4516 : Fin 2 → Cell := twoBank p4516 ray4516
theorem signs4516 : ∀ j, Signs p4516 (bank4516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4517 := params 4
abbrev ray4517 := rays 4
def bank4517 : Fin 2 → Cell := twoBank p4517 ray4517
theorem signs4517 : ∀ j, Signs p4517 (bank4517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4518 := params 5
abbrev ray4518 := rays 5
def bank4518 : Fin 2 → Cell := twoBank p4518 ray4518
theorem signs4518 : ∀ j, Signs p4518 (bank4518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4519 := params 6
abbrev ray4519 := rays 6
def bank4519 : Fin 2 → Cell := twoBank p4519 ray4519
theorem signs4519 : ∀ j, Signs p4519 (bank4519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4520 := params 7
abbrev ray4520 := rays 7
def bank4520 : Fin 2 → Cell := twoBank p4520 ray4520
theorem signs4520 : ∀ j, Signs p4520 (bank4520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4521 := params 8
abbrev ray4521 := rays 8
def bank4521 : Fin 2 → Cell := twoBank p4521 ray4521
theorem signs4521 : ∀ j, Signs p4521 (bank4521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4522 := params 9
abbrev ray4522 := rays 9
def bank4522 : Fin 2 → Cell := twoBank p4522 ray4522
theorem signs4522 : ∀ j, Signs p4522 (bank4522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4523 := params 10
abbrev ray4523 := rays 10
def bank4523 : Fin 2 → Cell := twoBank p4523 ray4523
theorem signs4523 : ∀ j, Signs p4523 (bank4523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4524 := params 11
abbrev ray4524 := rays 11
def bank4524 : Fin 2 → Cell := twoBank p4524 ray4524
theorem signs4524 : ∀ j, Signs p4524 (bank4524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4525 := params 12
abbrev ray4525 := rays 12
def bank4525 : Fin 2 → Cell := twoBank p4525 ray4525
theorem signs4525 : ∀ j, Signs p4525 (bank4525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4526 := params 13
abbrev ray4526 := rays 13
def bank4526 : Fin 2 → Cell := twoBank p4526 ray4526
theorem signs4526 : ∀ j, Signs p4526 (bank4526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4527 := params 14
abbrev ray4527 := rays 14
def bank4527 : Fin 2 → Cell := twoBank p4527 ray4527
theorem signs4527 : ∀ j, Signs p4527 (bank4527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4528 := params 15
abbrev ray4528 := rays 15
def bank4528 : Fin 2 → Cell := twoBank p4528 ray4528
theorem signs4528 : ∀ j, Signs p4528 (bank4528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4529 := params 16
abbrev ray4529 := rays 16
def bank4529 : Fin 2 → Cell := twoBank p4529 ray4529
theorem signs4529 : ∀ j, Signs p4529 (bank4529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4530 := params 17
abbrev ray4530 := rays 17
def bank4530 : Fin 2 → Cell := twoBank p4530 ray4530
theorem signs4530 : ∀ j, Signs p4530 (bank4530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4531 := params 18
abbrev ray4531 := rays 18
def bank4531 : Fin 2 → Cell := twoBank p4531 ray4531
theorem signs4531 : ∀ j, Signs p4531 (bank4531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4532 := params 19
abbrev ray4532 := rays 19
def bank4532 : Fin 2 → Cell := twoBank p4532 ray4532
theorem signs4532 : ∀ j, Signs p4532 (bank4532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4533 := params 20
abbrev ray4533 := rays 20
def bank4533 : Fin 2 → Cell := twoBank p4533 ray4533
theorem signs4533 : ∀ j, Signs p4533 (bank4533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4534 := params 21
abbrev ray4534 := rays 21
def bank4534 : Fin 2 → Cell := twoBank p4534 ray4534
theorem signs4534 : ∀ j, Signs p4534 (bank4534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4535 := params 22
abbrev ray4535 := rays 22
def bank4535 : Fin 2 → Cell := twoBank p4535 ray4535
theorem signs4535 : ∀ j, Signs p4535 (bank4535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4536 := params 23
abbrev ray4536 := rays 23
def bank4536 : Fin 2 → Cell := twoBank p4536 ray4536
theorem signs4536 : ∀ j, Signs p4536 (bank4536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4537 := params 24
abbrev ray4537 := rays 24
def bank4537 : Fin 2 → Cell := twoBank p4537 ray4537
theorem signs4537 : ∀ j, Signs p4537 (bank4537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4538 := params 25
abbrev ray4538 := rays 25
def bank4538 : Fin 2 → Cell := twoBank p4538 ray4538
theorem signs4538 : ∀ j, Signs p4538 (bank4538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4539 := params 26
abbrev ray4539 := rays 26
def bank4539 : Fin 2 → Cell := twoBank p4539 ray4539
theorem signs4539 : ∀ j, Signs p4539 (bank4539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4540 := params 27
abbrev ray4540 := rays 27
def bank4540 : Fin 2 → Cell := twoBank p4540 ray4540
theorem signs4540 : ∀ j, Signs p4540 (bank4540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4541 := params 28
abbrev ray4541 := rays 28
def bank4541 : Fin 2 → Cell := twoBank p4541 ray4541
theorem signs4541 : ∀ j, Signs p4541 (bank4541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4542 := params 29
abbrev ray4542 := rays 29
def bank4542 : Fin 2 → Cell := twoBank p4542 ray4542
theorem signs4542 : ∀ j, Signs p4542 (bank4542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4543 := params 30
abbrev ray4543 := rays 30
def bank4543 : Fin 2 → Cell := twoBank p4543 ray4543
theorem signs4543 : ∀ j, Signs p4543 (bank4543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4544 := params 31
abbrev ray4544 := rays 31
def bank4544 : Fin 2 → Cell := twoBank p4544 ray4544
theorem signs4544 : ∀ j, Signs p4544 (bank4544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04513_04544
