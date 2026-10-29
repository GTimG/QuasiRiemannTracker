/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04545_04576
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99149626120927,99149380766384,99149135387272,99148889983592,99148644555344,99148399102530,99148153625151,99147908123208,99147662596702,99147417045634,99147171470005,99146925869816,99146680245068,99146434595762,99146188921900,99145943223482,99145697500509,99145451752983,99145205980904,99144960184274,99144714363093,99144468517363,99144222647084,99143976752258,99143730832886,99143484888969,99143238920507,99142992927502,99142746909955,99142500867867,99142254801239,99142008710072,99141762594368]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4544+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4545 := params 0
abbrev ray4545 := rays 0
def bank4545 : Fin 2 → Cell := twoBank p4545 ray4545
theorem signs4545 : ∀ j, Signs p4545 (bank4545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4546 := params 1
abbrev ray4546 := rays 1
def bank4546 : Fin 2 → Cell := twoBank p4546 ray4546
theorem signs4546 : ∀ j, Signs p4546 (bank4546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4547 := params 2
abbrev ray4547 := rays 2
def bank4547 : Fin 2 → Cell := twoBank p4547 ray4547
theorem signs4547 : ∀ j, Signs p4547 (bank4547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4548 := params 3
abbrev ray4548 := rays 3
def bank4548 : Fin 2 → Cell := twoBank p4548 ray4548
theorem signs4548 : ∀ j, Signs p4548 (bank4548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4549 := params 4
abbrev ray4549 := rays 4
def bank4549 : Fin 2 → Cell := twoBank p4549 ray4549
theorem signs4549 : ∀ j, Signs p4549 (bank4549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4550 := params 5
abbrev ray4550 := rays 5
def bank4550 : Fin 2 → Cell := twoBank p4550 ray4550
theorem signs4550 : ∀ j, Signs p4550 (bank4550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4551 := params 6
abbrev ray4551 := rays 6
def bank4551 : Fin 2 → Cell := twoBank p4551 ray4551
theorem signs4551 : ∀ j, Signs p4551 (bank4551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4552 := params 7
abbrev ray4552 := rays 7
def bank4552 : Fin 2 → Cell := twoBank p4552 ray4552
theorem signs4552 : ∀ j, Signs p4552 (bank4552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4553 := params 8
abbrev ray4553 := rays 8
def bank4553 : Fin 2 → Cell := twoBank p4553 ray4553
theorem signs4553 : ∀ j, Signs p4553 (bank4553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4554 := params 9
abbrev ray4554 := rays 9
def bank4554 : Fin 2 → Cell := twoBank p4554 ray4554
theorem signs4554 : ∀ j, Signs p4554 (bank4554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4555 := params 10
abbrev ray4555 := rays 10
def bank4555 : Fin 2 → Cell := twoBank p4555 ray4555
theorem signs4555 : ∀ j, Signs p4555 (bank4555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4556 := params 11
abbrev ray4556 := rays 11
def bank4556 : Fin 2 → Cell := twoBank p4556 ray4556
theorem signs4556 : ∀ j, Signs p4556 (bank4556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4557 := params 12
abbrev ray4557 := rays 12
def bank4557 : Fin 2 → Cell := twoBank p4557 ray4557
theorem signs4557 : ∀ j, Signs p4557 (bank4557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4558 := params 13
abbrev ray4558 := rays 13
def bank4558 : Fin 2 → Cell := twoBank p4558 ray4558
theorem signs4558 : ∀ j, Signs p4558 (bank4558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4559 := params 14
abbrev ray4559 := rays 14
def bank4559 : Fin 2 → Cell := twoBank p4559 ray4559
theorem signs4559 : ∀ j, Signs p4559 (bank4559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4560 := params 15
abbrev ray4560 := rays 15
def bank4560 : Fin 2 → Cell := twoBank p4560 ray4560
theorem signs4560 : ∀ j, Signs p4560 (bank4560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4561 := params 16
abbrev ray4561 := rays 16
def bank4561 : Fin 2 → Cell := twoBank p4561 ray4561
theorem signs4561 : ∀ j, Signs p4561 (bank4561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4562 := params 17
abbrev ray4562 := rays 17
def bank4562 : Fin 2 → Cell := twoBank p4562 ray4562
theorem signs4562 : ∀ j, Signs p4562 (bank4562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4563 := params 18
abbrev ray4563 := rays 18
def bank4563 : Fin 2 → Cell := twoBank p4563 ray4563
theorem signs4563 : ∀ j, Signs p4563 (bank4563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4564 := params 19
abbrev ray4564 := rays 19
def bank4564 : Fin 2 → Cell := twoBank p4564 ray4564
theorem signs4564 : ∀ j, Signs p4564 (bank4564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4565 := params 20
abbrev ray4565 := rays 20
def bank4565 : Fin 2 → Cell := twoBank p4565 ray4565
theorem signs4565 : ∀ j, Signs p4565 (bank4565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4566 := params 21
abbrev ray4566 := rays 21
def bank4566 : Fin 2 → Cell := twoBank p4566 ray4566
theorem signs4566 : ∀ j, Signs p4566 (bank4566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4567 := params 22
abbrev ray4567 := rays 22
def bank4567 : Fin 2 → Cell := twoBank p4567 ray4567
theorem signs4567 : ∀ j, Signs p4567 (bank4567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4568 := params 23
abbrev ray4568 := rays 23
def bank4568 : Fin 2 → Cell := twoBank p4568 ray4568
theorem signs4568 : ∀ j, Signs p4568 (bank4568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4569 := params 24
abbrev ray4569 := rays 24
def bank4569 : Fin 2 → Cell := twoBank p4569 ray4569
theorem signs4569 : ∀ j, Signs p4569 (bank4569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4570 := params 25
abbrev ray4570 := rays 25
def bank4570 : Fin 2 → Cell := twoBank p4570 ray4570
theorem signs4570 : ∀ j, Signs p4570 (bank4570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4571 := params 26
abbrev ray4571 := rays 26
def bank4571 : Fin 2 → Cell := twoBank p4571 ray4571
theorem signs4571 : ∀ j, Signs p4571 (bank4571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4572 := params 27
abbrev ray4572 := rays 27
def bank4572 : Fin 2 → Cell := twoBank p4572 ray4572
theorem signs4572 : ∀ j, Signs p4572 (bank4572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4573 := params 28
abbrev ray4573 := rays 28
def bank4573 : Fin 2 → Cell := twoBank p4573 ray4573
theorem signs4573 : ∀ j, Signs p4573 (bank4573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4574 := params 29
abbrev ray4574 := rays 29
def bank4574 : Fin 2 → Cell := twoBank p4574 ray4574
theorem signs4574 : ∀ j, Signs p4574 (bank4574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4575 := params 30
abbrev ray4575 := rays 30
def bank4575 : Fin 2 → Cell := twoBank p4575 ray4575
theorem signs4575 : ∀ j, Signs p4575 (bank4575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4576 := params 31
abbrev ray4576 := rays 31
def bank4576 : Fin 2 → Cell := twoBank p4576 ray4576
theorem signs4576 : ∀ j, Signs p4576 (bank4576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04545_04576
