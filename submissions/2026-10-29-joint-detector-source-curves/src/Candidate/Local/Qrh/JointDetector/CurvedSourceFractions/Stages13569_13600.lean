/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13569_13600
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96036705801811,96036271604565,96035837391018,96035403161171,96034968915023,96034534652575,96034100373828,96033666078781,96033231767434,96032797439788,96032363095843,96031928735599,96031494359057,96031059966216,96030625557077,96030191131640,96029756689906,96029322231874,96028887757545,96028453266919,96028018759996,96027584236776,96027149697260,96026715141448,96026280569340,96025845980936,96025411376237,96024976755242,96024542117952,96024107464367,96023672794488,96023238108314,96022803405846]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13568+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13569 := params 0
abbrev ray13569 := rays 0
def bank13569 : Fin 1 → Cell := oneBank p13569 ray13569
theorem signs13569 : ∀ j, Signs p13569 (bank13569 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13570 := params 1
abbrev ray13570 := rays 1
def bank13570 : Fin 1 → Cell := oneBank p13570 ray13570
theorem signs13570 : ∀ j, Signs p13570 (bank13570 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13571 := params 2
abbrev ray13571 := rays 2
def bank13571 : Fin 1 → Cell := oneBank p13571 ray13571
theorem signs13571 : ∀ j, Signs p13571 (bank13571 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13572 := params 3
abbrev ray13572 := rays 3
def bank13572 : Fin 1 → Cell := oneBank p13572 ray13572
theorem signs13572 : ∀ j, Signs p13572 (bank13572 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13573 := params 4
abbrev ray13573 := rays 4
def bank13573 : Fin 1 → Cell := oneBank p13573 ray13573
theorem signs13573 : ∀ j, Signs p13573 (bank13573 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13574 := params 5
abbrev ray13574 := rays 5
def bank13574 : Fin 1 → Cell := oneBank p13574 ray13574
theorem signs13574 : ∀ j, Signs p13574 (bank13574 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13575 := params 6
abbrev ray13575 := rays 6
def bank13575 : Fin 1 → Cell := oneBank p13575 ray13575
theorem signs13575 : ∀ j, Signs p13575 (bank13575 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13576 := params 7
abbrev ray13576 := rays 7
def bank13576 : Fin 1 → Cell := oneBank p13576 ray13576
theorem signs13576 : ∀ j, Signs p13576 (bank13576 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13577 := params 8
abbrev ray13577 := rays 8
def bank13577 : Fin 1 → Cell := oneBank p13577 ray13577
theorem signs13577 : ∀ j, Signs p13577 (bank13577 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13578 := params 9
abbrev ray13578 := rays 9
def bank13578 : Fin 1 → Cell := oneBank p13578 ray13578
theorem signs13578 : ∀ j, Signs p13578 (bank13578 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13579 := params 10
abbrev ray13579 := rays 10
def bank13579 : Fin 1 → Cell := oneBank p13579 ray13579
theorem signs13579 : ∀ j, Signs p13579 (bank13579 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13580 := params 11
abbrev ray13580 := rays 11
def bank13580 : Fin 1 → Cell := oneBank p13580 ray13580
theorem signs13580 : ∀ j, Signs p13580 (bank13580 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13581 := params 12
abbrev ray13581 := rays 12
def bank13581 : Fin 1 → Cell := oneBank p13581 ray13581
theorem signs13581 : ∀ j, Signs p13581 (bank13581 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13582 := params 13
abbrev ray13582 := rays 13
def bank13582 : Fin 1 → Cell := oneBank p13582 ray13582
theorem signs13582 : ∀ j, Signs p13582 (bank13582 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13583 := params 14
abbrev ray13583 := rays 14
def bank13583 : Fin 1 → Cell := oneBank p13583 ray13583
theorem signs13583 : ∀ j, Signs p13583 (bank13583 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13584 := params 15
abbrev ray13584 := rays 15
def bank13584 : Fin 1 → Cell := oneBank p13584 ray13584
theorem signs13584 : ∀ j, Signs p13584 (bank13584 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13585 := params 16
abbrev ray13585 := rays 16
def bank13585 : Fin 1 → Cell := oneBank p13585 ray13585
theorem signs13585 : ∀ j, Signs p13585 (bank13585 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13586 := params 17
abbrev ray13586 := rays 17
def bank13586 : Fin 1 → Cell := oneBank p13586 ray13586
theorem signs13586 : ∀ j, Signs p13586 (bank13586 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13587 := params 18
abbrev ray13587 := rays 18
def bank13587 : Fin 1 → Cell := oneBank p13587 ray13587
theorem signs13587 : ∀ j, Signs p13587 (bank13587 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13588 := params 19
abbrev ray13588 := rays 19
def bank13588 : Fin 1 → Cell := oneBank p13588 ray13588
theorem signs13588 : ∀ j, Signs p13588 (bank13588 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13589 := params 20
abbrev ray13589 := rays 20
def bank13589 : Fin 1 → Cell := oneBank p13589 ray13589
theorem signs13589 : ∀ j, Signs p13589 (bank13589 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13590 := params 21
abbrev ray13590 := rays 21
def bank13590 : Fin 1 → Cell := oneBank p13590 ray13590
theorem signs13590 : ∀ j, Signs p13590 (bank13590 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13591 := params 22
abbrev ray13591 := rays 22
def bank13591 : Fin 1 → Cell := oneBank p13591 ray13591
theorem signs13591 : ∀ j, Signs p13591 (bank13591 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13592 := params 23
abbrev ray13592 := rays 23
def bank13592 : Fin 1 → Cell := oneBank p13592 ray13592
theorem signs13592 : ∀ j, Signs p13592 (bank13592 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13593 := params 24
abbrev ray13593 := rays 24
def bank13593 : Fin 1 → Cell := oneBank p13593 ray13593
theorem signs13593 : ∀ j, Signs p13593 (bank13593 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13594 := params 25
abbrev ray13594 := rays 25
def bank13594 : Fin 1 → Cell := oneBank p13594 ray13594
theorem signs13594 : ∀ j, Signs p13594 (bank13594 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13595 := params 26
abbrev ray13595 := rays 26
def bank13595 : Fin 1 → Cell := oneBank p13595 ray13595
theorem signs13595 : ∀ j, Signs p13595 (bank13595 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13596 := params 27
abbrev ray13596 := rays 27
def bank13596 : Fin 1 → Cell := oneBank p13596 ray13596
theorem signs13596 : ∀ j, Signs p13596 (bank13596 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13597 := params 28
abbrev ray13597 := rays 28
def bank13597 : Fin 1 → Cell := oneBank p13597 ray13597
theorem signs13597 : ∀ j, Signs p13597 (bank13597 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13598 := params 29
abbrev ray13598 := rays 29
def bank13598 : Fin 1 → Cell := oneBank p13598 ray13598
theorem signs13598 : ∀ j, Signs p13598 (bank13598 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13599 := params 30
abbrev ray13599 := rays 30
def bank13599 : Fin 1 → Cell := oneBank p13599 ray13599
theorem signs13599 : ∀ j, Signs p13599 (bank13599 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13600 := params 31
abbrev ray13600 := rays 31
def bank13600 : Fin 1 → Cell := oneBank p13600 ray13600
theorem signs13600 : ∀ j, Signs p13600 (bank13600 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13569_13600
