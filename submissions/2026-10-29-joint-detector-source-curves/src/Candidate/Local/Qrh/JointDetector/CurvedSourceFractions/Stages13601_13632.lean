/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13601_13632
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96022803405846,96022368687084,96021933952028,96021499200678,96021064433035,96020629649099,96020194848870,96019760032348,96019325199534,96018890350427,96018455485028,96018020603337,96017585705355,96017150791081,96016715860516,96016280913660,96015845950513,96015410971076,96014975975348,96014540963330,96014105935022,96013670890424,96013235829537,96012800752361,96012365658895,96011930549141,96011495423098,96011060280766,96010625122146,96010189947238,96009754756042,96009319548559,96008884324788]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13600+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13601 := params 0
abbrev ray13601 := rays 0
def bank13601 : Fin 1 → Cell := oneBank p13601 ray13601
theorem signs13601 : ∀ j, Signs p13601 (bank13601 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13602 := params 1
abbrev ray13602 := rays 1
def bank13602 : Fin 1 → Cell := oneBank p13602 ray13602
theorem signs13602 : ∀ j, Signs p13602 (bank13602 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13603 := params 2
abbrev ray13603 := rays 2
def bank13603 : Fin 1 → Cell := oneBank p13603 ray13603
theorem signs13603 : ∀ j, Signs p13603 (bank13603 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13604 := params 3
abbrev ray13604 := rays 3
def bank13604 : Fin 1 → Cell := oneBank p13604 ray13604
theorem signs13604 : ∀ j, Signs p13604 (bank13604 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13605 := params 4
abbrev ray13605 := rays 4
def bank13605 : Fin 1 → Cell := oneBank p13605 ray13605
theorem signs13605 : ∀ j, Signs p13605 (bank13605 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13606 := params 5
abbrev ray13606 := rays 5
def bank13606 : Fin 1 → Cell := oneBank p13606 ray13606
theorem signs13606 : ∀ j, Signs p13606 (bank13606 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13607 := params 6
abbrev ray13607 := rays 6
def bank13607 : Fin 1 → Cell := oneBank p13607 ray13607
theorem signs13607 : ∀ j, Signs p13607 (bank13607 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13608 := params 7
abbrev ray13608 := rays 7
def bank13608 : Fin 1 → Cell := oneBank p13608 ray13608
theorem signs13608 : ∀ j, Signs p13608 (bank13608 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13609 := params 8
abbrev ray13609 := rays 8
def bank13609 : Fin 1 → Cell := oneBank p13609 ray13609
theorem signs13609 : ∀ j, Signs p13609 (bank13609 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13610 := params 9
abbrev ray13610 := rays 9
def bank13610 : Fin 1 → Cell := oneBank p13610 ray13610
theorem signs13610 : ∀ j, Signs p13610 (bank13610 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13611 := params 10
abbrev ray13611 := rays 10
def bank13611 : Fin 1 → Cell := oneBank p13611 ray13611
theorem signs13611 : ∀ j, Signs p13611 (bank13611 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13612 := params 11
abbrev ray13612 := rays 11
def bank13612 : Fin 1 → Cell := oneBank p13612 ray13612
theorem signs13612 : ∀ j, Signs p13612 (bank13612 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13613 := params 12
abbrev ray13613 := rays 12
def bank13613 : Fin 1 → Cell := oneBank p13613 ray13613
theorem signs13613 : ∀ j, Signs p13613 (bank13613 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13614 := params 13
abbrev ray13614 := rays 13
def bank13614 : Fin 1 → Cell := oneBank p13614 ray13614
theorem signs13614 : ∀ j, Signs p13614 (bank13614 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13615 := params 14
abbrev ray13615 := rays 14
def bank13615 : Fin 1 → Cell := oneBank p13615 ray13615
theorem signs13615 : ∀ j, Signs p13615 (bank13615 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13616 := params 15
abbrev ray13616 := rays 15
def bank13616 : Fin 1 → Cell := oneBank p13616 ray13616
theorem signs13616 : ∀ j, Signs p13616 (bank13616 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13617 := params 16
abbrev ray13617 := rays 16
def bank13617 : Fin 1 → Cell := oneBank p13617 ray13617
theorem signs13617 : ∀ j, Signs p13617 (bank13617 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13618 := params 17
abbrev ray13618 := rays 17
def bank13618 : Fin 1 → Cell := oneBank p13618 ray13618
theorem signs13618 : ∀ j, Signs p13618 (bank13618 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13619 := params 18
abbrev ray13619 := rays 18
def bank13619 : Fin 1 → Cell := oneBank p13619 ray13619
theorem signs13619 : ∀ j, Signs p13619 (bank13619 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13620 := params 19
abbrev ray13620 := rays 19
def bank13620 : Fin 1 → Cell := oneBank p13620 ray13620
theorem signs13620 : ∀ j, Signs p13620 (bank13620 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13621 := params 20
abbrev ray13621 := rays 20
def bank13621 : Fin 1 → Cell := oneBank p13621 ray13621
theorem signs13621 : ∀ j, Signs p13621 (bank13621 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13622 := params 21
abbrev ray13622 := rays 21
def bank13622 : Fin 1 → Cell := oneBank p13622 ray13622
theorem signs13622 : ∀ j, Signs p13622 (bank13622 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13623 := params 22
abbrev ray13623 := rays 22
def bank13623 : Fin 1 → Cell := oneBank p13623 ray13623
theorem signs13623 : ∀ j, Signs p13623 (bank13623 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13624 := params 23
abbrev ray13624 := rays 23
def bank13624 : Fin 1 → Cell := oneBank p13624 ray13624
theorem signs13624 : ∀ j, Signs p13624 (bank13624 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13625 := params 24
abbrev ray13625 := rays 24
def bank13625 : Fin 1 → Cell := oneBank p13625 ray13625
theorem signs13625 : ∀ j, Signs p13625 (bank13625 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13626 := params 25
abbrev ray13626 := rays 25
def bank13626 : Fin 1 → Cell := oneBank p13626 ray13626
theorem signs13626 : ∀ j, Signs p13626 (bank13626 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13627 := params 26
abbrev ray13627 := rays 26
def bank13627 : Fin 1 → Cell := oneBank p13627 ray13627
theorem signs13627 : ∀ j, Signs p13627 (bank13627 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13628 := params 27
abbrev ray13628 := rays 27
def bank13628 : Fin 1 → Cell := oneBank p13628 ray13628
theorem signs13628 : ∀ j, Signs p13628 (bank13628 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13629 := params 28
abbrev ray13629 := rays 28
def bank13629 : Fin 1 → Cell := oneBank p13629 ray13629
theorem signs13629 : ∀ j, Signs p13629 (bank13629 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13630 := params 29
abbrev ray13630 := rays 29
def bank13630 : Fin 1 → Cell := oneBank p13630 ray13630
theorem signs13630 : ∀ j, Signs p13630 (bank13630 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13631 := params 30
abbrev ray13631 := rays 30
def bank13631 : Fin 1 → Cell := oneBank p13631 ray13631
theorem signs13631 : ∀ j, Signs p13631 (bank13631 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13632 := params 31
abbrev ray13632 := rays 31
def bank13632 : Fin 1 → Cell := oneBank p13632 ray13632
theorem signs13632 : ∀ j, Signs p13632 (bank13632 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13601_13632
