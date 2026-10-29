/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14593_14624
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95583585300309,95583134511706,95582683706986,95582232886149,95581782049195,95581331196125,95580880326938,95580429441635,95579978540215,95579527622679,95579076689027,95578625739259,95578174773375,95577723791376,95577272793261,95576821779031,95576370748686,95575919702226,95575468639651,95575017560961,95574566466156,95574115355237,95573664228204,95573213085056,95572761925794,95572310750418,95571859558929,95571408351326,95570957127609,95570505887779,95570054631836,95569603359780,95569152071611]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14592+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14593 := params 0
abbrev ray14593 := rays 0
def bank14593 : Fin 1 → Cell := oneBank p14593 ray14593
theorem signs14593 : ∀ j, Signs p14593 (bank14593 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14594 := params 1
abbrev ray14594 := rays 1
def bank14594 : Fin 1 → Cell := oneBank p14594 ray14594
theorem signs14594 : ∀ j, Signs p14594 (bank14594 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14595 := params 2
abbrev ray14595 := rays 2
def bank14595 : Fin 1 → Cell := oneBank p14595 ray14595
theorem signs14595 : ∀ j, Signs p14595 (bank14595 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14596 := params 3
abbrev ray14596 := rays 3
def bank14596 : Fin 1 → Cell := oneBank p14596 ray14596
theorem signs14596 : ∀ j, Signs p14596 (bank14596 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14597 := params 4
abbrev ray14597 := rays 4
def bank14597 : Fin 1 → Cell := oneBank p14597 ray14597
theorem signs14597 : ∀ j, Signs p14597 (bank14597 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14598 := params 5
abbrev ray14598 := rays 5
def bank14598 : Fin 1 → Cell := oneBank p14598 ray14598
theorem signs14598 : ∀ j, Signs p14598 (bank14598 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14599 := params 6
abbrev ray14599 := rays 6
def bank14599 : Fin 1 → Cell := oneBank p14599 ray14599
theorem signs14599 : ∀ j, Signs p14599 (bank14599 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14600 := params 7
abbrev ray14600 := rays 7
def bank14600 : Fin 1 → Cell := oneBank p14600 ray14600
theorem signs14600 : ∀ j, Signs p14600 (bank14600 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14601 := params 8
abbrev ray14601 := rays 8
def bank14601 : Fin 1 → Cell := oneBank p14601 ray14601
theorem signs14601 : ∀ j, Signs p14601 (bank14601 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14602 := params 9
abbrev ray14602 := rays 9
def bank14602 : Fin 1 → Cell := oneBank p14602 ray14602
theorem signs14602 : ∀ j, Signs p14602 (bank14602 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14603 := params 10
abbrev ray14603 := rays 10
def bank14603 : Fin 1 → Cell := oneBank p14603 ray14603
theorem signs14603 : ∀ j, Signs p14603 (bank14603 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14604 := params 11
abbrev ray14604 := rays 11
def bank14604 : Fin 1 → Cell := oneBank p14604 ray14604
theorem signs14604 : ∀ j, Signs p14604 (bank14604 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14605 := params 12
abbrev ray14605 := rays 12
def bank14605 : Fin 1 → Cell := oneBank p14605 ray14605
theorem signs14605 : ∀ j, Signs p14605 (bank14605 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14606 := params 13
abbrev ray14606 := rays 13
def bank14606 : Fin 1 → Cell := oneBank p14606 ray14606
theorem signs14606 : ∀ j, Signs p14606 (bank14606 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14607 := params 14
abbrev ray14607 := rays 14
def bank14607 : Fin 1 → Cell := oneBank p14607 ray14607
theorem signs14607 : ∀ j, Signs p14607 (bank14607 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14608 := params 15
abbrev ray14608 := rays 15
def bank14608 : Fin 1 → Cell := oneBank p14608 ray14608
theorem signs14608 : ∀ j, Signs p14608 (bank14608 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14609 := params 16
abbrev ray14609 := rays 16
def bank14609 : Fin 1 → Cell := oneBank p14609 ray14609
theorem signs14609 : ∀ j, Signs p14609 (bank14609 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14610 := params 17
abbrev ray14610 := rays 17
def bank14610 : Fin 1 → Cell := oneBank p14610 ray14610
theorem signs14610 : ∀ j, Signs p14610 (bank14610 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14611 := params 18
abbrev ray14611 := rays 18
def bank14611 : Fin 1 → Cell := oneBank p14611 ray14611
theorem signs14611 : ∀ j, Signs p14611 (bank14611 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14612 := params 19
abbrev ray14612 := rays 19
def bank14612 : Fin 1 → Cell := oneBank p14612 ray14612
theorem signs14612 : ∀ j, Signs p14612 (bank14612 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14613 := params 20
abbrev ray14613 := rays 20
def bank14613 : Fin 1 → Cell := oneBank p14613 ray14613
theorem signs14613 : ∀ j, Signs p14613 (bank14613 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14614 := params 21
abbrev ray14614 := rays 21
def bank14614 : Fin 1 → Cell := oneBank p14614 ray14614
theorem signs14614 : ∀ j, Signs p14614 (bank14614 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14615 := params 22
abbrev ray14615 := rays 22
def bank14615 : Fin 1 → Cell := oneBank p14615 ray14615
theorem signs14615 : ∀ j, Signs p14615 (bank14615 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14616 := params 23
abbrev ray14616 := rays 23
def bank14616 : Fin 1 → Cell := oneBank p14616 ray14616
theorem signs14616 : ∀ j, Signs p14616 (bank14616 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14617 := params 24
abbrev ray14617 := rays 24
def bank14617 : Fin 1 → Cell := oneBank p14617 ray14617
theorem signs14617 : ∀ j, Signs p14617 (bank14617 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14618 := params 25
abbrev ray14618 := rays 25
def bank14618 : Fin 1 → Cell := oneBank p14618 ray14618
theorem signs14618 : ∀ j, Signs p14618 (bank14618 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14619 := params 26
abbrev ray14619 := rays 26
def bank14619 : Fin 1 → Cell := oneBank p14619 ray14619
theorem signs14619 : ∀ j, Signs p14619 (bank14619 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14620 := params 27
abbrev ray14620 := rays 27
def bank14620 : Fin 1 → Cell := oneBank p14620 ray14620
theorem signs14620 : ∀ j, Signs p14620 (bank14620 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14621 := params 28
abbrev ray14621 := rays 28
def bank14621 : Fin 1 → Cell := oneBank p14621 ray14621
theorem signs14621 : ∀ j, Signs p14621 (bank14621 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14622 := params 29
abbrev ray14622 := rays 29
def bank14622 : Fin 1 → Cell := oneBank p14622 ray14622
theorem signs14622 : ∀ j, Signs p14622 (bank14622 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14623 := params 30
abbrev ray14623 := rays 30
def bank14623 : Fin 1 → Cell := oneBank p14623 ray14623
theorem signs14623 : ∀ j, Signs p14623 (bank14623 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14624 := params 31
abbrev ray14624 := rays 31
def bank14624 : Fin 1 → Cell := oneBank p14624 ray14624
theorem signs14624 : ∀ j, Signs p14624 (bank14624 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14593_14624
