/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04609_04640
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99133873942105,99133627017239,99133380067871,99133133094001,99132886095631,99132639072762,99132392025395,99132144953531,99131897857171,99131650736316,99131403590967,99131156421125,99130909226791,99130662007967,99130414764653,99130167496850,99129920204560,99129672887783,99129425546520,99129178180773,99128930790542,99128683375829,99128435936635,99128188472960,99127940984806,99127693472174,99127445935064,99127198373478,99126950787417,99126703176882,99126455541874,99126207882394,99125960198443]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4608+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4609 := params 0
abbrev ray4609 := rays 0
def bank4609 : Fin 2 → Cell := twoBank p4609 ray4609
theorem signs4609 : ∀ j, Signs p4609 (bank4609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4610 := params 1
abbrev ray4610 := rays 1
def bank4610 : Fin 2 → Cell := twoBank p4610 ray4610
theorem signs4610 : ∀ j, Signs p4610 (bank4610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4611 := params 2
abbrev ray4611 := rays 2
def bank4611 : Fin 2 → Cell := twoBank p4611 ray4611
theorem signs4611 : ∀ j, Signs p4611 (bank4611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4612 := params 3
abbrev ray4612 := rays 3
def bank4612 : Fin 2 → Cell := twoBank p4612 ray4612
theorem signs4612 : ∀ j, Signs p4612 (bank4612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4613 := params 4
abbrev ray4613 := rays 4
def bank4613 : Fin 2 → Cell := twoBank p4613 ray4613
theorem signs4613 : ∀ j, Signs p4613 (bank4613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4614 := params 5
abbrev ray4614 := rays 5
def bank4614 : Fin 2 → Cell := twoBank p4614 ray4614
theorem signs4614 : ∀ j, Signs p4614 (bank4614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4615 := params 6
abbrev ray4615 := rays 6
def bank4615 : Fin 2 → Cell := twoBank p4615 ray4615
theorem signs4615 : ∀ j, Signs p4615 (bank4615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4616 := params 7
abbrev ray4616 := rays 7
def bank4616 : Fin 2 → Cell := twoBank p4616 ray4616
theorem signs4616 : ∀ j, Signs p4616 (bank4616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4617 := params 8
abbrev ray4617 := rays 8
def bank4617 : Fin 2 → Cell := twoBank p4617 ray4617
theorem signs4617 : ∀ j, Signs p4617 (bank4617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4618 := params 9
abbrev ray4618 := rays 9
def bank4618 : Fin 2 → Cell := twoBank p4618 ray4618
theorem signs4618 : ∀ j, Signs p4618 (bank4618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4619 := params 10
abbrev ray4619 := rays 10
def bank4619 : Fin 2 → Cell := twoBank p4619 ray4619
theorem signs4619 : ∀ j, Signs p4619 (bank4619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4620 := params 11
abbrev ray4620 := rays 11
def bank4620 : Fin 2 → Cell := twoBank p4620 ray4620
theorem signs4620 : ∀ j, Signs p4620 (bank4620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4621 := params 12
abbrev ray4621 := rays 12
def bank4621 : Fin 2 → Cell := twoBank p4621 ray4621
theorem signs4621 : ∀ j, Signs p4621 (bank4621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4622 := params 13
abbrev ray4622 := rays 13
def bank4622 : Fin 2 → Cell := twoBank p4622 ray4622
theorem signs4622 : ∀ j, Signs p4622 (bank4622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4623 := params 14
abbrev ray4623 := rays 14
def bank4623 : Fin 2 → Cell := twoBank p4623 ray4623
theorem signs4623 : ∀ j, Signs p4623 (bank4623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4624 := params 15
abbrev ray4624 := rays 15
def bank4624 : Fin 2 → Cell := twoBank p4624 ray4624
theorem signs4624 : ∀ j, Signs p4624 (bank4624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4625 := params 16
abbrev ray4625 := rays 16
def bank4625 : Fin 2 → Cell := twoBank p4625 ray4625
theorem signs4625 : ∀ j, Signs p4625 (bank4625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4626 := params 17
abbrev ray4626 := rays 17
def bank4626 : Fin 2 → Cell := twoBank p4626 ray4626
theorem signs4626 : ∀ j, Signs p4626 (bank4626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4627 := params 18
abbrev ray4627 := rays 18
def bank4627 : Fin 2 → Cell := twoBank p4627 ray4627
theorem signs4627 : ∀ j, Signs p4627 (bank4627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4628 := params 19
abbrev ray4628 := rays 19
def bank4628 : Fin 2 → Cell := twoBank p4628 ray4628
theorem signs4628 : ∀ j, Signs p4628 (bank4628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4629 := params 20
abbrev ray4629 := rays 20
def bank4629 : Fin 2 → Cell := twoBank p4629 ray4629
theorem signs4629 : ∀ j, Signs p4629 (bank4629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4630 := params 21
abbrev ray4630 := rays 21
def bank4630 : Fin 2 → Cell := twoBank p4630 ray4630
theorem signs4630 : ∀ j, Signs p4630 (bank4630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4631 := params 22
abbrev ray4631 := rays 22
def bank4631 : Fin 2 → Cell := twoBank p4631 ray4631
theorem signs4631 : ∀ j, Signs p4631 (bank4631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4632 := params 23
abbrev ray4632 := rays 23
def bank4632 : Fin 2 → Cell := twoBank p4632 ray4632
theorem signs4632 : ∀ j, Signs p4632 (bank4632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4633 := params 24
abbrev ray4633 := rays 24
def bank4633 : Fin 2 → Cell := twoBank p4633 ray4633
theorem signs4633 : ∀ j, Signs p4633 (bank4633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4634 := params 25
abbrev ray4634 := rays 25
def bank4634 : Fin 2 → Cell := twoBank p4634 ray4634
theorem signs4634 : ∀ j, Signs p4634 (bank4634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4635 := params 26
abbrev ray4635 := rays 26
def bank4635 : Fin 2 → Cell := twoBank p4635 ray4635
theorem signs4635 : ∀ j, Signs p4635 (bank4635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4636 := params 27
abbrev ray4636 := rays 27
def bank4636 : Fin 2 → Cell := twoBank p4636 ray4636
theorem signs4636 : ∀ j, Signs p4636 (bank4636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4637 := params 28
abbrev ray4637 := rays 28
def bank4637 : Fin 2 → Cell := twoBank p4637 ray4637
theorem signs4637 : ∀ j, Signs p4637 (bank4637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4638 := params 29
abbrev ray4638 := rays 29
def bank4638 : Fin 2 → Cell := twoBank p4638 ray4638
theorem signs4638 : ∀ j, Signs p4638 (bank4638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4639 := params 30
abbrev ray4639 := rays 30
def bank4639 : Fin 2 → Cell := twoBank p4639 ray4639
theorem signs4639 : ∀ j, Signs p4639 (bank4639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4640 := params 31
abbrev ray4640 := rays 31
def bank4640 : Fin 2 → Cell := twoBank p4640 ray4640
theorem signs4640 : ∀ j, Signs p4640 (bank4640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04609_04640
