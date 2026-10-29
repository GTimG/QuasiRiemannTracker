/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04705_04736
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99110057573477,99109808301139,99109559004399,99109309683257,99109060337715,99108810967773,99108561573433,99108312154695,99108062711561,99107813244032,99107563752108,99107314235791,99107064695082,99106815129982,99106565540492,99106315926612,99106066288344,99105816625689,99105566938648,99105317227222,99105067491412,99104817731219,99104567946644,99104318137688,99104068304353,99103818446639,99103568564547,99103318658078,99103068727233,99102818772014,99102568792421,99102318788455,99102068760118]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4704+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4705 := params 0
abbrev ray4705 := rays 0
def bank4705 : Fin 2 → Cell := twoBank p4705 ray4705
theorem signs4705 : ∀ j, Signs p4705 (bank4705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4706 := params 1
abbrev ray4706 := rays 1
def bank4706 : Fin 2 → Cell := twoBank p4706 ray4706
theorem signs4706 : ∀ j, Signs p4706 (bank4706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4707 := params 2
abbrev ray4707 := rays 2
def bank4707 : Fin 2 → Cell := twoBank p4707 ray4707
theorem signs4707 : ∀ j, Signs p4707 (bank4707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4708 := params 3
abbrev ray4708 := rays 3
def bank4708 : Fin 2 → Cell := twoBank p4708 ray4708
theorem signs4708 : ∀ j, Signs p4708 (bank4708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4709 := params 4
abbrev ray4709 := rays 4
def bank4709 : Fin 2 → Cell := twoBank p4709 ray4709
theorem signs4709 : ∀ j, Signs p4709 (bank4709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4710 := params 5
abbrev ray4710 := rays 5
def bank4710 : Fin 2 → Cell := twoBank p4710 ray4710
theorem signs4710 : ∀ j, Signs p4710 (bank4710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4711 := params 6
abbrev ray4711 := rays 6
def bank4711 : Fin 2 → Cell := twoBank p4711 ray4711
theorem signs4711 : ∀ j, Signs p4711 (bank4711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4712 := params 7
abbrev ray4712 := rays 7
def bank4712 : Fin 2 → Cell := twoBank p4712 ray4712
theorem signs4712 : ∀ j, Signs p4712 (bank4712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4713 := params 8
abbrev ray4713 := rays 8
def bank4713 : Fin 2 → Cell := twoBank p4713 ray4713
theorem signs4713 : ∀ j, Signs p4713 (bank4713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4714 := params 9
abbrev ray4714 := rays 9
def bank4714 : Fin 2 → Cell := twoBank p4714 ray4714
theorem signs4714 : ∀ j, Signs p4714 (bank4714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4715 := params 10
abbrev ray4715 := rays 10
def bank4715 : Fin 2 → Cell := twoBank p4715 ray4715
theorem signs4715 : ∀ j, Signs p4715 (bank4715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4716 := params 11
abbrev ray4716 := rays 11
def bank4716 : Fin 2 → Cell := twoBank p4716 ray4716
theorem signs4716 : ∀ j, Signs p4716 (bank4716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4717 := params 12
abbrev ray4717 := rays 12
def bank4717 : Fin 2 → Cell := twoBank p4717 ray4717
theorem signs4717 : ∀ j, Signs p4717 (bank4717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4718 := params 13
abbrev ray4718 := rays 13
def bank4718 : Fin 2 → Cell := twoBank p4718 ray4718
theorem signs4718 : ∀ j, Signs p4718 (bank4718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4719 := params 14
abbrev ray4719 := rays 14
def bank4719 : Fin 2 → Cell := twoBank p4719 ray4719
theorem signs4719 : ∀ j, Signs p4719 (bank4719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4720 := params 15
abbrev ray4720 := rays 15
def bank4720 : Fin 2 → Cell := twoBank p4720 ray4720
theorem signs4720 : ∀ j, Signs p4720 (bank4720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4721 := params 16
abbrev ray4721 := rays 16
def bank4721 : Fin 2 → Cell := twoBank p4721 ray4721
theorem signs4721 : ∀ j, Signs p4721 (bank4721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4722 := params 17
abbrev ray4722 := rays 17
def bank4722 : Fin 2 → Cell := twoBank p4722 ray4722
theorem signs4722 : ∀ j, Signs p4722 (bank4722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4723 := params 18
abbrev ray4723 := rays 18
def bank4723 : Fin 2 → Cell := twoBank p4723 ray4723
theorem signs4723 : ∀ j, Signs p4723 (bank4723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4724 := params 19
abbrev ray4724 := rays 19
def bank4724 : Fin 2 → Cell := twoBank p4724 ray4724
theorem signs4724 : ∀ j, Signs p4724 (bank4724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4725 := params 20
abbrev ray4725 := rays 20
def bank4725 : Fin 2 → Cell := twoBank p4725 ray4725
theorem signs4725 : ∀ j, Signs p4725 (bank4725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4726 := params 21
abbrev ray4726 := rays 21
def bank4726 : Fin 2 → Cell := twoBank p4726 ray4726
theorem signs4726 : ∀ j, Signs p4726 (bank4726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4727 := params 22
abbrev ray4727 := rays 22
def bank4727 : Fin 2 → Cell := twoBank p4727 ray4727
theorem signs4727 : ∀ j, Signs p4727 (bank4727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4728 := params 23
abbrev ray4728 := rays 23
def bank4728 : Fin 2 → Cell := twoBank p4728 ray4728
theorem signs4728 : ∀ j, Signs p4728 (bank4728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4729 := params 24
abbrev ray4729 := rays 24
def bank4729 : Fin 2 → Cell := twoBank p4729 ray4729
theorem signs4729 : ∀ j, Signs p4729 (bank4729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4730 := params 25
abbrev ray4730 := rays 25
def bank4730 : Fin 2 → Cell := twoBank p4730 ray4730
theorem signs4730 : ∀ j, Signs p4730 (bank4730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4731 := params 26
abbrev ray4731 := rays 26
def bank4731 : Fin 2 → Cell := twoBank p4731 ray4731
theorem signs4731 : ∀ j, Signs p4731 (bank4731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4732 := params 27
abbrev ray4732 := rays 27
def bank4732 : Fin 2 → Cell := twoBank p4732 ray4732
theorem signs4732 : ∀ j, Signs p4732 (bank4732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4733 := params 28
abbrev ray4733 := rays 28
def bank4733 : Fin 2 → Cell := twoBank p4733 ray4733
theorem signs4733 : ∀ j, Signs p4733 (bank4733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4734 := params 29
abbrev ray4734 := rays 29
def bank4734 : Fin 2 → Cell := twoBank p4734 ray4734
theorem signs4734 : ∀ j, Signs p4734 (bank4734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4735 := params 30
abbrev ray4735 := rays 30
def bank4735 : Fin 2 → Cell := twoBank p4735 ray4735
theorem signs4735 : ∀ j, Signs p4735 (bank4735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4736 := params 31
abbrev ray4736 := rays 31
def bank4736 : Fin 2 → Cell := twoBank p4736 ray4736
theorem signs4736 : ∀ j, Signs p4736 (bank4736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04705_04736
