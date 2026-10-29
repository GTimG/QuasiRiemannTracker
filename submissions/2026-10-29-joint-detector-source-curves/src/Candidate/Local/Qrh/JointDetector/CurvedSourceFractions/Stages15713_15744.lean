/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15713_15744
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95068630504862,95068161736090,95067692951313,95067224150530,95066755333741,95066286500947,95065817652147,95065348787342,95064879906532,95064411009716,95063942096895,95063473168069,95063004223238,95062535262402,95062066285561,95061597292715,95061128283864,95060659259008,95060190218147,95059721161282,95059252088412,95058782999537,95058313894658,95057844773774,95057375636886,95056906483993,95056437315096,95055968130195,95055498929289,95055029712379,95054560479465,95054091230547,95053621965625]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15712+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15713 := params 0
abbrev ray15713 := rays 0
def bank15713 : Fin 1 → Cell := oneBank p15713 ray15713
theorem signs15713 : ∀ j, Signs p15713 (bank15713 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15714 := params 1
abbrev ray15714 := rays 1
def bank15714 : Fin 1 → Cell := oneBank p15714 ray15714
theorem signs15714 : ∀ j, Signs p15714 (bank15714 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15715 := params 2
abbrev ray15715 := rays 2
def bank15715 : Fin 1 → Cell := oneBank p15715 ray15715
theorem signs15715 : ∀ j, Signs p15715 (bank15715 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15716 := params 3
abbrev ray15716 := rays 3
def bank15716 : Fin 1 → Cell := oneBank p15716 ray15716
theorem signs15716 : ∀ j, Signs p15716 (bank15716 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15717 := params 4
abbrev ray15717 := rays 4
def bank15717 : Fin 1 → Cell := oneBank p15717 ray15717
theorem signs15717 : ∀ j, Signs p15717 (bank15717 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15718 := params 5
abbrev ray15718 := rays 5
def bank15718 : Fin 1 → Cell := oneBank p15718 ray15718
theorem signs15718 : ∀ j, Signs p15718 (bank15718 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15719 := params 6
abbrev ray15719 := rays 6
def bank15719 : Fin 1 → Cell := oneBank p15719 ray15719
theorem signs15719 : ∀ j, Signs p15719 (bank15719 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15720 := params 7
abbrev ray15720 := rays 7
def bank15720 : Fin 1 → Cell := oneBank p15720 ray15720
theorem signs15720 : ∀ j, Signs p15720 (bank15720 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15721 := params 8
abbrev ray15721 := rays 8
def bank15721 : Fin 1 → Cell := oneBank p15721 ray15721
theorem signs15721 : ∀ j, Signs p15721 (bank15721 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15722 := params 9
abbrev ray15722 := rays 9
def bank15722 : Fin 1 → Cell := oneBank p15722 ray15722
theorem signs15722 : ∀ j, Signs p15722 (bank15722 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15723 := params 10
abbrev ray15723 := rays 10
def bank15723 : Fin 1 → Cell := oneBank p15723 ray15723
theorem signs15723 : ∀ j, Signs p15723 (bank15723 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15724 := params 11
abbrev ray15724 := rays 11
def bank15724 : Fin 1 → Cell := oneBank p15724 ray15724
theorem signs15724 : ∀ j, Signs p15724 (bank15724 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15725 := params 12
abbrev ray15725 := rays 12
def bank15725 : Fin 1 → Cell := oneBank p15725 ray15725
theorem signs15725 : ∀ j, Signs p15725 (bank15725 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15726 := params 13
abbrev ray15726 := rays 13
def bank15726 : Fin 1 → Cell := oneBank p15726 ray15726
theorem signs15726 : ∀ j, Signs p15726 (bank15726 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15727 := params 14
abbrev ray15727 := rays 14
def bank15727 : Fin 1 → Cell := oneBank p15727 ray15727
theorem signs15727 : ∀ j, Signs p15727 (bank15727 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15728 := params 15
abbrev ray15728 := rays 15
def bank15728 : Fin 1 → Cell := oneBank p15728 ray15728
theorem signs15728 : ∀ j, Signs p15728 (bank15728 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15729 := params 16
abbrev ray15729 := rays 16
def bank15729 : Fin 1 → Cell := oneBank p15729 ray15729
theorem signs15729 : ∀ j, Signs p15729 (bank15729 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15730 := params 17
abbrev ray15730 := rays 17
def bank15730 : Fin 1 → Cell := oneBank p15730 ray15730
theorem signs15730 : ∀ j, Signs p15730 (bank15730 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15731 := params 18
abbrev ray15731 := rays 18
def bank15731 : Fin 1 → Cell := oneBank p15731 ray15731
theorem signs15731 : ∀ j, Signs p15731 (bank15731 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15732 := params 19
abbrev ray15732 := rays 19
def bank15732 : Fin 1 → Cell := oneBank p15732 ray15732
theorem signs15732 : ∀ j, Signs p15732 (bank15732 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15733 := params 20
abbrev ray15733 := rays 20
def bank15733 : Fin 1 → Cell := oneBank p15733 ray15733
theorem signs15733 : ∀ j, Signs p15733 (bank15733 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15734 := params 21
abbrev ray15734 := rays 21
def bank15734 : Fin 1 → Cell := oneBank p15734 ray15734
theorem signs15734 : ∀ j, Signs p15734 (bank15734 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15735 := params 22
abbrev ray15735 := rays 22
def bank15735 : Fin 1 → Cell := oneBank p15735 ray15735
theorem signs15735 : ∀ j, Signs p15735 (bank15735 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15736 := params 23
abbrev ray15736 := rays 23
def bank15736 : Fin 1 → Cell := oneBank p15736 ray15736
theorem signs15736 : ∀ j, Signs p15736 (bank15736 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15737 := params 24
abbrev ray15737 := rays 24
def bank15737 : Fin 1 → Cell := oneBank p15737 ray15737
theorem signs15737 : ∀ j, Signs p15737 (bank15737 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15738 := params 25
abbrev ray15738 := rays 25
def bank15738 : Fin 1 → Cell := oneBank p15738 ray15738
theorem signs15738 : ∀ j, Signs p15738 (bank15738 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15739 := params 26
abbrev ray15739 := rays 26
def bank15739 : Fin 1 → Cell := oneBank p15739 ray15739
theorem signs15739 : ∀ j, Signs p15739 (bank15739 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15740 := params 27
abbrev ray15740 := rays 27
def bank15740 : Fin 1 → Cell := oneBank p15740 ray15740
theorem signs15740 : ∀ j, Signs p15740 (bank15740 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15741 := params 28
abbrev ray15741 := rays 28
def bank15741 : Fin 1 → Cell := oneBank p15741 ray15741
theorem signs15741 : ∀ j, Signs p15741 (bank15741 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15742 := params 29
abbrev ray15742 := rays 29
def bank15742 : Fin 1 → Cell := oneBank p15742 ray15742
theorem signs15742 : ∀ j, Signs p15742 (bank15742 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15743 := params 30
abbrev ray15743 := rays 30
def bank15743 : Fin 1 → Cell := oneBank p15743 ray15743
theorem signs15743 : ∀ j, Signs p15743 (bank15743 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15744 := params 31
abbrev ray15744 := rays 31
def bank15744 : Fin 1 → Cell := oneBank p15744 ray15744
theorem signs15744 : ∀ j, Signs p15744 (bank15744 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15713_15744
