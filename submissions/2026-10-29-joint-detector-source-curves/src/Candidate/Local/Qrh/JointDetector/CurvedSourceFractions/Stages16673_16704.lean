/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16673_16704
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94611250607320,94610766488673,94610282354041,94609798203424,94609314036822,94608829854235,94608345655664,94607861441108,94607377210567,94606892964041,94606408701530,94605924423034,94605440128553,94604955818087,94604471491636,94603987149200,94603502790779,94603018416373,94602534025982,94602049619606,94601565197245,94601080758899,94600596304568,94600111834252,94599627347951,94599142845664,94598658327392,94598173793135,94597689242893,94597204676666,94596720094453,94596235496255,94595750882072]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16672+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16673 := params 0
abbrev ray16673 := rays 0
def bank16673 : Fin 1 → Cell := oneBank p16673 ray16673
theorem signs16673 : ∀ j, Signs p16673 (bank16673 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16674 := params 1
abbrev ray16674 := rays 1
def bank16674 : Fin 1 → Cell := oneBank p16674 ray16674
theorem signs16674 : ∀ j, Signs p16674 (bank16674 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16675 := params 2
abbrev ray16675 := rays 2
def bank16675 : Fin 1 → Cell := oneBank p16675 ray16675
theorem signs16675 : ∀ j, Signs p16675 (bank16675 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16676 := params 3
abbrev ray16676 := rays 3
def bank16676 : Fin 1 → Cell := oneBank p16676 ray16676
theorem signs16676 : ∀ j, Signs p16676 (bank16676 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16677 := params 4
abbrev ray16677 := rays 4
def bank16677 : Fin 1 → Cell := oneBank p16677 ray16677
theorem signs16677 : ∀ j, Signs p16677 (bank16677 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16678 := params 5
abbrev ray16678 := rays 5
def bank16678 : Fin 1 → Cell := oneBank p16678 ray16678
theorem signs16678 : ∀ j, Signs p16678 (bank16678 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16679 := params 6
abbrev ray16679 := rays 6
def bank16679 : Fin 1 → Cell := oneBank p16679 ray16679
theorem signs16679 : ∀ j, Signs p16679 (bank16679 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16680 := params 7
abbrev ray16680 := rays 7
def bank16680 : Fin 1 → Cell := oneBank p16680 ray16680
theorem signs16680 : ∀ j, Signs p16680 (bank16680 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16681 := params 8
abbrev ray16681 := rays 8
def bank16681 : Fin 1 → Cell := oneBank p16681 ray16681
theorem signs16681 : ∀ j, Signs p16681 (bank16681 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16682 := params 9
abbrev ray16682 := rays 9
def bank16682 : Fin 1 → Cell := oneBank p16682 ray16682
theorem signs16682 : ∀ j, Signs p16682 (bank16682 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16683 := params 10
abbrev ray16683 := rays 10
def bank16683 : Fin 1 → Cell := oneBank p16683 ray16683
theorem signs16683 : ∀ j, Signs p16683 (bank16683 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16684 := params 11
abbrev ray16684 := rays 11
def bank16684 : Fin 1 → Cell := oneBank p16684 ray16684
theorem signs16684 : ∀ j, Signs p16684 (bank16684 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16685 := params 12
abbrev ray16685 := rays 12
def bank16685 : Fin 1 → Cell := oneBank p16685 ray16685
theorem signs16685 : ∀ j, Signs p16685 (bank16685 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16686 := params 13
abbrev ray16686 := rays 13
def bank16686 : Fin 1 → Cell := oneBank p16686 ray16686
theorem signs16686 : ∀ j, Signs p16686 (bank16686 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16687 := params 14
abbrev ray16687 := rays 14
def bank16687 : Fin 1 → Cell := oneBank p16687 ray16687
theorem signs16687 : ∀ j, Signs p16687 (bank16687 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16688 := params 15
abbrev ray16688 := rays 15
def bank16688 : Fin 1 → Cell := oneBank p16688 ray16688
theorem signs16688 : ∀ j, Signs p16688 (bank16688 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16689 := params 16
abbrev ray16689 := rays 16
def bank16689 : Fin 1 → Cell := oneBank p16689 ray16689
theorem signs16689 : ∀ j, Signs p16689 (bank16689 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16690 := params 17
abbrev ray16690 := rays 17
def bank16690 : Fin 1 → Cell := oneBank p16690 ray16690
theorem signs16690 : ∀ j, Signs p16690 (bank16690 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16691 := params 18
abbrev ray16691 := rays 18
def bank16691 : Fin 1 → Cell := oneBank p16691 ray16691
theorem signs16691 : ∀ j, Signs p16691 (bank16691 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16692 := params 19
abbrev ray16692 := rays 19
def bank16692 : Fin 1 → Cell := oneBank p16692 ray16692
theorem signs16692 : ∀ j, Signs p16692 (bank16692 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16693 := params 20
abbrev ray16693 := rays 20
def bank16693 : Fin 1 → Cell := oneBank p16693 ray16693
theorem signs16693 : ∀ j, Signs p16693 (bank16693 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16694 := params 21
abbrev ray16694 := rays 21
def bank16694 : Fin 1 → Cell := oneBank p16694 ray16694
theorem signs16694 : ∀ j, Signs p16694 (bank16694 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16695 := params 22
abbrev ray16695 := rays 22
def bank16695 : Fin 1 → Cell := oneBank p16695 ray16695
theorem signs16695 : ∀ j, Signs p16695 (bank16695 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16696 := params 23
abbrev ray16696 := rays 23
def bank16696 : Fin 1 → Cell := oneBank p16696 ray16696
theorem signs16696 : ∀ j, Signs p16696 (bank16696 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16697 := params 24
abbrev ray16697 := rays 24
def bank16697 : Fin 1 → Cell := oneBank p16697 ray16697
theorem signs16697 : ∀ j, Signs p16697 (bank16697 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16698 := params 25
abbrev ray16698 := rays 25
def bank16698 : Fin 1 → Cell := oneBank p16698 ray16698
theorem signs16698 : ∀ j, Signs p16698 (bank16698 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16699 := params 26
abbrev ray16699 := rays 26
def bank16699 : Fin 1 → Cell := oneBank p16699 ray16699
theorem signs16699 : ∀ j, Signs p16699 (bank16699 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16700 := params 27
abbrev ray16700 := rays 27
def bank16700 : Fin 1 → Cell := oneBank p16700 ray16700
theorem signs16700 : ∀ j, Signs p16700 (bank16700 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16701 := params 28
abbrev ray16701 := rays 28
def bank16701 : Fin 1 → Cell := oneBank p16701 ray16701
theorem signs16701 : ∀ j, Signs p16701 (bank16701 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16702 := params 29
abbrev ray16702 := rays 29
def bank16702 : Fin 1 → Cell := oneBank p16702 ray16702
theorem signs16702 : ∀ j, Signs p16702 (bank16702 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16703 := params 30
abbrev ray16703 := rays 30
def bank16703 : Fin 1 → Cell := oneBank p16703 ray16703
theorem signs16703 : ∀ j, Signs p16703 (bank16703 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16704 := params 31
abbrev ray16704 := rays 31
def bank16704 : Fin 1 → Cell := oneBank p16704 ray16704
theorem signs16704 : ∀ j, Signs p16704 (bank16704 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16673_16704
