/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14657_14688
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95554702343380,95554250523561,95553798687633,95553346835597,95552894967453,95552443083201,95551991182841,95551539266374,95551087333799,95550635385117,95550183420328,95549731439432,95549279442429,95548827429319,95548375400102,95547923354779,95547471293350,95547019215814,95546567122172,95546115012424,95545662886570,95545210744611,95544758586546,95544306412376,95543854222100,95543402015719,95542949793233,95542497554642,95542045299946,95541593029146,95541140742241,95540688439232,95540236120119]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14656+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14657 := params 0
abbrev ray14657 := rays 0
def bank14657 : Fin 1 → Cell := oneBank p14657 ray14657
theorem signs14657 : ∀ j, Signs p14657 (bank14657 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14658 := params 1
abbrev ray14658 := rays 1
def bank14658 : Fin 1 → Cell := oneBank p14658 ray14658
theorem signs14658 : ∀ j, Signs p14658 (bank14658 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14659 := params 2
abbrev ray14659 := rays 2
def bank14659 : Fin 1 → Cell := oneBank p14659 ray14659
theorem signs14659 : ∀ j, Signs p14659 (bank14659 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14660 := params 3
abbrev ray14660 := rays 3
def bank14660 : Fin 1 → Cell := oneBank p14660 ray14660
theorem signs14660 : ∀ j, Signs p14660 (bank14660 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14661 := params 4
abbrev ray14661 := rays 4
def bank14661 : Fin 1 → Cell := oneBank p14661 ray14661
theorem signs14661 : ∀ j, Signs p14661 (bank14661 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14662 := params 5
abbrev ray14662 := rays 5
def bank14662 : Fin 1 → Cell := oneBank p14662 ray14662
theorem signs14662 : ∀ j, Signs p14662 (bank14662 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14663 := params 6
abbrev ray14663 := rays 6
def bank14663 : Fin 1 → Cell := oneBank p14663 ray14663
theorem signs14663 : ∀ j, Signs p14663 (bank14663 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14664 := params 7
abbrev ray14664 := rays 7
def bank14664 : Fin 1 → Cell := oneBank p14664 ray14664
theorem signs14664 : ∀ j, Signs p14664 (bank14664 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14665 := params 8
abbrev ray14665 := rays 8
def bank14665 : Fin 1 → Cell := oneBank p14665 ray14665
theorem signs14665 : ∀ j, Signs p14665 (bank14665 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14666 := params 9
abbrev ray14666 := rays 9
def bank14666 : Fin 1 → Cell := oneBank p14666 ray14666
theorem signs14666 : ∀ j, Signs p14666 (bank14666 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14667 := params 10
abbrev ray14667 := rays 10
def bank14667 : Fin 1 → Cell := oneBank p14667 ray14667
theorem signs14667 : ∀ j, Signs p14667 (bank14667 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14668 := params 11
abbrev ray14668 := rays 11
def bank14668 : Fin 1 → Cell := oneBank p14668 ray14668
theorem signs14668 : ∀ j, Signs p14668 (bank14668 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14669 := params 12
abbrev ray14669 := rays 12
def bank14669 : Fin 1 → Cell := oneBank p14669 ray14669
theorem signs14669 : ∀ j, Signs p14669 (bank14669 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14670 := params 13
abbrev ray14670 := rays 13
def bank14670 : Fin 1 → Cell := oneBank p14670 ray14670
theorem signs14670 : ∀ j, Signs p14670 (bank14670 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14671 := params 14
abbrev ray14671 := rays 14
def bank14671 : Fin 1 → Cell := oneBank p14671 ray14671
theorem signs14671 : ∀ j, Signs p14671 (bank14671 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14672 := params 15
abbrev ray14672 := rays 15
def bank14672 : Fin 1 → Cell := oneBank p14672 ray14672
theorem signs14672 : ∀ j, Signs p14672 (bank14672 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14673 := params 16
abbrev ray14673 := rays 16
def bank14673 : Fin 1 → Cell := oneBank p14673 ray14673
theorem signs14673 : ∀ j, Signs p14673 (bank14673 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14674 := params 17
abbrev ray14674 := rays 17
def bank14674 : Fin 1 → Cell := oneBank p14674 ray14674
theorem signs14674 : ∀ j, Signs p14674 (bank14674 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14675 := params 18
abbrev ray14675 := rays 18
def bank14675 : Fin 1 → Cell := oneBank p14675 ray14675
theorem signs14675 : ∀ j, Signs p14675 (bank14675 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14676 := params 19
abbrev ray14676 := rays 19
def bank14676 : Fin 1 → Cell := oneBank p14676 ray14676
theorem signs14676 : ∀ j, Signs p14676 (bank14676 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14677 := params 20
abbrev ray14677 := rays 20
def bank14677 : Fin 1 → Cell := oneBank p14677 ray14677
theorem signs14677 : ∀ j, Signs p14677 (bank14677 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14678 := params 21
abbrev ray14678 := rays 21
def bank14678 : Fin 1 → Cell := oneBank p14678 ray14678
theorem signs14678 : ∀ j, Signs p14678 (bank14678 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14679 := params 22
abbrev ray14679 := rays 22
def bank14679 : Fin 1 → Cell := oneBank p14679 ray14679
theorem signs14679 : ∀ j, Signs p14679 (bank14679 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14680 := params 23
abbrev ray14680 := rays 23
def bank14680 : Fin 1 → Cell := oneBank p14680 ray14680
theorem signs14680 : ∀ j, Signs p14680 (bank14680 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14681 := params 24
abbrev ray14681 := rays 24
def bank14681 : Fin 1 → Cell := oneBank p14681 ray14681
theorem signs14681 : ∀ j, Signs p14681 (bank14681 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14682 := params 25
abbrev ray14682 := rays 25
def bank14682 : Fin 1 → Cell := oneBank p14682 ray14682
theorem signs14682 : ∀ j, Signs p14682 (bank14682 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14683 := params 26
abbrev ray14683 := rays 26
def bank14683 : Fin 1 → Cell := oneBank p14683 ray14683
theorem signs14683 : ∀ j, Signs p14683 (bank14683 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14684 := params 27
abbrev ray14684 := rays 27
def bank14684 : Fin 1 → Cell := oneBank p14684 ray14684
theorem signs14684 : ∀ j, Signs p14684 (bank14684 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14685 := params 28
abbrev ray14685 := rays 28
def bank14685 : Fin 1 → Cell := oneBank p14685 ray14685
theorem signs14685 : ∀ j, Signs p14685 (bank14685 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14686 := params 29
abbrev ray14686 := rays 29
def bank14686 : Fin 1 → Cell := oneBank p14686 ray14686
theorem signs14686 : ∀ j, Signs p14686 (bank14686 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14687 := params 30
abbrev ray14687 := rays 30
def bank14687 : Fin 1 → Cell := oneBank p14687 ray14687
theorem signs14687 : ∀ j, Signs p14687 (bank14687 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14688 := params 31
abbrev ray14688 := rays 31
def bank14688 : Fin 1 → Cell := oneBank p14688 ray14688
theorem signs14688 : ∀ j, Signs p14688 (bank14688 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14657_14688
