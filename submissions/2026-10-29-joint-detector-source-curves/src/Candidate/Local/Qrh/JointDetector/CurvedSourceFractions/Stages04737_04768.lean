/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04737_04768
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99102068760118,99101818707410,99101568630333,99101318528887,99101068403073,99100818252893,99100568078348,99100317879438,99100067656165,99099817408529,99099567136532,99099316840175,99099066519458,99098816174383,99098565804951,99098315411163,99098064993020,99097814550522,99097564083671,99097313592468,99097063076914,99096812537010,99096561972757,99096311384156,99096060771208,99095810133914,99095559472275,99095308786292,99095058075966,99094807341299,99094556582291,99094305798943,99094054991256]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4736+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4737 := params 0
abbrev ray4737 := rays 0
def bank4737 : Fin 2 → Cell := twoBank p4737 ray4737
theorem signs4737 : ∀ j, Signs p4737 (bank4737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4738 := params 1
abbrev ray4738 := rays 1
def bank4738 : Fin 2 → Cell := twoBank p4738 ray4738
theorem signs4738 : ∀ j, Signs p4738 (bank4738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4739 := params 2
abbrev ray4739 := rays 2
def bank4739 : Fin 2 → Cell := twoBank p4739 ray4739
theorem signs4739 : ∀ j, Signs p4739 (bank4739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4740 := params 3
abbrev ray4740 := rays 3
def bank4740 : Fin 2 → Cell := twoBank p4740 ray4740
theorem signs4740 : ∀ j, Signs p4740 (bank4740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4741 := params 4
abbrev ray4741 := rays 4
def bank4741 : Fin 2 → Cell := twoBank p4741 ray4741
theorem signs4741 : ∀ j, Signs p4741 (bank4741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4742 := params 5
abbrev ray4742 := rays 5
def bank4742 : Fin 2 → Cell := twoBank p4742 ray4742
theorem signs4742 : ∀ j, Signs p4742 (bank4742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4743 := params 6
abbrev ray4743 := rays 6
def bank4743 : Fin 2 → Cell := twoBank p4743 ray4743
theorem signs4743 : ∀ j, Signs p4743 (bank4743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4744 := params 7
abbrev ray4744 := rays 7
def bank4744 : Fin 2 → Cell := twoBank p4744 ray4744
theorem signs4744 : ∀ j, Signs p4744 (bank4744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4745 := params 8
abbrev ray4745 := rays 8
def bank4745 : Fin 2 → Cell := twoBank p4745 ray4745
theorem signs4745 : ∀ j, Signs p4745 (bank4745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4746 := params 9
abbrev ray4746 := rays 9
def bank4746 : Fin 2 → Cell := twoBank p4746 ray4746
theorem signs4746 : ∀ j, Signs p4746 (bank4746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4747 := params 10
abbrev ray4747 := rays 10
def bank4747 : Fin 2 → Cell := twoBank p4747 ray4747
theorem signs4747 : ∀ j, Signs p4747 (bank4747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4748 := params 11
abbrev ray4748 := rays 11
def bank4748 : Fin 2 → Cell := twoBank p4748 ray4748
theorem signs4748 : ∀ j, Signs p4748 (bank4748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4749 := params 12
abbrev ray4749 := rays 12
def bank4749 : Fin 2 → Cell := twoBank p4749 ray4749
theorem signs4749 : ∀ j, Signs p4749 (bank4749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4750 := params 13
abbrev ray4750 := rays 13
def bank4750 : Fin 2 → Cell := twoBank p4750 ray4750
theorem signs4750 : ∀ j, Signs p4750 (bank4750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4751 := params 14
abbrev ray4751 := rays 14
def bank4751 : Fin 2 → Cell := twoBank p4751 ray4751
theorem signs4751 : ∀ j, Signs p4751 (bank4751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4752 := params 15
abbrev ray4752 := rays 15
def bank4752 : Fin 2 → Cell := twoBank p4752 ray4752
theorem signs4752 : ∀ j, Signs p4752 (bank4752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4753 := params 16
abbrev ray4753 := rays 16
def bank4753 : Fin 2 → Cell := twoBank p4753 ray4753
theorem signs4753 : ∀ j, Signs p4753 (bank4753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4754 := params 17
abbrev ray4754 := rays 17
def bank4754 : Fin 2 → Cell := twoBank p4754 ray4754
theorem signs4754 : ∀ j, Signs p4754 (bank4754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4755 := params 18
abbrev ray4755 := rays 18
def bank4755 : Fin 2 → Cell := twoBank p4755 ray4755
theorem signs4755 : ∀ j, Signs p4755 (bank4755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4756 := params 19
abbrev ray4756 := rays 19
def bank4756 : Fin 2 → Cell := twoBank p4756 ray4756
theorem signs4756 : ∀ j, Signs p4756 (bank4756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4757 := params 20
abbrev ray4757 := rays 20
def bank4757 : Fin 2 → Cell := twoBank p4757 ray4757
theorem signs4757 : ∀ j, Signs p4757 (bank4757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4758 := params 21
abbrev ray4758 := rays 21
def bank4758 : Fin 2 → Cell := twoBank p4758 ray4758
theorem signs4758 : ∀ j, Signs p4758 (bank4758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4759 := params 22
abbrev ray4759 := rays 22
def bank4759 : Fin 2 → Cell := twoBank p4759 ray4759
theorem signs4759 : ∀ j, Signs p4759 (bank4759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4760 := params 23
abbrev ray4760 := rays 23
def bank4760 : Fin 2 → Cell := twoBank p4760 ray4760
theorem signs4760 : ∀ j, Signs p4760 (bank4760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4761 := params 24
abbrev ray4761 := rays 24
def bank4761 : Fin 2 → Cell := twoBank p4761 ray4761
theorem signs4761 : ∀ j, Signs p4761 (bank4761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4762 := params 25
abbrev ray4762 := rays 25
def bank4762 : Fin 2 → Cell := twoBank p4762 ray4762
theorem signs4762 : ∀ j, Signs p4762 (bank4762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4763 := params 26
abbrev ray4763 := rays 26
def bank4763 : Fin 2 → Cell := twoBank p4763 ray4763
theorem signs4763 : ∀ j, Signs p4763 (bank4763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4764 := params 27
abbrev ray4764 := rays 27
def bank4764 : Fin 2 → Cell := twoBank p4764 ray4764
theorem signs4764 : ∀ j, Signs p4764 (bank4764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4765 := params 28
abbrev ray4765 := rays 28
def bank4765 : Fin 2 → Cell := twoBank p4765 ray4765
theorem signs4765 : ∀ j, Signs p4765 (bank4765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4766 := params 29
abbrev ray4766 := rays 29
def bank4766 : Fin 2 → Cell := twoBank p4766 ray4766
theorem signs4766 : ∀ j, Signs p4766 (bank4766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4767 := params 30
abbrev ray4767 := rays 30
def bank4767 : Fin 2 → Cell := twoBank p4767 ray4767
theorem signs4767 : ∀ j, Signs p4767 (bank4767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4768 := params 31
abbrev ray4768 := rays 31
def bank4768 : Fin 2 → Cell := twoBank p4768 ray4768
theorem signs4768 : ∀ j, Signs p4768 (bank4768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04737_04768
