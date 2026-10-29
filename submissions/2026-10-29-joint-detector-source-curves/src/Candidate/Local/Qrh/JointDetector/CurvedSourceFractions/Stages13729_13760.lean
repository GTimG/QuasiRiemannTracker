/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13729_13760
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95967027040871,95966590238225,95966153419312,95965716584132,95965279732686,95964842864974,95964405980996,95963969080752,95963532164242,95963095231467,95962658282427,95962221317122,95961784335552,95961347337717,95960910323618,95960473293255,95960036246628,95959599183737,95959162104582,95958725009164,95958287897483,95957850769539,95957413625332,95956976464862,95956539288130,95956102095136,95955664885880,95955227660362,95954790418582,95954353160541,95953915886239,95953478595676,95953041288852]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13728+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13729 := params 0
abbrev ray13729 := rays 0
def bank13729 : Fin 1 → Cell := oneBank p13729 ray13729
theorem signs13729 : ∀ j, Signs p13729 (bank13729 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13730 := params 1
abbrev ray13730 := rays 1
def bank13730 : Fin 1 → Cell := oneBank p13730 ray13730
theorem signs13730 : ∀ j, Signs p13730 (bank13730 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13731 := params 2
abbrev ray13731 := rays 2
def bank13731 : Fin 1 → Cell := oneBank p13731 ray13731
theorem signs13731 : ∀ j, Signs p13731 (bank13731 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13732 := params 3
abbrev ray13732 := rays 3
def bank13732 : Fin 1 → Cell := oneBank p13732 ray13732
theorem signs13732 : ∀ j, Signs p13732 (bank13732 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13733 := params 4
abbrev ray13733 := rays 4
def bank13733 : Fin 1 → Cell := oneBank p13733 ray13733
theorem signs13733 : ∀ j, Signs p13733 (bank13733 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13734 := params 5
abbrev ray13734 := rays 5
def bank13734 : Fin 1 → Cell := oneBank p13734 ray13734
theorem signs13734 : ∀ j, Signs p13734 (bank13734 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13735 := params 6
abbrev ray13735 := rays 6
def bank13735 : Fin 1 → Cell := oneBank p13735 ray13735
theorem signs13735 : ∀ j, Signs p13735 (bank13735 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13736 := params 7
abbrev ray13736 := rays 7
def bank13736 : Fin 1 → Cell := oneBank p13736 ray13736
theorem signs13736 : ∀ j, Signs p13736 (bank13736 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13737 := params 8
abbrev ray13737 := rays 8
def bank13737 : Fin 1 → Cell := oneBank p13737 ray13737
theorem signs13737 : ∀ j, Signs p13737 (bank13737 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13738 := params 9
abbrev ray13738 := rays 9
def bank13738 : Fin 1 → Cell := oneBank p13738 ray13738
theorem signs13738 : ∀ j, Signs p13738 (bank13738 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13739 := params 10
abbrev ray13739 := rays 10
def bank13739 : Fin 1 → Cell := oneBank p13739 ray13739
theorem signs13739 : ∀ j, Signs p13739 (bank13739 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13740 := params 11
abbrev ray13740 := rays 11
def bank13740 : Fin 1 → Cell := oneBank p13740 ray13740
theorem signs13740 : ∀ j, Signs p13740 (bank13740 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13741 := params 12
abbrev ray13741 := rays 12
def bank13741 : Fin 1 → Cell := oneBank p13741 ray13741
theorem signs13741 : ∀ j, Signs p13741 (bank13741 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13742 := params 13
abbrev ray13742 := rays 13
def bank13742 : Fin 1 → Cell := oneBank p13742 ray13742
theorem signs13742 : ∀ j, Signs p13742 (bank13742 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13743 := params 14
abbrev ray13743 := rays 14
def bank13743 : Fin 1 → Cell := oneBank p13743 ray13743
theorem signs13743 : ∀ j, Signs p13743 (bank13743 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13744 := params 15
abbrev ray13744 := rays 15
def bank13744 : Fin 1 → Cell := oneBank p13744 ray13744
theorem signs13744 : ∀ j, Signs p13744 (bank13744 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13745 := params 16
abbrev ray13745 := rays 16
def bank13745 : Fin 1 → Cell := oneBank p13745 ray13745
theorem signs13745 : ∀ j, Signs p13745 (bank13745 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13746 := params 17
abbrev ray13746 := rays 17
def bank13746 : Fin 1 → Cell := oneBank p13746 ray13746
theorem signs13746 : ∀ j, Signs p13746 (bank13746 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13747 := params 18
abbrev ray13747 := rays 18
def bank13747 : Fin 1 → Cell := oneBank p13747 ray13747
theorem signs13747 : ∀ j, Signs p13747 (bank13747 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13748 := params 19
abbrev ray13748 := rays 19
def bank13748 : Fin 1 → Cell := oneBank p13748 ray13748
theorem signs13748 : ∀ j, Signs p13748 (bank13748 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13749 := params 20
abbrev ray13749 := rays 20
def bank13749 : Fin 1 → Cell := oneBank p13749 ray13749
theorem signs13749 : ∀ j, Signs p13749 (bank13749 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13750 := params 21
abbrev ray13750 := rays 21
def bank13750 : Fin 1 → Cell := oneBank p13750 ray13750
theorem signs13750 : ∀ j, Signs p13750 (bank13750 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13751 := params 22
abbrev ray13751 := rays 22
def bank13751 : Fin 1 → Cell := oneBank p13751 ray13751
theorem signs13751 : ∀ j, Signs p13751 (bank13751 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13752 := params 23
abbrev ray13752 := rays 23
def bank13752 : Fin 1 → Cell := oneBank p13752 ray13752
theorem signs13752 : ∀ j, Signs p13752 (bank13752 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13753 := params 24
abbrev ray13753 := rays 24
def bank13753 : Fin 1 → Cell := oneBank p13753 ray13753
theorem signs13753 : ∀ j, Signs p13753 (bank13753 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13754 := params 25
abbrev ray13754 := rays 25
def bank13754 : Fin 1 → Cell := oneBank p13754 ray13754
theorem signs13754 : ∀ j, Signs p13754 (bank13754 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13755 := params 26
abbrev ray13755 := rays 26
def bank13755 : Fin 1 → Cell := oneBank p13755 ray13755
theorem signs13755 : ∀ j, Signs p13755 (bank13755 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13756 := params 27
abbrev ray13756 := rays 27
def bank13756 : Fin 1 → Cell := oneBank p13756 ray13756
theorem signs13756 : ∀ j, Signs p13756 (bank13756 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13757 := params 28
abbrev ray13757 := rays 28
def bank13757 : Fin 1 → Cell := oneBank p13757 ray13757
theorem signs13757 : ∀ j, Signs p13757 (bank13757 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13758 := params 29
abbrev ray13758 := rays 29
def bank13758 : Fin 1 → Cell := oneBank p13758 ray13758
theorem signs13758 : ∀ j, Signs p13758 (bank13758 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13759 := params 30
abbrev ray13759 := rays 30
def bank13759 : Fin 1 → Cell := oneBank p13759 ray13759
theorem signs13759 : ∀ j, Signs p13759 (bank13759 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13760 := params 31
abbrev ray13760 := rays 31
def bank13760 : Fin 1 → Cell := oneBank p13760 ray13760
theorem signs13760 : ∀ j, Signs p13760 (bank13760 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13729_13760
