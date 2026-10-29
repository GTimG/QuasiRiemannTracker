/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14785_14816
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95496738524092,95496284643495,95495830746806,95495376834026,95494922905155,95494468960193,95494014999140,95493561021996,95493107028761,95492653019436,95492198994020,95491744952514,95491290894918,95490836821232,95490382731456,95489928625590,95489474503634,95489020365589,95488566211454,95488112041230,95487657854917,95487203652515,95486749434024,95486295199444,95485840948775,95485386682018,95484932399172,95484478100238,95484023785216,95483569454106,95483115106908,95482660743622,95482206364249]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14784+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14785 := params 0
abbrev ray14785 := rays 0
def bank14785 : Fin 1 → Cell := oneBank p14785 ray14785
theorem signs14785 : ∀ j, Signs p14785 (bank14785 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14786 := params 1
abbrev ray14786 := rays 1
def bank14786 : Fin 1 → Cell := oneBank p14786 ray14786
theorem signs14786 : ∀ j, Signs p14786 (bank14786 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14787 := params 2
abbrev ray14787 := rays 2
def bank14787 : Fin 1 → Cell := oneBank p14787 ray14787
theorem signs14787 : ∀ j, Signs p14787 (bank14787 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14788 := params 3
abbrev ray14788 := rays 3
def bank14788 : Fin 1 → Cell := oneBank p14788 ray14788
theorem signs14788 : ∀ j, Signs p14788 (bank14788 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14789 := params 4
abbrev ray14789 := rays 4
def bank14789 : Fin 1 → Cell := oneBank p14789 ray14789
theorem signs14789 : ∀ j, Signs p14789 (bank14789 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14790 := params 5
abbrev ray14790 := rays 5
def bank14790 : Fin 1 → Cell := oneBank p14790 ray14790
theorem signs14790 : ∀ j, Signs p14790 (bank14790 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14791 := params 6
abbrev ray14791 := rays 6
def bank14791 : Fin 1 → Cell := oneBank p14791 ray14791
theorem signs14791 : ∀ j, Signs p14791 (bank14791 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14792 := params 7
abbrev ray14792 := rays 7
def bank14792 : Fin 1 → Cell := oneBank p14792 ray14792
theorem signs14792 : ∀ j, Signs p14792 (bank14792 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14793 := params 8
abbrev ray14793 := rays 8
def bank14793 : Fin 1 → Cell := oneBank p14793 ray14793
theorem signs14793 : ∀ j, Signs p14793 (bank14793 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14794 := params 9
abbrev ray14794 := rays 9
def bank14794 : Fin 1 → Cell := oneBank p14794 ray14794
theorem signs14794 : ∀ j, Signs p14794 (bank14794 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14795 := params 10
abbrev ray14795 := rays 10
def bank14795 : Fin 1 → Cell := oneBank p14795 ray14795
theorem signs14795 : ∀ j, Signs p14795 (bank14795 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14796 := params 11
abbrev ray14796 := rays 11
def bank14796 : Fin 1 → Cell := oneBank p14796 ray14796
theorem signs14796 : ∀ j, Signs p14796 (bank14796 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14797 := params 12
abbrev ray14797 := rays 12
def bank14797 : Fin 1 → Cell := oneBank p14797 ray14797
theorem signs14797 : ∀ j, Signs p14797 (bank14797 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14798 := params 13
abbrev ray14798 := rays 13
def bank14798 : Fin 1 → Cell := oneBank p14798 ray14798
theorem signs14798 : ∀ j, Signs p14798 (bank14798 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14799 := params 14
abbrev ray14799 := rays 14
def bank14799 : Fin 1 → Cell := oneBank p14799 ray14799
theorem signs14799 : ∀ j, Signs p14799 (bank14799 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14800 := params 15
abbrev ray14800 := rays 15
def bank14800 : Fin 1 → Cell := oneBank p14800 ray14800
theorem signs14800 : ∀ j, Signs p14800 (bank14800 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14801 := params 16
abbrev ray14801 := rays 16
def bank14801 : Fin 1 → Cell := oneBank p14801 ray14801
theorem signs14801 : ∀ j, Signs p14801 (bank14801 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14802 := params 17
abbrev ray14802 := rays 17
def bank14802 : Fin 1 → Cell := oneBank p14802 ray14802
theorem signs14802 : ∀ j, Signs p14802 (bank14802 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14803 := params 18
abbrev ray14803 := rays 18
def bank14803 : Fin 1 → Cell := oneBank p14803 ray14803
theorem signs14803 : ∀ j, Signs p14803 (bank14803 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14804 := params 19
abbrev ray14804 := rays 19
def bank14804 : Fin 1 → Cell := oneBank p14804 ray14804
theorem signs14804 : ∀ j, Signs p14804 (bank14804 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14805 := params 20
abbrev ray14805 := rays 20
def bank14805 : Fin 1 → Cell := oneBank p14805 ray14805
theorem signs14805 : ∀ j, Signs p14805 (bank14805 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14806 := params 21
abbrev ray14806 := rays 21
def bank14806 : Fin 1 → Cell := oneBank p14806 ray14806
theorem signs14806 : ∀ j, Signs p14806 (bank14806 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14807 := params 22
abbrev ray14807 := rays 22
def bank14807 : Fin 1 → Cell := oneBank p14807 ray14807
theorem signs14807 : ∀ j, Signs p14807 (bank14807 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14808 := params 23
abbrev ray14808 := rays 23
def bank14808 : Fin 1 → Cell := oneBank p14808 ray14808
theorem signs14808 : ∀ j, Signs p14808 (bank14808 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14809 := params 24
abbrev ray14809 := rays 24
def bank14809 : Fin 1 → Cell := oneBank p14809 ray14809
theorem signs14809 : ∀ j, Signs p14809 (bank14809 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14810 := params 25
abbrev ray14810 := rays 25
def bank14810 : Fin 1 → Cell := oneBank p14810 ray14810
theorem signs14810 : ∀ j, Signs p14810 (bank14810 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14811 := params 26
abbrev ray14811 := rays 26
def bank14811 : Fin 1 → Cell := oneBank p14811 ray14811
theorem signs14811 : ∀ j, Signs p14811 (bank14811 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14812 := params 27
abbrev ray14812 := rays 27
def bank14812 : Fin 1 → Cell := oneBank p14812 ray14812
theorem signs14812 : ∀ j, Signs p14812 (bank14812 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14813 := params 28
abbrev ray14813 := rays 28
def bank14813 : Fin 1 → Cell := oneBank p14813 ray14813
theorem signs14813 : ∀ j, Signs p14813 (bank14813 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14814 := params 29
abbrev ray14814 := rays 29
def bank14814 : Fin 1 → Cell := oneBank p14814 ray14814
theorem signs14814 : ∀ j, Signs p14814 (bank14814 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14815 := params 30
abbrev ray14815 := rays 30
def bank14815 : Fin 1 → Cell := oneBank p14815 ray14815
theorem signs14815 : ∀ j, Signs p14815 (bank14815 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14816 := params 31
abbrev ray14816 := rays 31
def bank14816 : Fin 1 → Cell := oneBank p14816 ray14816
theorem signs14816 : ∀ j, Signs p14816 (bank14816 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14785_14816
