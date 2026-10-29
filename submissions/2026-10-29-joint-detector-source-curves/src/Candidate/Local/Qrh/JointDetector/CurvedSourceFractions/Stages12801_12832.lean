/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12801_12832
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96365338123661,96364916515480,96364494890808,96364073249646,96363651591994,96363229917852,96362808227220,96362386520099,96361964796489,96361543056390,96361121299803,96360699526728,96360277737165,96359855931115,96359434108577,96359012269552,96358590414041,96358168542043,96357746653559,96357324748589,96356902827133,96356480889192,96356058934766,96355636963855,96355214976460,96354792972580,96354370952216,96353948915369,96353526862038,96353104792224,96352682705927,96352260603148,96351838483886]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12800+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12801 := params 0
abbrev ray12801 := rays 0
def bank12801 : Fin 1 → Cell := oneBank p12801 ray12801
theorem signs12801 : ∀ j, Signs p12801 (bank12801 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12802 := params 1
abbrev ray12802 := rays 1
def bank12802 : Fin 1 → Cell := oneBank p12802 ray12802
theorem signs12802 : ∀ j, Signs p12802 (bank12802 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12803 := params 2
abbrev ray12803 := rays 2
def bank12803 : Fin 1 → Cell := oneBank p12803 ray12803
theorem signs12803 : ∀ j, Signs p12803 (bank12803 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12804 := params 3
abbrev ray12804 := rays 3
def bank12804 : Fin 1 → Cell := oneBank p12804 ray12804
theorem signs12804 : ∀ j, Signs p12804 (bank12804 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12805 := params 4
abbrev ray12805 := rays 4
def bank12805 : Fin 1 → Cell := oneBank p12805 ray12805
theorem signs12805 : ∀ j, Signs p12805 (bank12805 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12806 := params 5
abbrev ray12806 := rays 5
def bank12806 : Fin 1 → Cell := oneBank p12806 ray12806
theorem signs12806 : ∀ j, Signs p12806 (bank12806 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12807 := params 6
abbrev ray12807 := rays 6
def bank12807 : Fin 1 → Cell := oneBank p12807 ray12807
theorem signs12807 : ∀ j, Signs p12807 (bank12807 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12808 := params 7
abbrev ray12808 := rays 7
def bank12808 : Fin 1 → Cell := oneBank p12808 ray12808
theorem signs12808 : ∀ j, Signs p12808 (bank12808 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12809 := params 8
abbrev ray12809 := rays 8
def bank12809 : Fin 1 → Cell := oneBank p12809 ray12809
theorem signs12809 : ∀ j, Signs p12809 (bank12809 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12810 := params 9
abbrev ray12810 := rays 9
def bank12810 : Fin 1 → Cell := oneBank p12810 ray12810
theorem signs12810 : ∀ j, Signs p12810 (bank12810 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12811 := params 10
abbrev ray12811 := rays 10
def bank12811 : Fin 1 → Cell := oneBank p12811 ray12811
theorem signs12811 : ∀ j, Signs p12811 (bank12811 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12812 := params 11
abbrev ray12812 := rays 11
def bank12812 : Fin 1 → Cell := oneBank p12812 ray12812
theorem signs12812 : ∀ j, Signs p12812 (bank12812 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12813 := params 12
abbrev ray12813 := rays 12
def bank12813 : Fin 1 → Cell := oneBank p12813 ray12813
theorem signs12813 : ∀ j, Signs p12813 (bank12813 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12814 := params 13
abbrev ray12814 := rays 13
def bank12814 : Fin 1 → Cell := oneBank p12814 ray12814
theorem signs12814 : ∀ j, Signs p12814 (bank12814 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12815 := params 14
abbrev ray12815 := rays 14
def bank12815 : Fin 1 → Cell := oneBank p12815 ray12815
theorem signs12815 : ∀ j, Signs p12815 (bank12815 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12816 := params 15
abbrev ray12816 := rays 15
def bank12816 : Fin 1 → Cell := oneBank p12816 ray12816
theorem signs12816 : ∀ j, Signs p12816 (bank12816 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12817 := params 16
abbrev ray12817 := rays 16
def bank12817 : Fin 1 → Cell := oneBank p12817 ray12817
theorem signs12817 : ∀ j, Signs p12817 (bank12817 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12818 := params 17
abbrev ray12818 := rays 17
def bank12818 : Fin 1 → Cell := oneBank p12818 ray12818
theorem signs12818 : ∀ j, Signs p12818 (bank12818 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12819 := params 18
abbrev ray12819 := rays 18
def bank12819 : Fin 1 → Cell := oneBank p12819 ray12819
theorem signs12819 : ∀ j, Signs p12819 (bank12819 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12820 := params 19
abbrev ray12820 := rays 19
def bank12820 : Fin 1 → Cell := oneBank p12820 ray12820
theorem signs12820 : ∀ j, Signs p12820 (bank12820 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12821 := params 20
abbrev ray12821 := rays 20
def bank12821 : Fin 1 → Cell := oneBank p12821 ray12821
theorem signs12821 : ∀ j, Signs p12821 (bank12821 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12822 := params 21
abbrev ray12822 := rays 21
def bank12822 : Fin 1 → Cell := oneBank p12822 ray12822
theorem signs12822 : ∀ j, Signs p12822 (bank12822 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12823 := params 22
abbrev ray12823 := rays 22
def bank12823 : Fin 1 → Cell := oneBank p12823 ray12823
theorem signs12823 : ∀ j, Signs p12823 (bank12823 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12824 := params 23
abbrev ray12824 := rays 23
def bank12824 : Fin 1 → Cell := oneBank p12824 ray12824
theorem signs12824 : ∀ j, Signs p12824 (bank12824 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12825 := params 24
abbrev ray12825 := rays 24
def bank12825 : Fin 1 → Cell := oneBank p12825 ray12825
theorem signs12825 : ∀ j, Signs p12825 (bank12825 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12826 := params 25
abbrev ray12826 := rays 25
def bank12826 : Fin 1 → Cell := oneBank p12826 ray12826
theorem signs12826 : ∀ j, Signs p12826 (bank12826 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12827 := params 26
abbrev ray12827 := rays 26
def bank12827 : Fin 1 → Cell := oneBank p12827 ray12827
theorem signs12827 : ∀ j, Signs p12827 (bank12827 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12828 := params 27
abbrev ray12828 := rays 27
def bank12828 : Fin 1 → Cell := oneBank p12828 ray12828
theorem signs12828 : ∀ j, Signs p12828 (bank12828 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12829 := params 28
abbrev ray12829 := rays 28
def bank12829 : Fin 1 → Cell := oneBank p12829 ray12829
theorem signs12829 : ∀ j, Signs p12829 (bank12829 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12830 := params 29
abbrev ray12830 := rays 29
def bank12830 : Fin 1 → Cell := oneBank p12830 ray12830
theorem signs12830 : ∀ j, Signs p12830 (bank12830 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12831 := params 30
abbrev ray12831 := rays 30
def bank12831 : Fin 1 → Cell := oneBank p12831 ray12831
theorem signs12831 : ∀ j, Signs p12831 (bank12831 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12832 := params 31
abbrev ray12832 := rays 31
def bank12832 : Fin 1 → Cell := oneBank p12832 ray12832
theorem signs12832 : ∀ j, Signs p12832 (bank12832 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12801_12832
