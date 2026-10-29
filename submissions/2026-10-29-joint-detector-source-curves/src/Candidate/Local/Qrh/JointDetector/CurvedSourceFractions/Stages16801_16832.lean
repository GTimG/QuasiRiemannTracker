/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16801_16832
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94549153490222,94548667325375,94548181144541,94547694947720,94547208734911,94546722506115,94546236261332,94545750000561,94545263723803,94544777431057,94544291122324,94543804797603,94543318456895,94542832100199,94542345727515,94541859338844,94541372934185,94540886513538,94540400076904,94539913624282,94539427155672,94538940671074,94538454170489,94537967653916,94537481121355,94536994572806,94536508008269,94536021427744,94535534831231,94535048218730,94534561590241,94534074945764,94533588285299]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16800+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16801 := params 0
abbrev ray16801 := rays 0
def bank16801 : Fin 1 → Cell := oneBank p16801 ray16801
theorem signs16801 : ∀ j, Signs p16801 (bank16801 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16802 := params 1
abbrev ray16802 := rays 1
def bank16802 : Fin 1 → Cell := oneBank p16802 ray16802
theorem signs16802 : ∀ j, Signs p16802 (bank16802 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16803 := params 2
abbrev ray16803 := rays 2
def bank16803 : Fin 1 → Cell := oneBank p16803 ray16803
theorem signs16803 : ∀ j, Signs p16803 (bank16803 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16804 := params 3
abbrev ray16804 := rays 3
def bank16804 : Fin 1 → Cell := oneBank p16804 ray16804
theorem signs16804 : ∀ j, Signs p16804 (bank16804 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16805 := params 4
abbrev ray16805 := rays 4
def bank16805 : Fin 1 → Cell := oneBank p16805 ray16805
theorem signs16805 : ∀ j, Signs p16805 (bank16805 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16806 := params 5
abbrev ray16806 := rays 5
def bank16806 : Fin 1 → Cell := oneBank p16806 ray16806
theorem signs16806 : ∀ j, Signs p16806 (bank16806 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16807 := params 6
abbrev ray16807 := rays 6
def bank16807 : Fin 1 → Cell := oneBank p16807 ray16807
theorem signs16807 : ∀ j, Signs p16807 (bank16807 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16808 := params 7
abbrev ray16808 := rays 7
def bank16808 : Fin 1 → Cell := oneBank p16808 ray16808
theorem signs16808 : ∀ j, Signs p16808 (bank16808 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16809 := params 8
abbrev ray16809 := rays 8
def bank16809 : Fin 1 → Cell := oneBank p16809 ray16809
theorem signs16809 : ∀ j, Signs p16809 (bank16809 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16810 := params 9
abbrev ray16810 := rays 9
def bank16810 : Fin 1 → Cell := oneBank p16810 ray16810
theorem signs16810 : ∀ j, Signs p16810 (bank16810 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16811 := params 10
abbrev ray16811 := rays 10
def bank16811 : Fin 1 → Cell := oneBank p16811 ray16811
theorem signs16811 : ∀ j, Signs p16811 (bank16811 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16812 := params 11
abbrev ray16812 := rays 11
def bank16812 : Fin 1 → Cell := oneBank p16812 ray16812
theorem signs16812 : ∀ j, Signs p16812 (bank16812 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16813 := params 12
abbrev ray16813 := rays 12
def bank16813 : Fin 1 → Cell := oneBank p16813 ray16813
theorem signs16813 : ∀ j, Signs p16813 (bank16813 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16814 := params 13
abbrev ray16814 := rays 13
def bank16814 : Fin 1 → Cell := oneBank p16814 ray16814
theorem signs16814 : ∀ j, Signs p16814 (bank16814 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16815 := params 14
abbrev ray16815 := rays 14
def bank16815 : Fin 1 → Cell := oneBank p16815 ray16815
theorem signs16815 : ∀ j, Signs p16815 (bank16815 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16816 := params 15
abbrev ray16816 := rays 15
def bank16816 : Fin 1 → Cell := oneBank p16816 ray16816
theorem signs16816 : ∀ j, Signs p16816 (bank16816 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16817 := params 16
abbrev ray16817 := rays 16
def bank16817 : Fin 1 → Cell := oneBank p16817 ray16817
theorem signs16817 : ∀ j, Signs p16817 (bank16817 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16818 := params 17
abbrev ray16818 := rays 17
def bank16818 : Fin 1 → Cell := oneBank p16818 ray16818
theorem signs16818 : ∀ j, Signs p16818 (bank16818 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16819 := params 18
abbrev ray16819 := rays 18
def bank16819 : Fin 1 → Cell := oneBank p16819 ray16819
theorem signs16819 : ∀ j, Signs p16819 (bank16819 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16820 := params 19
abbrev ray16820 := rays 19
def bank16820 : Fin 1 → Cell := oneBank p16820 ray16820
theorem signs16820 : ∀ j, Signs p16820 (bank16820 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16821 := params 20
abbrev ray16821 := rays 20
def bank16821 : Fin 1 → Cell := oneBank p16821 ray16821
theorem signs16821 : ∀ j, Signs p16821 (bank16821 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16822 := params 21
abbrev ray16822 := rays 21
def bank16822 : Fin 1 → Cell := oneBank p16822 ray16822
theorem signs16822 : ∀ j, Signs p16822 (bank16822 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16823 := params 22
abbrev ray16823 := rays 22
def bank16823 : Fin 1 → Cell := oneBank p16823 ray16823
theorem signs16823 : ∀ j, Signs p16823 (bank16823 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16824 := params 23
abbrev ray16824 := rays 23
def bank16824 : Fin 1 → Cell := oneBank p16824 ray16824
theorem signs16824 : ∀ j, Signs p16824 (bank16824 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16825 := params 24
abbrev ray16825 := rays 24
def bank16825 : Fin 1 → Cell := oneBank p16825 ray16825
theorem signs16825 : ∀ j, Signs p16825 (bank16825 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16826 := params 25
abbrev ray16826 := rays 25
def bank16826 : Fin 1 → Cell := oneBank p16826 ray16826
theorem signs16826 : ∀ j, Signs p16826 (bank16826 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16827 := params 26
abbrev ray16827 := rays 26
def bank16827 : Fin 1 → Cell := oneBank p16827 ray16827
theorem signs16827 : ∀ j, Signs p16827 (bank16827 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16828 := params 27
abbrev ray16828 := rays 27
def bank16828 : Fin 1 → Cell := oneBank p16828 ray16828
theorem signs16828 : ∀ j, Signs p16828 (bank16828 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16829 := params 28
abbrev ray16829 := rays 28
def bank16829 : Fin 1 → Cell := oneBank p16829 ray16829
theorem signs16829 : ∀ j, Signs p16829 (bank16829 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16830 := params 29
abbrev ray16830 := rays 29
def bank16830 : Fin 1 → Cell := oneBank p16830 ray16830
theorem signs16830 : ∀ j, Signs p16830 (bank16830 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16831 := params 30
abbrev ray16831 := rays 30
def bank16831 : Fin 1 → Cell := oneBank p16831 ray16831
theorem signs16831 : ∀ j, Signs p16831 (bank16831 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16832 := params 31
abbrev ray16832 := rays 31
def bank16832 : Fin 1 → Cell := oneBank p16832 ray16832
theorem signs16832 : ∀ j, Signs p16832 (bank16832 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16801_16832
