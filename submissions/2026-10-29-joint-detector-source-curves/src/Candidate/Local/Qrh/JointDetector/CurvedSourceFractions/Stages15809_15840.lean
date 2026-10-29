/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15809_15840
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95023555724802,95023085419736,95022615098670,95022144761603,95021674408536,95021204039468,95020733654400,95020263253332,95019792836264,95019322403196,95018851954127,95018381489058,95017911007989,95017440510921,95016969997853,95016499468785,95016028923717,95015558362649,95015087785582,95014617192515,95014146583448,95013675958382,95013205317316,95012734660251,95012263987187,95011793298123,95011322593060,95010851871998,95010381134936,95009910381875,95009439612815,95008968827756,95008498026698]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15808+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15809 := params 0
abbrev ray15809 := rays 0
def bank15809 : Fin 1 → Cell := oneBank p15809 ray15809
theorem signs15809 : ∀ j, Signs p15809 (bank15809 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15810 := params 1
abbrev ray15810 := rays 1
def bank15810 : Fin 1 → Cell := oneBank p15810 ray15810
theorem signs15810 : ∀ j, Signs p15810 (bank15810 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15811 := params 2
abbrev ray15811 := rays 2
def bank15811 : Fin 1 → Cell := oneBank p15811 ray15811
theorem signs15811 : ∀ j, Signs p15811 (bank15811 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15812 := params 3
abbrev ray15812 := rays 3
def bank15812 : Fin 1 → Cell := oneBank p15812 ray15812
theorem signs15812 : ∀ j, Signs p15812 (bank15812 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15813 := params 4
abbrev ray15813 := rays 4
def bank15813 : Fin 1 → Cell := oneBank p15813 ray15813
theorem signs15813 : ∀ j, Signs p15813 (bank15813 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15814 := params 5
abbrev ray15814 := rays 5
def bank15814 : Fin 1 → Cell := oneBank p15814 ray15814
theorem signs15814 : ∀ j, Signs p15814 (bank15814 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15815 := params 6
abbrev ray15815 := rays 6
def bank15815 : Fin 1 → Cell := oneBank p15815 ray15815
theorem signs15815 : ∀ j, Signs p15815 (bank15815 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15816 := params 7
abbrev ray15816 := rays 7
def bank15816 : Fin 1 → Cell := oneBank p15816 ray15816
theorem signs15816 : ∀ j, Signs p15816 (bank15816 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15817 := params 8
abbrev ray15817 := rays 8
def bank15817 : Fin 1 → Cell := oneBank p15817 ray15817
theorem signs15817 : ∀ j, Signs p15817 (bank15817 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15818 := params 9
abbrev ray15818 := rays 9
def bank15818 : Fin 1 → Cell := oneBank p15818 ray15818
theorem signs15818 : ∀ j, Signs p15818 (bank15818 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15819 := params 10
abbrev ray15819 := rays 10
def bank15819 : Fin 1 → Cell := oneBank p15819 ray15819
theorem signs15819 : ∀ j, Signs p15819 (bank15819 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15820 := params 11
abbrev ray15820 := rays 11
def bank15820 : Fin 1 → Cell := oneBank p15820 ray15820
theorem signs15820 : ∀ j, Signs p15820 (bank15820 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15821 := params 12
abbrev ray15821 := rays 12
def bank15821 : Fin 1 → Cell := oneBank p15821 ray15821
theorem signs15821 : ∀ j, Signs p15821 (bank15821 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15822 := params 13
abbrev ray15822 := rays 13
def bank15822 : Fin 1 → Cell := oneBank p15822 ray15822
theorem signs15822 : ∀ j, Signs p15822 (bank15822 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15823 := params 14
abbrev ray15823 := rays 14
def bank15823 : Fin 1 → Cell := oneBank p15823 ray15823
theorem signs15823 : ∀ j, Signs p15823 (bank15823 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15824 := params 15
abbrev ray15824 := rays 15
def bank15824 : Fin 1 → Cell := oneBank p15824 ray15824
theorem signs15824 : ∀ j, Signs p15824 (bank15824 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15825 := params 16
abbrev ray15825 := rays 16
def bank15825 : Fin 1 → Cell := oneBank p15825 ray15825
theorem signs15825 : ∀ j, Signs p15825 (bank15825 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15826 := params 17
abbrev ray15826 := rays 17
def bank15826 : Fin 1 → Cell := oneBank p15826 ray15826
theorem signs15826 : ∀ j, Signs p15826 (bank15826 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15827 := params 18
abbrev ray15827 := rays 18
def bank15827 : Fin 1 → Cell := oneBank p15827 ray15827
theorem signs15827 : ∀ j, Signs p15827 (bank15827 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15828 := params 19
abbrev ray15828 := rays 19
def bank15828 : Fin 1 → Cell := oneBank p15828 ray15828
theorem signs15828 : ∀ j, Signs p15828 (bank15828 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15829 := params 20
abbrev ray15829 := rays 20
def bank15829 : Fin 1 → Cell := oneBank p15829 ray15829
theorem signs15829 : ∀ j, Signs p15829 (bank15829 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15830 := params 21
abbrev ray15830 := rays 21
def bank15830 : Fin 1 → Cell := oneBank p15830 ray15830
theorem signs15830 : ∀ j, Signs p15830 (bank15830 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15831 := params 22
abbrev ray15831 := rays 22
def bank15831 : Fin 1 → Cell := oneBank p15831 ray15831
theorem signs15831 : ∀ j, Signs p15831 (bank15831 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15832 := params 23
abbrev ray15832 := rays 23
def bank15832 : Fin 1 → Cell := oneBank p15832 ray15832
theorem signs15832 : ∀ j, Signs p15832 (bank15832 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15833 := params 24
abbrev ray15833 := rays 24
def bank15833 : Fin 1 → Cell := oneBank p15833 ray15833
theorem signs15833 : ∀ j, Signs p15833 (bank15833 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15834 := params 25
abbrev ray15834 := rays 25
def bank15834 : Fin 1 → Cell := oneBank p15834 ray15834
theorem signs15834 : ∀ j, Signs p15834 (bank15834 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15835 := params 26
abbrev ray15835 := rays 26
def bank15835 : Fin 1 → Cell := oneBank p15835 ray15835
theorem signs15835 : ∀ j, Signs p15835 (bank15835 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15836 := params 27
abbrev ray15836 := rays 27
def bank15836 : Fin 1 → Cell := oneBank p15836 ray15836
theorem signs15836 : ∀ j, Signs p15836 (bank15836 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15837 := params 28
abbrev ray15837 := rays 28
def bank15837 : Fin 1 → Cell := oneBank p15837 ray15837
theorem signs15837 : ∀ j, Signs p15837 (bank15837 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15838 := params 29
abbrev ray15838 := rays 29
def bank15838 : Fin 1 → Cell := oneBank p15838 ray15838
theorem signs15838 : ∀ j, Signs p15838 (bank15838 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15839 := params 30
abbrev ray15839 := rays 30
def bank15839 : Fin 1 → Cell := oneBank p15839 ray15839
theorem signs15839 : ∀ j, Signs p15839 (bank15839 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15840 := params 31
abbrev ray15840 := rays 31
def bank15840 : Fin 1 → Cell := oneBank p15840 ray15840
theorem signs15840 : ∀ j, Signs p15840 (bank15840 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15809_15840
