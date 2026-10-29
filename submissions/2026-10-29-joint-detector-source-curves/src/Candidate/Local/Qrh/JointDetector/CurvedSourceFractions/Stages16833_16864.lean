/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16833_16864
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94533588285299,94533101608846,94532614916405,94532128207976,94531641483559,94531154743153,94530667986759,94530181214377,94529694426007,94529207621648,94528720801301,94528233964965,94527747112641,94527260244329,94526773360028,94526286459739,94525799543461,94525312611195,94524825662940,94524338698696,94523851718464,94523364722243,94522877710034,94522390681836,94521903637649,94521416577473,94520929501308,94520442409155,94519955301013,94519468176882,94518981036762,94518493880653,94518006708555]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16832+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16833 := params 0
abbrev ray16833 := rays 0
def bank16833 : Fin 1 → Cell := oneBank p16833 ray16833
theorem signs16833 : ∀ j, Signs p16833 (bank16833 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16834 := params 1
abbrev ray16834 := rays 1
def bank16834 : Fin 1 → Cell := oneBank p16834 ray16834
theorem signs16834 : ∀ j, Signs p16834 (bank16834 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16835 := params 2
abbrev ray16835 := rays 2
def bank16835 : Fin 1 → Cell := oneBank p16835 ray16835
theorem signs16835 : ∀ j, Signs p16835 (bank16835 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16836 := params 3
abbrev ray16836 := rays 3
def bank16836 : Fin 1 → Cell := oneBank p16836 ray16836
theorem signs16836 : ∀ j, Signs p16836 (bank16836 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16837 := params 4
abbrev ray16837 := rays 4
def bank16837 : Fin 1 → Cell := oneBank p16837 ray16837
theorem signs16837 : ∀ j, Signs p16837 (bank16837 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16838 := params 5
abbrev ray16838 := rays 5
def bank16838 : Fin 1 → Cell := oneBank p16838 ray16838
theorem signs16838 : ∀ j, Signs p16838 (bank16838 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16839 := params 6
abbrev ray16839 := rays 6
def bank16839 : Fin 1 → Cell := oneBank p16839 ray16839
theorem signs16839 : ∀ j, Signs p16839 (bank16839 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16840 := params 7
abbrev ray16840 := rays 7
def bank16840 : Fin 1 → Cell := oneBank p16840 ray16840
theorem signs16840 : ∀ j, Signs p16840 (bank16840 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16841 := params 8
abbrev ray16841 := rays 8
def bank16841 : Fin 1 → Cell := oneBank p16841 ray16841
theorem signs16841 : ∀ j, Signs p16841 (bank16841 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16842 := params 9
abbrev ray16842 := rays 9
def bank16842 : Fin 1 → Cell := oneBank p16842 ray16842
theorem signs16842 : ∀ j, Signs p16842 (bank16842 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16843 := params 10
abbrev ray16843 := rays 10
def bank16843 : Fin 1 → Cell := oneBank p16843 ray16843
theorem signs16843 : ∀ j, Signs p16843 (bank16843 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16844 := params 11
abbrev ray16844 := rays 11
def bank16844 : Fin 1 → Cell := oneBank p16844 ray16844
theorem signs16844 : ∀ j, Signs p16844 (bank16844 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16845 := params 12
abbrev ray16845 := rays 12
def bank16845 : Fin 1 → Cell := oneBank p16845 ray16845
theorem signs16845 : ∀ j, Signs p16845 (bank16845 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16846 := params 13
abbrev ray16846 := rays 13
def bank16846 : Fin 1 → Cell := oneBank p16846 ray16846
theorem signs16846 : ∀ j, Signs p16846 (bank16846 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16847 := params 14
abbrev ray16847 := rays 14
def bank16847 : Fin 1 → Cell := oneBank p16847 ray16847
theorem signs16847 : ∀ j, Signs p16847 (bank16847 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16848 := params 15
abbrev ray16848 := rays 15
def bank16848 : Fin 1 → Cell := oneBank p16848 ray16848
theorem signs16848 : ∀ j, Signs p16848 (bank16848 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16849 := params 16
abbrev ray16849 := rays 16
def bank16849 : Fin 1 → Cell := oneBank p16849 ray16849
theorem signs16849 : ∀ j, Signs p16849 (bank16849 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16850 := params 17
abbrev ray16850 := rays 17
def bank16850 : Fin 1 → Cell := oneBank p16850 ray16850
theorem signs16850 : ∀ j, Signs p16850 (bank16850 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16851 := params 18
abbrev ray16851 := rays 18
def bank16851 : Fin 1 → Cell := oneBank p16851 ray16851
theorem signs16851 : ∀ j, Signs p16851 (bank16851 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16852 := params 19
abbrev ray16852 := rays 19
def bank16852 : Fin 1 → Cell := oneBank p16852 ray16852
theorem signs16852 : ∀ j, Signs p16852 (bank16852 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16853 := params 20
abbrev ray16853 := rays 20
def bank16853 : Fin 1 → Cell := oneBank p16853 ray16853
theorem signs16853 : ∀ j, Signs p16853 (bank16853 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16854 := params 21
abbrev ray16854 := rays 21
def bank16854 : Fin 1 → Cell := oneBank p16854 ray16854
theorem signs16854 : ∀ j, Signs p16854 (bank16854 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16855 := params 22
abbrev ray16855 := rays 22
def bank16855 : Fin 1 → Cell := oneBank p16855 ray16855
theorem signs16855 : ∀ j, Signs p16855 (bank16855 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16856 := params 23
abbrev ray16856 := rays 23
def bank16856 : Fin 1 → Cell := oneBank p16856 ray16856
theorem signs16856 : ∀ j, Signs p16856 (bank16856 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16857 := params 24
abbrev ray16857 := rays 24
def bank16857 : Fin 1 → Cell := oneBank p16857 ray16857
theorem signs16857 : ∀ j, Signs p16857 (bank16857 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16858 := params 25
abbrev ray16858 := rays 25
def bank16858 : Fin 1 → Cell := oneBank p16858 ray16858
theorem signs16858 : ∀ j, Signs p16858 (bank16858 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16859 := params 26
abbrev ray16859 := rays 26
def bank16859 : Fin 1 → Cell := oneBank p16859 ray16859
theorem signs16859 : ∀ j, Signs p16859 (bank16859 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16860 := params 27
abbrev ray16860 := rays 27
def bank16860 : Fin 1 → Cell := oneBank p16860 ray16860
theorem signs16860 : ∀ j, Signs p16860 (bank16860 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16861 := params 28
abbrev ray16861 := rays 28
def bank16861 : Fin 1 → Cell := oneBank p16861 ray16861
theorem signs16861 : ∀ j, Signs p16861 (bank16861 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16862 := params 29
abbrev ray16862 := rays 29
def bank16862 : Fin 1 → Cell := oneBank p16862 ray16862
theorem signs16862 : ∀ j, Signs p16862 (bank16862 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16863 := params 30
abbrev ray16863 := rays 30
def bank16863 : Fin 1 → Cell := oneBank p16863 ray16863
theorem signs16863 : ∀ j, Signs p16863 (bank16863 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16864 := params 31
abbrev ray16864 := rays 31
def bank16864 : Fin 1 → Cell := oneBank p16864 ray16864
theorem signs16864 : ∀ j, Signs p16864 (bank16864 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16833_16864
