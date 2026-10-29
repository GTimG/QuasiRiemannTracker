/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15905_15936
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94978333483235,94977861642343,94977389785455,94976917912571,94976446023691,94975974118815,94975502197943,94975030261075,94974558308212,94974086339353,94973614354498,94973142353648,94972670336802,94972198303961,94971726255124,94971254190292,94970782109465,94970310012642,94969837899824,94969365771011,94968893626203,94968421465399,94967949288600,94967477095806,94967004887017,94966532662233,94966060421454,94965588164680,94965115891912,94964643603149,94964171298391,94963698977638,94963226640891]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15904+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15905 := params 0
abbrev ray15905 := rays 0
def bank15905 : Fin 1 → Cell := oneBank p15905 ray15905
theorem signs15905 : ∀ j, Signs p15905 (bank15905 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15906 := params 1
abbrev ray15906 := rays 1
def bank15906 : Fin 1 → Cell := oneBank p15906 ray15906
theorem signs15906 : ∀ j, Signs p15906 (bank15906 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15907 := params 2
abbrev ray15907 := rays 2
def bank15907 : Fin 1 → Cell := oneBank p15907 ray15907
theorem signs15907 : ∀ j, Signs p15907 (bank15907 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15908 := params 3
abbrev ray15908 := rays 3
def bank15908 : Fin 1 → Cell := oneBank p15908 ray15908
theorem signs15908 : ∀ j, Signs p15908 (bank15908 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15909 := params 4
abbrev ray15909 := rays 4
def bank15909 : Fin 1 → Cell := oneBank p15909 ray15909
theorem signs15909 : ∀ j, Signs p15909 (bank15909 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15910 := params 5
abbrev ray15910 := rays 5
def bank15910 : Fin 1 → Cell := oneBank p15910 ray15910
theorem signs15910 : ∀ j, Signs p15910 (bank15910 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15911 := params 6
abbrev ray15911 := rays 6
def bank15911 : Fin 1 → Cell := oneBank p15911 ray15911
theorem signs15911 : ∀ j, Signs p15911 (bank15911 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15912 := params 7
abbrev ray15912 := rays 7
def bank15912 : Fin 1 → Cell := oneBank p15912 ray15912
theorem signs15912 : ∀ j, Signs p15912 (bank15912 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15913 := params 8
abbrev ray15913 := rays 8
def bank15913 : Fin 1 → Cell := oneBank p15913 ray15913
theorem signs15913 : ∀ j, Signs p15913 (bank15913 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15914 := params 9
abbrev ray15914 := rays 9
def bank15914 : Fin 1 → Cell := oneBank p15914 ray15914
theorem signs15914 : ∀ j, Signs p15914 (bank15914 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15915 := params 10
abbrev ray15915 := rays 10
def bank15915 : Fin 1 → Cell := oneBank p15915 ray15915
theorem signs15915 : ∀ j, Signs p15915 (bank15915 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15916 := params 11
abbrev ray15916 := rays 11
def bank15916 : Fin 1 → Cell := oneBank p15916 ray15916
theorem signs15916 : ∀ j, Signs p15916 (bank15916 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15917 := params 12
abbrev ray15917 := rays 12
def bank15917 : Fin 1 → Cell := oneBank p15917 ray15917
theorem signs15917 : ∀ j, Signs p15917 (bank15917 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15918 := params 13
abbrev ray15918 := rays 13
def bank15918 : Fin 1 → Cell := oneBank p15918 ray15918
theorem signs15918 : ∀ j, Signs p15918 (bank15918 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15919 := params 14
abbrev ray15919 := rays 14
def bank15919 : Fin 1 → Cell := oneBank p15919 ray15919
theorem signs15919 : ∀ j, Signs p15919 (bank15919 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15920 := params 15
abbrev ray15920 := rays 15
def bank15920 : Fin 1 → Cell := oneBank p15920 ray15920
theorem signs15920 : ∀ j, Signs p15920 (bank15920 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15921 := params 16
abbrev ray15921 := rays 16
def bank15921 : Fin 1 → Cell := oneBank p15921 ray15921
theorem signs15921 : ∀ j, Signs p15921 (bank15921 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15922 := params 17
abbrev ray15922 := rays 17
def bank15922 : Fin 1 → Cell := oneBank p15922 ray15922
theorem signs15922 : ∀ j, Signs p15922 (bank15922 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15923 := params 18
abbrev ray15923 := rays 18
def bank15923 : Fin 1 → Cell := oneBank p15923 ray15923
theorem signs15923 : ∀ j, Signs p15923 (bank15923 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15924 := params 19
abbrev ray15924 := rays 19
def bank15924 : Fin 1 → Cell := oneBank p15924 ray15924
theorem signs15924 : ∀ j, Signs p15924 (bank15924 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15925 := params 20
abbrev ray15925 := rays 20
def bank15925 : Fin 1 → Cell := oneBank p15925 ray15925
theorem signs15925 : ∀ j, Signs p15925 (bank15925 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15926 := params 21
abbrev ray15926 := rays 21
def bank15926 : Fin 1 → Cell := oneBank p15926 ray15926
theorem signs15926 : ∀ j, Signs p15926 (bank15926 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15927 := params 22
abbrev ray15927 := rays 22
def bank15927 : Fin 1 → Cell := oneBank p15927 ray15927
theorem signs15927 : ∀ j, Signs p15927 (bank15927 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15928 := params 23
abbrev ray15928 := rays 23
def bank15928 : Fin 1 → Cell := oneBank p15928 ray15928
theorem signs15928 : ∀ j, Signs p15928 (bank15928 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15929 := params 24
abbrev ray15929 := rays 24
def bank15929 : Fin 1 → Cell := oneBank p15929 ray15929
theorem signs15929 : ∀ j, Signs p15929 (bank15929 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15930 := params 25
abbrev ray15930 := rays 25
def bank15930 : Fin 1 → Cell := oneBank p15930 ray15930
theorem signs15930 : ∀ j, Signs p15930 (bank15930 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15931 := params 26
abbrev ray15931 := rays 26
def bank15931 : Fin 1 → Cell := oneBank p15931 ray15931
theorem signs15931 : ∀ j, Signs p15931 (bank15931 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15932 := params 27
abbrev ray15932 := rays 27
def bank15932 : Fin 1 → Cell := oneBank p15932 ray15932
theorem signs15932 : ∀ j, Signs p15932 (bank15932 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15933 := params 28
abbrev ray15933 := rays 28
def bank15933 : Fin 1 → Cell := oneBank p15933 ray15933
theorem signs15933 : ∀ j, Signs p15933 (bank15933 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15934 := params 29
abbrev ray15934 := rays 29
def bank15934 : Fin 1 → Cell := oneBank p15934 ray15934
theorem signs15934 : ∀ j, Signs p15934 (bank15934 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15935 := params 30
abbrev ray15935 := rays 30
def bank15935 : Fin 1 → Cell := oneBank p15935 ray15935
theorem signs15935 : ∀ j, Signs p15935 (bank15935 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15936 := params 31
abbrev ray15936 := rays 31
def bank15936 : Fin 1 → Cell := oneBank p15936 ray15936
theorem signs15936 : ∀ j, Signs p15936 (bank15936 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15905_15936
