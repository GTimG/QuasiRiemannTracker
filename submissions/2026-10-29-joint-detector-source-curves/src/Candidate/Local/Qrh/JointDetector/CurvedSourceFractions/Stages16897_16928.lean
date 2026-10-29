/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16897_16928
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94502408759063,94501921059312,94501433343571,94500945611840,94500457864119,94499970100408,94499482320707,94498994525015,94498506713333,94498018885661,94497531041999,94497043182346,94496555306703,94496067415070,94495579507446,94495091583832,94494603644227,94494115688632,94493627717046,94493139729470,94492651725903,94492163706345,94491675670797,94491187619258,94490699551728,94490211468207,94489723368696,94489235253194,94488747121701,94488258974217,94487770810742,94487282631276,94486794435819]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16896+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16897 := params 0
abbrev ray16897 := rays 0
def bank16897 : Fin 1 → Cell := oneBank p16897 ray16897
theorem signs16897 : ∀ j, Signs p16897 (bank16897 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16898 := params 1
abbrev ray16898 := rays 1
def bank16898 : Fin 1 → Cell := oneBank p16898 ray16898
theorem signs16898 : ∀ j, Signs p16898 (bank16898 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16899 := params 2
abbrev ray16899 := rays 2
def bank16899 : Fin 1 → Cell := oneBank p16899 ray16899
theorem signs16899 : ∀ j, Signs p16899 (bank16899 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16900 := params 3
abbrev ray16900 := rays 3
def bank16900 : Fin 1 → Cell := oneBank p16900 ray16900
theorem signs16900 : ∀ j, Signs p16900 (bank16900 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16901 := params 4
abbrev ray16901 := rays 4
def bank16901 : Fin 1 → Cell := oneBank p16901 ray16901
theorem signs16901 : ∀ j, Signs p16901 (bank16901 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16902 := params 5
abbrev ray16902 := rays 5
def bank16902 : Fin 1 → Cell := oneBank p16902 ray16902
theorem signs16902 : ∀ j, Signs p16902 (bank16902 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16903 := params 6
abbrev ray16903 := rays 6
def bank16903 : Fin 1 → Cell := oneBank p16903 ray16903
theorem signs16903 : ∀ j, Signs p16903 (bank16903 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16904 := params 7
abbrev ray16904 := rays 7
def bank16904 : Fin 1 → Cell := oneBank p16904 ray16904
theorem signs16904 : ∀ j, Signs p16904 (bank16904 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16905 := params 8
abbrev ray16905 := rays 8
def bank16905 : Fin 1 → Cell := oneBank p16905 ray16905
theorem signs16905 : ∀ j, Signs p16905 (bank16905 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16906 := params 9
abbrev ray16906 := rays 9
def bank16906 : Fin 1 → Cell := oneBank p16906 ray16906
theorem signs16906 : ∀ j, Signs p16906 (bank16906 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16907 := params 10
abbrev ray16907 := rays 10
def bank16907 : Fin 1 → Cell := oneBank p16907 ray16907
theorem signs16907 : ∀ j, Signs p16907 (bank16907 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16908 := params 11
abbrev ray16908 := rays 11
def bank16908 : Fin 1 → Cell := oneBank p16908 ray16908
theorem signs16908 : ∀ j, Signs p16908 (bank16908 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16909 := params 12
abbrev ray16909 := rays 12
def bank16909 : Fin 1 → Cell := oneBank p16909 ray16909
theorem signs16909 : ∀ j, Signs p16909 (bank16909 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16910 := params 13
abbrev ray16910 := rays 13
def bank16910 : Fin 1 → Cell := oneBank p16910 ray16910
theorem signs16910 : ∀ j, Signs p16910 (bank16910 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16911 := params 14
abbrev ray16911 := rays 14
def bank16911 : Fin 1 → Cell := oneBank p16911 ray16911
theorem signs16911 : ∀ j, Signs p16911 (bank16911 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16912 := params 15
abbrev ray16912 := rays 15
def bank16912 : Fin 1 → Cell := oneBank p16912 ray16912
theorem signs16912 : ∀ j, Signs p16912 (bank16912 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16913 := params 16
abbrev ray16913 := rays 16
def bank16913 : Fin 1 → Cell := oneBank p16913 ray16913
theorem signs16913 : ∀ j, Signs p16913 (bank16913 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16914 := params 17
abbrev ray16914 := rays 17
def bank16914 : Fin 1 → Cell := oneBank p16914 ray16914
theorem signs16914 : ∀ j, Signs p16914 (bank16914 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16915 := params 18
abbrev ray16915 := rays 18
def bank16915 : Fin 1 → Cell := oneBank p16915 ray16915
theorem signs16915 : ∀ j, Signs p16915 (bank16915 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16916 := params 19
abbrev ray16916 := rays 19
def bank16916 : Fin 1 → Cell := oneBank p16916 ray16916
theorem signs16916 : ∀ j, Signs p16916 (bank16916 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16917 := params 20
abbrev ray16917 := rays 20
def bank16917 : Fin 1 → Cell := oneBank p16917 ray16917
theorem signs16917 : ∀ j, Signs p16917 (bank16917 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16918 := params 21
abbrev ray16918 := rays 21
def bank16918 : Fin 1 → Cell := oneBank p16918 ray16918
theorem signs16918 : ∀ j, Signs p16918 (bank16918 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16919 := params 22
abbrev ray16919 := rays 22
def bank16919 : Fin 1 → Cell := oneBank p16919 ray16919
theorem signs16919 : ∀ j, Signs p16919 (bank16919 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16920 := params 23
abbrev ray16920 := rays 23
def bank16920 : Fin 1 → Cell := oneBank p16920 ray16920
theorem signs16920 : ∀ j, Signs p16920 (bank16920 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16921 := params 24
abbrev ray16921 := rays 24
def bank16921 : Fin 1 → Cell := oneBank p16921 ray16921
theorem signs16921 : ∀ j, Signs p16921 (bank16921 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16922 := params 25
abbrev ray16922 := rays 25
def bank16922 : Fin 1 → Cell := oneBank p16922 ray16922
theorem signs16922 : ∀ j, Signs p16922 (bank16922 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16923 := params 26
abbrev ray16923 := rays 26
def bank16923 : Fin 1 → Cell := oneBank p16923 ray16923
theorem signs16923 : ∀ j, Signs p16923 (bank16923 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16924 := params 27
abbrev ray16924 := rays 27
def bank16924 : Fin 1 → Cell := oneBank p16924 ray16924
theorem signs16924 : ∀ j, Signs p16924 (bank16924 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16925 := params 28
abbrev ray16925 := rays 28
def bank16925 : Fin 1 → Cell := oneBank p16925 ray16925
theorem signs16925 : ∀ j, Signs p16925 (bank16925 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16926 := params 29
abbrev ray16926 := rays 29
def bank16926 : Fin 1 → Cell := oneBank p16926 ray16926
theorem signs16926 : ∀ j, Signs p16926 (bank16926 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16927 := params 30
abbrev ray16927 := rays 30
def bank16927 : Fin 1 → Cell := oneBank p16927 ray16927
theorem signs16927 : ∀ j, Signs p16927 (bank16927 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16928 := params 31
abbrev ray16928 := rays 31
def bank16928 : Fin 1 → Cell := oneBank p16928 ray16928
theorem signs16928 : ∀ j, Signs p16928 (bank16928 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16897_16928
