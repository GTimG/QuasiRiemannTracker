/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08897_08928
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97861982390371,97861638558893,97861294706426,97860950832970,97860606938525,97860263023093,97859919086674,97859575129268,97859231150876,97858887151499,97858543131138,97858199089793,97857855027464,97857510944153,97857166839860,97856822714585,97856478568330,97856134401094,97855790212879,97855446003685,97855101773513,97854757522363,97854413250236,97854068957133,97853724643054,97853380308000,97853035951971,97852691574969,97852347176993,97852002758045,97851658318125,97851313857234,97850969375372]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8896+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8897 := params 0
abbrev ray8897 := rays 0
def bank8897 : Fin 2 → Cell := twoBank p8897 ray8897
theorem signs8897 : ∀ j, Signs p8897 (bank8897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8898 := params 1
abbrev ray8898 := rays 1
def bank8898 : Fin 2 → Cell := twoBank p8898 ray8898
theorem signs8898 : ∀ j, Signs p8898 (bank8898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8899 := params 2
abbrev ray8899 := rays 2
def bank8899 : Fin 2 → Cell := twoBank p8899 ray8899
theorem signs8899 : ∀ j, Signs p8899 (bank8899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8900 := params 3
abbrev ray8900 := rays 3
def bank8900 : Fin 2 → Cell := twoBank p8900 ray8900
theorem signs8900 : ∀ j, Signs p8900 (bank8900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8901 := params 4
abbrev ray8901 := rays 4
def bank8901 : Fin 2 → Cell := twoBank p8901 ray8901
theorem signs8901 : ∀ j, Signs p8901 (bank8901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8902 := params 5
abbrev ray8902 := rays 5
def bank8902 : Fin 2 → Cell := twoBank p8902 ray8902
theorem signs8902 : ∀ j, Signs p8902 (bank8902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8903 := params 6
abbrev ray8903 := rays 6
def bank8903 : Fin 2 → Cell := twoBank p8903 ray8903
theorem signs8903 : ∀ j, Signs p8903 (bank8903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8904 := params 7
abbrev ray8904 := rays 7
def bank8904 : Fin 2 → Cell := twoBank p8904 ray8904
theorem signs8904 : ∀ j, Signs p8904 (bank8904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8905 := params 8
abbrev ray8905 := rays 8
def bank8905 : Fin 2 → Cell := twoBank p8905 ray8905
theorem signs8905 : ∀ j, Signs p8905 (bank8905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8906 := params 9
abbrev ray8906 := rays 9
def bank8906 : Fin 2 → Cell := twoBank p8906 ray8906
theorem signs8906 : ∀ j, Signs p8906 (bank8906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8907 := params 10
abbrev ray8907 := rays 10
def bank8907 : Fin 2 → Cell := twoBank p8907 ray8907
theorem signs8907 : ∀ j, Signs p8907 (bank8907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8908 := params 11
abbrev ray8908 := rays 11
def bank8908 : Fin 2 → Cell := twoBank p8908 ray8908
theorem signs8908 : ∀ j, Signs p8908 (bank8908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8909 := params 12
abbrev ray8909 := rays 12
def bank8909 : Fin 2 → Cell := twoBank p8909 ray8909
theorem signs8909 : ∀ j, Signs p8909 (bank8909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8910 := params 13
abbrev ray8910 := rays 13
def bank8910 : Fin 2 → Cell := twoBank p8910 ray8910
theorem signs8910 : ∀ j, Signs p8910 (bank8910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8911 := params 14
abbrev ray8911 := rays 14
def bank8911 : Fin 2 → Cell := twoBank p8911 ray8911
theorem signs8911 : ∀ j, Signs p8911 (bank8911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8912 := params 15
abbrev ray8912 := rays 15
def bank8912 : Fin 2 → Cell := twoBank p8912 ray8912
theorem signs8912 : ∀ j, Signs p8912 (bank8912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8913 := params 16
abbrev ray8913 := rays 16
def bank8913 : Fin 2 → Cell := twoBank p8913 ray8913
theorem signs8913 : ∀ j, Signs p8913 (bank8913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8914 := params 17
abbrev ray8914 := rays 17
def bank8914 : Fin 2 → Cell := twoBank p8914 ray8914
theorem signs8914 : ∀ j, Signs p8914 (bank8914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8915 := params 18
abbrev ray8915 := rays 18
def bank8915 : Fin 2 → Cell := twoBank p8915 ray8915
theorem signs8915 : ∀ j, Signs p8915 (bank8915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8916 := params 19
abbrev ray8916 := rays 19
def bank8916 : Fin 2 → Cell := twoBank p8916 ray8916
theorem signs8916 : ∀ j, Signs p8916 (bank8916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8917 := params 20
abbrev ray8917 := rays 20
def bank8917 : Fin 2 → Cell := twoBank p8917 ray8917
theorem signs8917 : ∀ j, Signs p8917 (bank8917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8918 := params 21
abbrev ray8918 := rays 21
def bank8918 : Fin 2 → Cell := twoBank p8918 ray8918
theorem signs8918 : ∀ j, Signs p8918 (bank8918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8919 := params 22
abbrev ray8919 := rays 22
def bank8919 : Fin 2 → Cell := twoBank p8919 ray8919
theorem signs8919 : ∀ j, Signs p8919 (bank8919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8920 := params 23
abbrev ray8920 := rays 23
def bank8920 : Fin 2 → Cell := twoBank p8920 ray8920
theorem signs8920 : ∀ j, Signs p8920 (bank8920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8921 := params 24
abbrev ray8921 := rays 24
def bank8921 : Fin 2 → Cell := twoBank p8921 ray8921
theorem signs8921 : ∀ j, Signs p8921 (bank8921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8922 := params 25
abbrev ray8922 := rays 25
def bank8922 : Fin 2 → Cell := twoBank p8922 ray8922
theorem signs8922 : ∀ j, Signs p8922 (bank8922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8923 := params 26
abbrev ray8923 := rays 26
def bank8923 : Fin 2 → Cell := twoBank p8923 ray8923
theorem signs8923 : ∀ j, Signs p8923 (bank8923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8924 := params 27
abbrev ray8924 := rays 27
def bank8924 : Fin 2 → Cell := twoBank p8924 ray8924
theorem signs8924 : ∀ j, Signs p8924 (bank8924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8925 := params 28
abbrev ray8925 := rays 28
def bank8925 : Fin 2 → Cell := twoBank p8925 ray8925
theorem signs8925 : ∀ j, Signs p8925 (bank8925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8926 := params 29
abbrev ray8926 := rays 29
def bank8926 : Fin 2 → Cell := twoBank p8926 ray8926
theorem signs8926 : ∀ j, Signs p8926 (bank8926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8927 := params 30
abbrev ray8927 := rays 30
def bank8927 : Fin 2 → Cell := twoBank p8927 ray8927
theorem signs8927 : ∀ j, Signs p8927 (bank8927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8928 := params 31
abbrev ray8928 := rays 31
def bank8928 : Fin 2 → Cell := twoBank p8928 ray8928
theorem signs8928 : ∀ j, Signs p8928 (bank8928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08897_08928
