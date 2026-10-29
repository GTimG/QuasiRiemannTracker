/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07905_07936
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98192619273685,98192296586887,98191973878436,98191651148333,98191328396578,98191005623172,98190682828116,98190360011411,98190037173057,98189714313055,98189391431406,98189068528110,98188745603168,98188422656581,98188099688350,98187776698475,98187453686957,98187130653797,98186807598995,98186484522552,98186161424469,98185838304746,98185515163385,98185192000385,98184868815748,98184545609474,98184222381564,98183899132019,98183575860840,98183252568027,98182929253581,98182605917502,98182282559791]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7904+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7905 := params 0
abbrev ray7905 := rays 0
def bank7905 : Fin 2 → Cell := twoBank p7905 ray7905
theorem signs7905 : ∀ j, Signs p7905 (bank7905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7906 := params 1
abbrev ray7906 := rays 1
def bank7906 : Fin 2 → Cell := twoBank p7906 ray7906
theorem signs7906 : ∀ j, Signs p7906 (bank7906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7907 := params 2
abbrev ray7907 := rays 2
def bank7907 : Fin 2 → Cell := twoBank p7907 ray7907
theorem signs7907 : ∀ j, Signs p7907 (bank7907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7908 := params 3
abbrev ray7908 := rays 3
def bank7908 : Fin 2 → Cell := twoBank p7908 ray7908
theorem signs7908 : ∀ j, Signs p7908 (bank7908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7909 := params 4
abbrev ray7909 := rays 4
def bank7909 : Fin 2 → Cell := twoBank p7909 ray7909
theorem signs7909 : ∀ j, Signs p7909 (bank7909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7910 := params 5
abbrev ray7910 := rays 5
def bank7910 : Fin 2 → Cell := twoBank p7910 ray7910
theorem signs7910 : ∀ j, Signs p7910 (bank7910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7911 := params 6
abbrev ray7911 := rays 6
def bank7911 : Fin 2 → Cell := twoBank p7911 ray7911
theorem signs7911 : ∀ j, Signs p7911 (bank7911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7912 := params 7
abbrev ray7912 := rays 7
def bank7912 : Fin 2 → Cell := twoBank p7912 ray7912
theorem signs7912 : ∀ j, Signs p7912 (bank7912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7913 := params 8
abbrev ray7913 := rays 8
def bank7913 : Fin 2 → Cell := twoBank p7913 ray7913
theorem signs7913 : ∀ j, Signs p7913 (bank7913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7914 := params 9
abbrev ray7914 := rays 9
def bank7914 : Fin 2 → Cell := twoBank p7914 ray7914
theorem signs7914 : ∀ j, Signs p7914 (bank7914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7915 := params 10
abbrev ray7915 := rays 10
def bank7915 : Fin 2 → Cell := twoBank p7915 ray7915
theorem signs7915 : ∀ j, Signs p7915 (bank7915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7916 := params 11
abbrev ray7916 := rays 11
def bank7916 : Fin 2 → Cell := twoBank p7916 ray7916
theorem signs7916 : ∀ j, Signs p7916 (bank7916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7917 := params 12
abbrev ray7917 := rays 12
def bank7917 : Fin 2 → Cell := twoBank p7917 ray7917
theorem signs7917 : ∀ j, Signs p7917 (bank7917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7918 := params 13
abbrev ray7918 := rays 13
def bank7918 : Fin 2 → Cell := twoBank p7918 ray7918
theorem signs7918 : ∀ j, Signs p7918 (bank7918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7919 := params 14
abbrev ray7919 := rays 14
def bank7919 : Fin 2 → Cell := twoBank p7919 ray7919
theorem signs7919 : ∀ j, Signs p7919 (bank7919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7920 := params 15
abbrev ray7920 := rays 15
def bank7920 : Fin 2 → Cell := twoBank p7920 ray7920
theorem signs7920 : ∀ j, Signs p7920 (bank7920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7921 := params 16
abbrev ray7921 := rays 16
def bank7921 : Fin 2 → Cell := twoBank p7921 ray7921
theorem signs7921 : ∀ j, Signs p7921 (bank7921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7922 := params 17
abbrev ray7922 := rays 17
def bank7922 : Fin 2 → Cell := twoBank p7922 ray7922
theorem signs7922 : ∀ j, Signs p7922 (bank7922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7923 := params 18
abbrev ray7923 := rays 18
def bank7923 : Fin 2 → Cell := twoBank p7923 ray7923
theorem signs7923 : ∀ j, Signs p7923 (bank7923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7924 := params 19
abbrev ray7924 := rays 19
def bank7924 : Fin 2 → Cell := twoBank p7924 ray7924
theorem signs7924 : ∀ j, Signs p7924 (bank7924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7925 := params 20
abbrev ray7925 := rays 20
def bank7925 : Fin 2 → Cell := twoBank p7925 ray7925
theorem signs7925 : ∀ j, Signs p7925 (bank7925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7926 := params 21
abbrev ray7926 := rays 21
def bank7926 : Fin 2 → Cell := twoBank p7926 ray7926
theorem signs7926 : ∀ j, Signs p7926 (bank7926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7927 := params 22
abbrev ray7927 := rays 22
def bank7927 : Fin 2 → Cell := twoBank p7927 ray7927
theorem signs7927 : ∀ j, Signs p7927 (bank7927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7928 := params 23
abbrev ray7928 := rays 23
def bank7928 : Fin 2 → Cell := twoBank p7928 ray7928
theorem signs7928 : ∀ j, Signs p7928 (bank7928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7929 := params 24
abbrev ray7929 := rays 24
def bank7929 : Fin 2 → Cell := twoBank p7929 ray7929
theorem signs7929 : ∀ j, Signs p7929 (bank7929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7930 := params 25
abbrev ray7930 := rays 25
def bank7930 : Fin 2 → Cell := twoBank p7930 ray7930
theorem signs7930 : ∀ j, Signs p7930 (bank7930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7931 := params 26
abbrev ray7931 := rays 26
def bank7931 : Fin 2 → Cell := twoBank p7931 ray7931
theorem signs7931 : ∀ j, Signs p7931 (bank7931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7932 := params 27
abbrev ray7932 := rays 27
def bank7932 : Fin 2 → Cell := twoBank p7932 ray7932
theorem signs7932 : ∀ j, Signs p7932 (bank7932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7933 := params 28
abbrev ray7933 := rays 28
def bank7933 : Fin 2 → Cell := twoBank p7933 ray7933
theorem signs7933 : ∀ j, Signs p7933 (bank7933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7934 := params 29
abbrev ray7934 := rays 29
def bank7934 : Fin 2 → Cell := twoBank p7934 ray7934
theorem signs7934 : ∀ j, Signs p7934 (bank7934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7935 := params 30
abbrev ray7935 := rays 30
def bank7935 : Fin 2 → Cell := twoBank p7935 ray7935
theorem signs7935 : ∀ j, Signs p7935 (bank7935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7936 := params 31
abbrev ray7936 := rays 31
def bank7936 : Fin 2 → Cell := twoBank p7936 ray7936
theorem signs7936 : ∀ j, Signs p7936 (bank7936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07905_07936
