/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06913_06944
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98501940905974,98501640061536,98501339194700,98501038305468,98500737393839,98500436459815,98500135503397,98499834524585,98499533523380,98499232499783,98498931453795,98498630385416,98498329294647,98498028181489,98497727045943,98497425888010,98497124707690,98496823504985,98496522279895,98496221032421,98495919762563,98495618470323,98495317155701,98495015818698,98494714459315,98494413077552,98494111673411,98493810246892,98493508797996,98493207326724,98492905833076,98492604317053,98492302778657]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6912+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6913 := params 0
abbrev ray6913 := rays 0
def bank6913 : Fin 2 → Cell := twoBank p6913 ray6913
theorem signs6913 : ∀ j, Signs p6913 (bank6913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6914 := params 1
abbrev ray6914 := rays 1
def bank6914 : Fin 2 → Cell := twoBank p6914 ray6914
theorem signs6914 : ∀ j, Signs p6914 (bank6914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6915 := params 2
abbrev ray6915 := rays 2
def bank6915 : Fin 2 → Cell := twoBank p6915 ray6915
theorem signs6915 : ∀ j, Signs p6915 (bank6915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6916 := params 3
abbrev ray6916 := rays 3
def bank6916 : Fin 2 → Cell := twoBank p6916 ray6916
theorem signs6916 : ∀ j, Signs p6916 (bank6916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6917 := params 4
abbrev ray6917 := rays 4
def bank6917 : Fin 2 → Cell := twoBank p6917 ray6917
theorem signs6917 : ∀ j, Signs p6917 (bank6917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6918 := params 5
abbrev ray6918 := rays 5
def bank6918 : Fin 2 → Cell := twoBank p6918 ray6918
theorem signs6918 : ∀ j, Signs p6918 (bank6918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6919 := params 6
abbrev ray6919 := rays 6
def bank6919 : Fin 2 → Cell := twoBank p6919 ray6919
theorem signs6919 : ∀ j, Signs p6919 (bank6919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6920 := params 7
abbrev ray6920 := rays 7
def bank6920 : Fin 2 → Cell := twoBank p6920 ray6920
theorem signs6920 : ∀ j, Signs p6920 (bank6920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6921 := params 8
abbrev ray6921 := rays 8
def bank6921 : Fin 2 → Cell := twoBank p6921 ray6921
theorem signs6921 : ∀ j, Signs p6921 (bank6921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6922 := params 9
abbrev ray6922 := rays 9
def bank6922 : Fin 2 → Cell := twoBank p6922 ray6922
theorem signs6922 : ∀ j, Signs p6922 (bank6922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6923 := params 10
abbrev ray6923 := rays 10
def bank6923 : Fin 2 → Cell := twoBank p6923 ray6923
theorem signs6923 : ∀ j, Signs p6923 (bank6923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6924 := params 11
abbrev ray6924 := rays 11
def bank6924 : Fin 2 → Cell := twoBank p6924 ray6924
theorem signs6924 : ∀ j, Signs p6924 (bank6924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6925 := params 12
abbrev ray6925 := rays 12
def bank6925 : Fin 2 → Cell := twoBank p6925 ray6925
theorem signs6925 : ∀ j, Signs p6925 (bank6925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6926 := params 13
abbrev ray6926 := rays 13
def bank6926 : Fin 2 → Cell := twoBank p6926 ray6926
theorem signs6926 : ∀ j, Signs p6926 (bank6926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6927 := params 14
abbrev ray6927 := rays 14
def bank6927 : Fin 2 → Cell := twoBank p6927 ray6927
theorem signs6927 : ∀ j, Signs p6927 (bank6927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6928 := params 15
abbrev ray6928 := rays 15
def bank6928 : Fin 2 → Cell := twoBank p6928 ray6928
theorem signs6928 : ∀ j, Signs p6928 (bank6928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6929 := params 16
abbrev ray6929 := rays 16
def bank6929 : Fin 2 → Cell := twoBank p6929 ray6929
theorem signs6929 : ∀ j, Signs p6929 (bank6929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6930 := params 17
abbrev ray6930 := rays 17
def bank6930 : Fin 2 → Cell := twoBank p6930 ray6930
theorem signs6930 : ∀ j, Signs p6930 (bank6930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6931 := params 18
abbrev ray6931 := rays 18
def bank6931 : Fin 2 → Cell := twoBank p6931 ray6931
theorem signs6931 : ∀ j, Signs p6931 (bank6931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6932 := params 19
abbrev ray6932 := rays 19
def bank6932 : Fin 2 → Cell := twoBank p6932 ray6932
theorem signs6932 : ∀ j, Signs p6932 (bank6932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6933 := params 20
abbrev ray6933 := rays 20
def bank6933 : Fin 2 → Cell := twoBank p6933 ray6933
theorem signs6933 : ∀ j, Signs p6933 (bank6933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6934 := params 21
abbrev ray6934 := rays 21
def bank6934 : Fin 2 → Cell := twoBank p6934 ray6934
theorem signs6934 : ∀ j, Signs p6934 (bank6934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6935 := params 22
abbrev ray6935 := rays 22
def bank6935 : Fin 2 → Cell := twoBank p6935 ray6935
theorem signs6935 : ∀ j, Signs p6935 (bank6935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6936 := params 23
abbrev ray6936 := rays 23
def bank6936 : Fin 2 → Cell := twoBank p6936 ray6936
theorem signs6936 : ∀ j, Signs p6936 (bank6936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6937 := params 24
abbrev ray6937 := rays 24
def bank6937 : Fin 2 → Cell := twoBank p6937 ray6937
theorem signs6937 : ∀ j, Signs p6937 (bank6937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6938 := params 25
abbrev ray6938 := rays 25
def bank6938 : Fin 2 → Cell := twoBank p6938 ray6938
theorem signs6938 : ∀ j, Signs p6938 (bank6938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6939 := params 26
abbrev ray6939 := rays 26
def bank6939 : Fin 2 → Cell := twoBank p6939 ray6939
theorem signs6939 : ∀ j, Signs p6939 (bank6939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6940 := params 27
abbrev ray6940 := rays 27
def bank6940 : Fin 2 → Cell := twoBank p6940 ray6940
theorem signs6940 : ∀ j, Signs p6940 (bank6940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6941 := params 28
abbrev ray6941 := rays 28
def bank6941 : Fin 2 → Cell := twoBank p6941 ray6941
theorem signs6941 : ∀ j, Signs p6941 (bank6941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6942 := params 29
abbrev ray6942 := rays 29
def bank6942 : Fin 2 → Cell := twoBank p6942 ray6942
theorem signs6942 : ∀ j, Signs p6942 (bank6942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6943 := params 30
abbrev ray6943 := rays 30
def bank6943 : Fin 2 → Cell := twoBank p6943 ray6943
theorem signs6943 : ∀ j, Signs p6943 (bank6943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6944 := params 31
abbrev ray6944 := rays 31
def bank6944 : Fin 2 → Cell := twoBank p6944 ray6944
theorem signs6944 : ∀ j, Signs p6944 (bank6944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06913_06944
