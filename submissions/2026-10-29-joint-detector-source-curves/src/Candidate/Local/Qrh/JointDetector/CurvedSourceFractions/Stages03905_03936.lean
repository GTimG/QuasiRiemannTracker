/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03905_03936
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99301566227553,99301336819089,99301107385355,99300877926352,99300648442081,99300418932543,99300189397740,99299959837672,99299730252341,99299500641748,99299271005894,99299041344780,99298811658407,99298581946777,99298352209890,99298122447748,99297892660351,99297662847701,99297433009799,99297203146647,99296973258245,99296743344594,99296513405696,99296283441552,99296053452163,99295823437530,99295593397654,99295363332536,99295133242177,99294903126579,99294672985743,99294442819669,99294212628359]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3904+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3905 := params 0
abbrev ray3905 := rays 0
def bank3905 : Fin 2 → Cell := twoBank p3905 ray3905
theorem signs3905 : ∀ j, Signs p3905 (bank3905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3906 := params 1
abbrev ray3906 := rays 1
def bank3906 : Fin 2 → Cell := twoBank p3906 ray3906
theorem signs3906 : ∀ j, Signs p3906 (bank3906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3907 := params 2
abbrev ray3907 := rays 2
def bank3907 : Fin 2 → Cell := twoBank p3907 ray3907
theorem signs3907 : ∀ j, Signs p3907 (bank3907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3908 := params 3
abbrev ray3908 := rays 3
def bank3908 : Fin 2 → Cell := twoBank p3908 ray3908
theorem signs3908 : ∀ j, Signs p3908 (bank3908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3909 := params 4
abbrev ray3909 := rays 4
def bank3909 : Fin 2 → Cell := twoBank p3909 ray3909
theorem signs3909 : ∀ j, Signs p3909 (bank3909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3910 := params 5
abbrev ray3910 := rays 5
def bank3910 : Fin 2 → Cell := twoBank p3910 ray3910
theorem signs3910 : ∀ j, Signs p3910 (bank3910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3911 := params 6
abbrev ray3911 := rays 6
def bank3911 : Fin 2 → Cell := twoBank p3911 ray3911
theorem signs3911 : ∀ j, Signs p3911 (bank3911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3912 := params 7
abbrev ray3912 := rays 7
def bank3912 : Fin 2 → Cell := twoBank p3912 ray3912
theorem signs3912 : ∀ j, Signs p3912 (bank3912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3913 := params 8
abbrev ray3913 := rays 8
def bank3913 : Fin 2 → Cell := twoBank p3913 ray3913
theorem signs3913 : ∀ j, Signs p3913 (bank3913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3914 := params 9
abbrev ray3914 := rays 9
def bank3914 : Fin 2 → Cell := twoBank p3914 ray3914
theorem signs3914 : ∀ j, Signs p3914 (bank3914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3915 := params 10
abbrev ray3915 := rays 10
def bank3915 : Fin 2 → Cell := twoBank p3915 ray3915
theorem signs3915 : ∀ j, Signs p3915 (bank3915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3916 := params 11
abbrev ray3916 := rays 11
def bank3916 : Fin 2 → Cell := twoBank p3916 ray3916
theorem signs3916 : ∀ j, Signs p3916 (bank3916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3917 := params 12
abbrev ray3917 := rays 12
def bank3917 : Fin 2 → Cell := twoBank p3917 ray3917
theorem signs3917 : ∀ j, Signs p3917 (bank3917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3918 := params 13
abbrev ray3918 := rays 13
def bank3918 : Fin 2 → Cell := twoBank p3918 ray3918
theorem signs3918 : ∀ j, Signs p3918 (bank3918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3919 := params 14
abbrev ray3919 := rays 14
def bank3919 : Fin 2 → Cell := twoBank p3919 ray3919
theorem signs3919 : ∀ j, Signs p3919 (bank3919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3920 := params 15
abbrev ray3920 := rays 15
def bank3920 : Fin 2 → Cell := twoBank p3920 ray3920
theorem signs3920 : ∀ j, Signs p3920 (bank3920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3921 := params 16
abbrev ray3921 := rays 16
def bank3921 : Fin 2 → Cell := twoBank p3921 ray3921
theorem signs3921 : ∀ j, Signs p3921 (bank3921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3922 := params 17
abbrev ray3922 := rays 17
def bank3922 : Fin 2 → Cell := twoBank p3922 ray3922
theorem signs3922 : ∀ j, Signs p3922 (bank3922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3923 := params 18
abbrev ray3923 := rays 18
def bank3923 : Fin 2 → Cell := twoBank p3923 ray3923
theorem signs3923 : ∀ j, Signs p3923 (bank3923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3924 := params 19
abbrev ray3924 := rays 19
def bank3924 : Fin 2 → Cell := twoBank p3924 ray3924
theorem signs3924 : ∀ j, Signs p3924 (bank3924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3925 := params 20
abbrev ray3925 := rays 20
def bank3925 : Fin 2 → Cell := twoBank p3925 ray3925
theorem signs3925 : ∀ j, Signs p3925 (bank3925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3926 := params 21
abbrev ray3926 := rays 21
def bank3926 : Fin 2 → Cell := twoBank p3926 ray3926
theorem signs3926 : ∀ j, Signs p3926 (bank3926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3927 := params 22
abbrev ray3927 := rays 22
def bank3927 : Fin 2 → Cell := twoBank p3927 ray3927
theorem signs3927 : ∀ j, Signs p3927 (bank3927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3928 := params 23
abbrev ray3928 := rays 23
def bank3928 : Fin 2 → Cell := twoBank p3928 ray3928
theorem signs3928 : ∀ j, Signs p3928 (bank3928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3929 := params 24
abbrev ray3929 := rays 24
def bank3929 : Fin 2 → Cell := twoBank p3929 ray3929
theorem signs3929 : ∀ j, Signs p3929 (bank3929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3930 := params 25
abbrev ray3930 := rays 25
def bank3930 : Fin 2 → Cell := twoBank p3930 ray3930
theorem signs3930 : ∀ j, Signs p3930 (bank3930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3931 := params 26
abbrev ray3931 := rays 26
def bank3931 : Fin 2 → Cell := twoBank p3931 ray3931
theorem signs3931 : ∀ j, Signs p3931 (bank3931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3932 := params 27
abbrev ray3932 := rays 27
def bank3932 : Fin 2 → Cell := twoBank p3932 ray3932
theorem signs3932 : ∀ j, Signs p3932 (bank3932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3933 := params 28
abbrev ray3933 := rays 28
def bank3933 : Fin 2 → Cell := twoBank p3933 ray3933
theorem signs3933 : ∀ j, Signs p3933 (bank3933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3934 := params 29
abbrev ray3934 := rays 29
def bank3934 : Fin 2 → Cell := twoBank p3934 ray3934
theorem signs3934 : ∀ j, Signs p3934 (bank3934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3935 := params 30
abbrev ray3935 := rays 30
def bank3935 : Fin 2 → Cell := twoBank p3935 ray3935
theorem signs3935 : ∀ j, Signs p3935 (bank3935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3936 := params 31
abbrev ray3936 := rays 31
def bank3936 : Fin 2 → Cell := twoBank p3936 ray3936
theorem signs3936 : ∀ j, Signs p3936 (bank3936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03905_03936
