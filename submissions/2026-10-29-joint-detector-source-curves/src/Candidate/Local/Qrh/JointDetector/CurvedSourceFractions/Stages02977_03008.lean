/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02977_03008
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99503407847571,99503202399859,99502996925757,99502791425266,99502585898388,99502380345124,99502174765475,99501969159443,99501763527029,99501557868234,99501352183060,99501146471507,99500940733577,99500734969272,99500529178592,99500323361539,99500117518114,99499911648318,99499705752153,99499499829620,99499293880720,99499087905455,99498881903825,99498675875832,99498469821478,99498263740763,99498057633689,99497851500257,99497645340469,99497439154325,99497232941827,99497026702976,99496820437774]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2976+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2977 := params 0
abbrev ray2977 := rays 0
def bank2977 : Fin 2 → Cell := twoBank p2977 ray2977
theorem signs2977 : ∀ j, Signs p2977 (bank2977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2978 := params 1
abbrev ray2978 := rays 1
def bank2978 : Fin 2 → Cell := twoBank p2978 ray2978
theorem signs2978 : ∀ j, Signs p2978 (bank2978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2979 := params 2
abbrev ray2979 := rays 2
def bank2979 : Fin 2 → Cell := twoBank p2979 ray2979
theorem signs2979 : ∀ j, Signs p2979 (bank2979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2980 := params 3
abbrev ray2980 := rays 3
def bank2980 : Fin 2 → Cell := twoBank p2980 ray2980
theorem signs2980 : ∀ j, Signs p2980 (bank2980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2981 := params 4
abbrev ray2981 := rays 4
def bank2981 : Fin 2 → Cell := twoBank p2981 ray2981
theorem signs2981 : ∀ j, Signs p2981 (bank2981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2982 := params 5
abbrev ray2982 := rays 5
def bank2982 : Fin 2 → Cell := twoBank p2982 ray2982
theorem signs2982 : ∀ j, Signs p2982 (bank2982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2983 := params 6
abbrev ray2983 := rays 6
def bank2983 : Fin 2 → Cell := twoBank p2983 ray2983
theorem signs2983 : ∀ j, Signs p2983 (bank2983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2984 := params 7
abbrev ray2984 := rays 7
def bank2984 : Fin 2 → Cell := twoBank p2984 ray2984
theorem signs2984 : ∀ j, Signs p2984 (bank2984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2985 := params 8
abbrev ray2985 := rays 8
def bank2985 : Fin 2 → Cell := twoBank p2985 ray2985
theorem signs2985 : ∀ j, Signs p2985 (bank2985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2986 := params 9
abbrev ray2986 := rays 9
def bank2986 : Fin 2 → Cell := twoBank p2986 ray2986
theorem signs2986 : ∀ j, Signs p2986 (bank2986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2987 := params 10
abbrev ray2987 := rays 10
def bank2987 : Fin 2 → Cell := twoBank p2987 ray2987
theorem signs2987 : ∀ j, Signs p2987 (bank2987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2988 := params 11
abbrev ray2988 := rays 11
def bank2988 : Fin 2 → Cell := twoBank p2988 ray2988
theorem signs2988 : ∀ j, Signs p2988 (bank2988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2989 := params 12
abbrev ray2989 := rays 12
def bank2989 : Fin 2 → Cell := twoBank p2989 ray2989
theorem signs2989 : ∀ j, Signs p2989 (bank2989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2990 := params 13
abbrev ray2990 := rays 13
def bank2990 : Fin 2 → Cell := twoBank p2990 ray2990
theorem signs2990 : ∀ j, Signs p2990 (bank2990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2991 := params 14
abbrev ray2991 := rays 14
def bank2991 : Fin 2 → Cell := twoBank p2991 ray2991
theorem signs2991 : ∀ j, Signs p2991 (bank2991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2992 := params 15
abbrev ray2992 := rays 15
def bank2992 : Fin 2 → Cell := twoBank p2992 ray2992
theorem signs2992 : ∀ j, Signs p2992 (bank2992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2993 := params 16
abbrev ray2993 := rays 16
def bank2993 : Fin 2 → Cell := twoBank p2993 ray2993
theorem signs2993 : ∀ j, Signs p2993 (bank2993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2994 := params 17
abbrev ray2994 := rays 17
def bank2994 : Fin 2 → Cell := twoBank p2994 ray2994
theorem signs2994 : ∀ j, Signs p2994 (bank2994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2995 := params 18
abbrev ray2995 := rays 18
def bank2995 : Fin 2 → Cell := twoBank p2995 ray2995
theorem signs2995 : ∀ j, Signs p2995 (bank2995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2996 := params 19
abbrev ray2996 := rays 19
def bank2996 : Fin 2 → Cell := twoBank p2996 ray2996
theorem signs2996 : ∀ j, Signs p2996 (bank2996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2997 := params 20
abbrev ray2997 := rays 20
def bank2997 : Fin 2 → Cell := twoBank p2997 ray2997
theorem signs2997 : ∀ j, Signs p2997 (bank2997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2998 := params 21
abbrev ray2998 := rays 21
def bank2998 : Fin 2 → Cell := twoBank p2998 ray2998
theorem signs2998 : ∀ j, Signs p2998 (bank2998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2999 := params 22
abbrev ray2999 := rays 22
def bank2999 : Fin 2 → Cell := twoBank p2999 ray2999
theorem signs2999 : ∀ j, Signs p2999 (bank2999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3000 := params 23
abbrev ray3000 := rays 23
def bank3000 : Fin 2 → Cell := twoBank p3000 ray3000
theorem signs3000 : ∀ j, Signs p3000 (bank3000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3001 := params 24
abbrev ray3001 := rays 24
def bank3001 : Fin 2 → Cell := twoBank p3001 ray3001
theorem signs3001 : ∀ j, Signs p3001 (bank3001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3002 := params 25
abbrev ray3002 := rays 25
def bank3002 : Fin 2 → Cell := twoBank p3002 ray3002
theorem signs3002 : ∀ j, Signs p3002 (bank3002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3003 := params 26
abbrev ray3003 := rays 26
def bank3003 : Fin 2 → Cell := twoBank p3003 ray3003
theorem signs3003 : ∀ j, Signs p3003 (bank3003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3004 := params 27
abbrev ray3004 := rays 27
def bank3004 : Fin 2 → Cell := twoBank p3004 ray3004
theorem signs3004 : ∀ j, Signs p3004 (bank3004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3005 := params 28
abbrev ray3005 := rays 28
def bank3005 : Fin 2 → Cell := twoBank p3005 ray3005
theorem signs3005 : ∀ j, Signs p3005 (bank3005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3006 := params 29
abbrev ray3006 := rays 29
def bank3006 : Fin 2 → Cell := twoBank p3006 ray3006
theorem signs3006 : ∀ j, Signs p3006 (bank3006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3007 := params 30
abbrev ray3007 := rays 30
def bank3007 : Fin 2 → Cell := twoBank p3007 ray3007
theorem signs3007 : ∀ j, Signs p3007 (bank3007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3008 := params 31
abbrev ray3008 := rays 31
def bank3008 : Fin 2 → Cell := twoBank p3008 ray3008
theorem signs3008 : ∀ j, Signs p3008 (bank3008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02977_03008
