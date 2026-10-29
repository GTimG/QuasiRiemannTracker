/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10977_11008
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97102319386769,97101933155312,97101546904028,97101160632917,97100774341980,97100388031217,97100001700629,97099615350216,97099228979979,97098842589918,97098456180034,97098069750327,97097683300797,97097296831446,97096910342273,97096523833279,97096137304465,97095750755831,97095364187378,97094977599106,97094590991015,97094204363107,97093817715381,97093431047838,97093044360479,97092657653304,97092270926313,97091884179507,97091497412887,97091110626453,97090723820205,97090336994144,97089950148271]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10976+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10977 := params 0
abbrev ray10977 := rays 0
def bank10977 : Fin 2 → Cell := twoBank p10977 ray10977
theorem signs10977 : ∀ j, Signs p10977 (bank10977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10978 := params 1
abbrev ray10978 := rays 1
def bank10978 : Fin 2 → Cell := twoBank p10978 ray10978
theorem signs10978 : ∀ j, Signs p10978 (bank10978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10979 := params 2
abbrev ray10979 := rays 2
def bank10979 : Fin 2 → Cell := twoBank p10979 ray10979
theorem signs10979 : ∀ j, Signs p10979 (bank10979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10980 := params 3
abbrev ray10980 := rays 3
def bank10980 : Fin 2 → Cell := twoBank p10980 ray10980
theorem signs10980 : ∀ j, Signs p10980 (bank10980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10981 := params 4
abbrev ray10981 := rays 4
def bank10981 : Fin 2 → Cell := twoBank p10981 ray10981
theorem signs10981 : ∀ j, Signs p10981 (bank10981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10982 := params 5
abbrev ray10982 := rays 5
def bank10982 : Fin 2 → Cell := twoBank p10982 ray10982
theorem signs10982 : ∀ j, Signs p10982 (bank10982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10983 := params 6
abbrev ray10983 := rays 6
def bank10983 : Fin 2 → Cell := twoBank p10983 ray10983
theorem signs10983 : ∀ j, Signs p10983 (bank10983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10984 := params 7
abbrev ray10984 := rays 7
def bank10984 : Fin 2 → Cell := twoBank p10984 ray10984
theorem signs10984 : ∀ j, Signs p10984 (bank10984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10985 := params 8
abbrev ray10985 := rays 8
def bank10985 : Fin 2 → Cell := twoBank p10985 ray10985
theorem signs10985 : ∀ j, Signs p10985 (bank10985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10986 := params 9
abbrev ray10986 := rays 9
def bank10986 : Fin 2 → Cell := twoBank p10986 ray10986
theorem signs10986 : ∀ j, Signs p10986 (bank10986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10987 := params 10
abbrev ray10987 := rays 10
def bank10987 : Fin 2 → Cell := twoBank p10987 ray10987
theorem signs10987 : ∀ j, Signs p10987 (bank10987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10988 := params 11
abbrev ray10988 := rays 11
def bank10988 : Fin 2 → Cell := twoBank p10988 ray10988
theorem signs10988 : ∀ j, Signs p10988 (bank10988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10989 := params 12
abbrev ray10989 := rays 12
def bank10989 : Fin 2 → Cell := twoBank p10989 ray10989
theorem signs10989 : ∀ j, Signs p10989 (bank10989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10990 := params 13
abbrev ray10990 := rays 13
def bank10990 : Fin 2 → Cell := twoBank p10990 ray10990
theorem signs10990 : ∀ j, Signs p10990 (bank10990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10991 := params 14
abbrev ray10991 := rays 14
def bank10991 : Fin 2 → Cell := twoBank p10991 ray10991
theorem signs10991 : ∀ j, Signs p10991 (bank10991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10992 := params 15
abbrev ray10992 := rays 15
def bank10992 : Fin 2 → Cell := twoBank p10992 ray10992
theorem signs10992 : ∀ j, Signs p10992 (bank10992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10993 := params 16
abbrev ray10993 := rays 16
def bank10993 : Fin 2 → Cell := twoBank p10993 ray10993
theorem signs10993 : ∀ j, Signs p10993 (bank10993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10994 := params 17
abbrev ray10994 := rays 17
def bank10994 : Fin 2 → Cell := twoBank p10994 ray10994
theorem signs10994 : ∀ j, Signs p10994 (bank10994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10995 := params 18
abbrev ray10995 := rays 18
def bank10995 : Fin 2 → Cell := twoBank p10995 ray10995
theorem signs10995 : ∀ j, Signs p10995 (bank10995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10996 := params 19
abbrev ray10996 := rays 19
def bank10996 : Fin 2 → Cell := twoBank p10996 ray10996
theorem signs10996 : ∀ j, Signs p10996 (bank10996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10997 := params 20
abbrev ray10997 := rays 20
def bank10997 : Fin 2 → Cell := twoBank p10997 ray10997
theorem signs10997 : ∀ j, Signs p10997 (bank10997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10998 := params 21
abbrev ray10998 := rays 21
def bank10998 : Fin 2 → Cell := twoBank p10998 ray10998
theorem signs10998 : ∀ j, Signs p10998 (bank10998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10999 := params 22
abbrev ray10999 := rays 22
def bank10999 : Fin 2 → Cell := twoBank p10999 ray10999
theorem signs10999 : ∀ j, Signs p10999 (bank10999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11000 := params 23
abbrev ray11000 := rays 23
def bank11000 : Fin 2 → Cell := twoBank p11000 ray11000
theorem signs11000 : ∀ j, Signs p11000 (bank11000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11001 := params 24
abbrev ray11001 := rays 24
def bank11001 : Fin 2 → Cell := twoBank p11001 ray11001
theorem signs11001 : ∀ j, Signs p11001 (bank11001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11002 := params 25
abbrev ray11002 := rays 25
def bank11002 : Fin 2 → Cell := twoBank p11002 ray11002
theorem signs11002 : ∀ j, Signs p11002 (bank11002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11003 := params 26
abbrev ray11003 := rays 26
def bank11003 : Fin 2 → Cell := twoBank p11003 ray11003
theorem signs11003 : ∀ j, Signs p11003 (bank11003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11004 := params 27
abbrev ray11004 := rays 27
def bank11004 : Fin 2 → Cell := twoBank p11004 ray11004
theorem signs11004 : ∀ j, Signs p11004 (bank11004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11005 := params 28
abbrev ray11005 := rays 28
def bank11005 : Fin 2 → Cell := twoBank p11005 ray11005
theorem signs11005 : ∀ j, Signs p11005 (bank11005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11006 := params 29
abbrev ray11006 := rays 29
def bank11006 : Fin 2 → Cell := twoBank p11006 ray11006
theorem signs11006 : ∀ j, Signs p11006 (bank11006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11007 := params 30
abbrev ray11007 := rays 30
def bank11007 : Fin 2 → Cell := twoBank p11007 ray11007
theorem signs11007 : ∀ j, Signs p11007 (bank11007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11008 := params 31
abbrev ray11008 := rays 31
def bank11008 : Fin 2 → Cell := twoBank p11008 ray11008
theorem signs11008 : ∀ j, Signs p11008 (bank11008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10977_11008
