/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05985_06016
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98771360708999,98771081005053,98770801277930,98770521527631,98770241754156,98769961957507,98769682137684,98769402294689,98769122428522,98768842539184,98768562626676,98768282690999,98768002732154,98767722750142,98767442744963,98767162716619,98766882665110,98766602590437,98766322492602,98766042371605,98765762227446,98765482060127,98765201869649,98764921656012,98764641419218,98764361159267,98764080876160,98763800569899,98763520240484,98763239887915,98762959512194,98762679113322,98762398691299]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5984+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5985 := params 0
abbrev ray5985 := rays 0
def bank5985 : Fin 2 → Cell := twoBank p5985 ray5985
theorem signs5985 : ∀ j, Signs p5985 (bank5985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5986 := params 1
abbrev ray5986 := rays 1
def bank5986 : Fin 2 → Cell := twoBank p5986 ray5986
theorem signs5986 : ∀ j, Signs p5986 (bank5986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5987 := params 2
abbrev ray5987 := rays 2
def bank5987 : Fin 2 → Cell := twoBank p5987 ray5987
theorem signs5987 : ∀ j, Signs p5987 (bank5987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5988 := params 3
abbrev ray5988 := rays 3
def bank5988 : Fin 2 → Cell := twoBank p5988 ray5988
theorem signs5988 : ∀ j, Signs p5988 (bank5988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5989 := params 4
abbrev ray5989 := rays 4
def bank5989 : Fin 2 → Cell := twoBank p5989 ray5989
theorem signs5989 : ∀ j, Signs p5989 (bank5989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5990 := params 5
abbrev ray5990 := rays 5
def bank5990 : Fin 2 → Cell := twoBank p5990 ray5990
theorem signs5990 : ∀ j, Signs p5990 (bank5990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5991 := params 6
abbrev ray5991 := rays 6
def bank5991 : Fin 2 → Cell := twoBank p5991 ray5991
theorem signs5991 : ∀ j, Signs p5991 (bank5991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5992 := params 7
abbrev ray5992 := rays 7
def bank5992 : Fin 2 → Cell := twoBank p5992 ray5992
theorem signs5992 : ∀ j, Signs p5992 (bank5992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5993 := params 8
abbrev ray5993 := rays 8
def bank5993 : Fin 2 → Cell := twoBank p5993 ray5993
theorem signs5993 : ∀ j, Signs p5993 (bank5993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5994 := params 9
abbrev ray5994 := rays 9
def bank5994 : Fin 2 → Cell := twoBank p5994 ray5994
theorem signs5994 : ∀ j, Signs p5994 (bank5994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5995 := params 10
abbrev ray5995 := rays 10
def bank5995 : Fin 2 → Cell := twoBank p5995 ray5995
theorem signs5995 : ∀ j, Signs p5995 (bank5995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5996 := params 11
abbrev ray5996 := rays 11
def bank5996 : Fin 2 → Cell := twoBank p5996 ray5996
theorem signs5996 : ∀ j, Signs p5996 (bank5996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5997 := params 12
abbrev ray5997 := rays 12
def bank5997 : Fin 2 → Cell := twoBank p5997 ray5997
theorem signs5997 : ∀ j, Signs p5997 (bank5997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5998 := params 13
abbrev ray5998 := rays 13
def bank5998 : Fin 2 → Cell := twoBank p5998 ray5998
theorem signs5998 : ∀ j, Signs p5998 (bank5998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5999 := params 14
abbrev ray5999 := rays 14
def bank5999 : Fin 2 → Cell := twoBank p5999 ray5999
theorem signs5999 : ∀ j, Signs p5999 (bank5999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6000 := params 15
abbrev ray6000 := rays 15
def bank6000 : Fin 2 → Cell := twoBank p6000 ray6000
theorem signs6000 : ∀ j, Signs p6000 (bank6000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6001 := params 16
abbrev ray6001 := rays 16
def bank6001 : Fin 2 → Cell := twoBank p6001 ray6001
theorem signs6001 : ∀ j, Signs p6001 (bank6001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6002 := params 17
abbrev ray6002 := rays 17
def bank6002 : Fin 2 → Cell := twoBank p6002 ray6002
theorem signs6002 : ∀ j, Signs p6002 (bank6002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6003 := params 18
abbrev ray6003 := rays 18
def bank6003 : Fin 2 → Cell := twoBank p6003 ray6003
theorem signs6003 : ∀ j, Signs p6003 (bank6003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6004 := params 19
abbrev ray6004 := rays 19
def bank6004 : Fin 2 → Cell := twoBank p6004 ray6004
theorem signs6004 : ∀ j, Signs p6004 (bank6004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6005 := params 20
abbrev ray6005 := rays 20
def bank6005 : Fin 2 → Cell := twoBank p6005 ray6005
theorem signs6005 : ∀ j, Signs p6005 (bank6005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6006 := params 21
abbrev ray6006 := rays 21
def bank6006 : Fin 2 → Cell := twoBank p6006 ray6006
theorem signs6006 : ∀ j, Signs p6006 (bank6006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6007 := params 22
abbrev ray6007 := rays 22
def bank6007 : Fin 2 → Cell := twoBank p6007 ray6007
theorem signs6007 : ∀ j, Signs p6007 (bank6007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6008 := params 23
abbrev ray6008 := rays 23
def bank6008 : Fin 2 → Cell := twoBank p6008 ray6008
theorem signs6008 : ∀ j, Signs p6008 (bank6008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6009 := params 24
abbrev ray6009 := rays 24
def bank6009 : Fin 2 → Cell := twoBank p6009 ray6009
theorem signs6009 : ∀ j, Signs p6009 (bank6009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6010 := params 25
abbrev ray6010 := rays 25
def bank6010 : Fin 2 → Cell := twoBank p6010 ray6010
theorem signs6010 : ∀ j, Signs p6010 (bank6010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6011 := params 26
abbrev ray6011 := rays 26
def bank6011 : Fin 2 → Cell := twoBank p6011 ray6011
theorem signs6011 : ∀ j, Signs p6011 (bank6011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6012 := params 27
abbrev ray6012 := rays 27
def bank6012 : Fin 2 → Cell := twoBank p6012 ray6012
theorem signs6012 : ∀ j, Signs p6012 (bank6012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6013 := params 28
abbrev ray6013 := rays 28
def bank6013 : Fin 2 → Cell := twoBank p6013 ray6013
theorem signs6013 : ∀ j, Signs p6013 (bank6013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6014 := params 29
abbrev ray6014 := rays 29
def bank6014 : Fin 2 → Cell := twoBank p6014 ray6014
theorem signs6014 : ∀ j, Signs p6014 (bank6014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6015 := params 30
abbrev ray6015 := rays 30
def bank6015 : Fin 2 → Cell := twoBank p6015 ray6015
theorem signs6015 : ∀ j, Signs p6015 (bank6015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6016 := params 31
abbrev ray6016 := rays 31
def bank6016 : Fin 2 → Cell := twoBank p6016 ray6016
theorem signs6016 : ∀ j, Signs p6016 (bank6016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05985_06016
