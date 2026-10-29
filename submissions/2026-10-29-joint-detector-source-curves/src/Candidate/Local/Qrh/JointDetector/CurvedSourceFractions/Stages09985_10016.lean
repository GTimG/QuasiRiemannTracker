/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09985_10016
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97475612806730,97475246496097,97474880165119,97474513813796,97474147442128,97473781050116,97473414637761,97473048205063,97472681752023,97472315278641,97471948784918,97471582270854,97471215736450,97470849181707,97470482606625,97470116011204,97469749395445,97469382759349,97469016102916,97468649426147,97468282729043,97467916011604,97467549273830,97467182515722,97466815737281,97466448938507,97466082119400,97465715279962,97465348420192,97464981540092,97464614639662,97464247718902,97463880777813]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9984+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9985 := params 0
abbrev ray9985 := rays 0
def bank9985 : Fin 2 → Cell := twoBank p9985 ray9985
theorem signs9985 : ∀ j, Signs p9985 (bank9985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9986 := params 1
abbrev ray9986 := rays 1
def bank9986 : Fin 2 → Cell := twoBank p9986 ray9986
theorem signs9986 : ∀ j, Signs p9986 (bank9986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9987 := params 2
abbrev ray9987 := rays 2
def bank9987 : Fin 2 → Cell := twoBank p9987 ray9987
theorem signs9987 : ∀ j, Signs p9987 (bank9987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9988 := params 3
abbrev ray9988 := rays 3
def bank9988 : Fin 2 → Cell := twoBank p9988 ray9988
theorem signs9988 : ∀ j, Signs p9988 (bank9988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9989 := params 4
abbrev ray9989 := rays 4
def bank9989 : Fin 2 → Cell := twoBank p9989 ray9989
theorem signs9989 : ∀ j, Signs p9989 (bank9989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9990 := params 5
abbrev ray9990 := rays 5
def bank9990 : Fin 2 → Cell := twoBank p9990 ray9990
theorem signs9990 : ∀ j, Signs p9990 (bank9990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9991 := params 6
abbrev ray9991 := rays 6
def bank9991 : Fin 2 → Cell := twoBank p9991 ray9991
theorem signs9991 : ∀ j, Signs p9991 (bank9991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9992 := params 7
abbrev ray9992 := rays 7
def bank9992 : Fin 2 → Cell := twoBank p9992 ray9992
theorem signs9992 : ∀ j, Signs p9992 (bank9992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9993 := params 8
abbrev ray9993 := rays 8
def bank9993 : Fin 2 → Cell := twoBank p9993 ray9993
theorem signs9993 : ∀ j, Signs p9993 (bank9993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9994 := params 9
abbrev ray9994 := rays 9
def bank9994 : Fin 2 → Cell := twoBank p9994 ray9994
theorem signs9994 : ∀ j, Signs p9994 (bank9994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9995 := params 10
abbrev ray9995 := rays 10
def bank9995 : Fin 2 → Cell := twoBank p9995 ray9995
theorem signs9995 : ∀ j, Signs p9995 (bank9995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9996 := params 11
abbrev ray9996 := rays 11
def bank9996 : Fin 2 → Cell := twoBank p9996 ray9996
theorem signs9996 : ∀ j, Signs p9996 (bank9996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9997 := params 12
abbrev ray9997 := rays 12
def bank9997 : Fin 2 → Cell := twoBank p9997 ray9997
theorem signs9997 : ∀ j, Signs p9997 (bank9997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9998 := params 13
abbrev ray9998 := rays 13
def bank9998 : Fin 2 → Cell := twoBank p9998 ray9998
theorem signs9998 : ∀ j, Signs p9998 (bank9998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9999 := params 14
abbrev ray9999 := rays 14
def bank9999 : Fin 2 → Cell := twoBank p9999 ray9999
theorem signs9999 : ∀ j, Signs p9999 (bank9999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10000 := params 15
abbrev ray10000 := rays 15
def bank10000 : Fin 2 → Cell := twoBank p10000 ray10000
theorem signs10000 : ∀ j, Signs p10000 (bank10000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10001 := params 16
abbrev ray10001 := rays 16
def bank10001 : Fin 2 → Cell := twoBank p10001 ray10001
theorem signs10001 : ∀ j, Signs p10001 (bank10001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10002 := params 17
abbrev ray10002 := rays 17
def bank10002 : Fin 2 → Cell := twoBank p10002 ray10002
theorem signs10002 : ∀ j, Signs p10002 (bank10002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10003 := params 18
abbrev ray10003 := rays 18
def bank10003 : Fin 2 → Cell := twoBank p10003 ray10003
theorem signs10003 : ∀ j, Signs p10003 (bank10003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10004 := params 19
abbrev ray10004 := rays 19
def bank10004 : Fin 2 → Cell := twoBank p10004 ray10004
theorem signs10004 : ∀ j, Signs p10004 (bank10004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10005 := params 20
abbrev ray10005 := rays 20
def bank10005 : Fin 2 → Cell := twoBank p10005 ray10005
theorem signs10005 : ∀ j, Signs p10005 (bank10005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10006 := params 21
abbrev ray10006 := rays 21
def bank10006 : Fin 2 → Cell := twoBank p10006 ray10006
theorem signs10006 : ∀ j, Signs p10006 (bank10006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10007 := params 22
abbrev ray10007 := rays 22
def bank10007 : Fin 2 → Cell := twoBank p10007 ray10007
theorem signs10007 : ∀ j, Signs p10007 (bank10007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10008 := params 23
abbrev ray10008 := rays 23
def bank10008 : Fin 2 → Cell := twoBank p10008 ray10008
theorem signs10008 : ∀ j, Signs p10008 (bank10008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10009 := params 24
abbrev ray10009 := rays 24
def bank10009 : Fin 2 → Cell := twoBank p10009 ray10009
theorem signs10009 : ∀ j, Signs p10009 (bank10009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10010 := params 25
abbrev ray10010 := rays 25
def bank10010 : Fin 2 → Cell := twoBank p10010 ray10010
theorem signs10010 : ∀ j, Signs p10010 (bank10010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10011 := params 26
abbrev ray10011 := rays 26
def bank10011 : Fin 2 → Cell := twoBank p10011 ray10011
theorem signs10011 : ∀ j, Signs p10011 (bank10011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10012 := params 27
abbrev ray10012 := rays 27
def bank10012 : Fin 2 → Cell := twoBank p10012 ray10012
theorem signs10012 : ∀ j, Signs p10012 (bank10012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10013 := params 28
abbrev ray10013 := rays 28
def bank10013 : Fin 2 → Cell := twoBank p10013 ray10013
theorem signs10013 : ∀ j, Signs p10013 (bank10013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10014 := params 29
abbrev ray10014 := rays 29
def bank10014 : Fin 2 → Cell := twoBank p10014 ray10014
theorem signs10014 : ∀ j, Signs p10014 (bank10014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10015 := params 30
abbrev ray10015 := rays 30
def bank10015 : Fin 2 → Cell := twoBank p10015 ray10015
theorem signs10015 : ∀ j, Signs p10015 (bank10015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10016 := params 31
abbrev ray10016 := rays 31
def bank10016 : Fin 2 → Cell := twoBank p10016 ray10016
theorem signs10016 : ∀ j, Signs p10016 (bank10016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09985_10016
