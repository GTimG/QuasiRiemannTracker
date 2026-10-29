/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13985_14016
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95854675167997,95854234207536,95853793230859,95853352237965,95852911228855,95852470203529,95852029161987,95851588104229,95851147030255,95850705940066,95850264833662,95849823711043,95849382572209,95848941417160,95848500245897,95848059058420,95847617854728,95847176634823,95846735398704,95846294146371,95845852877825,95845411593066,95844970292094,95844528974909,95844087641511,95843646291901,95843204926079,95842763544045,95842322145799,95841880731341,95841439300672,95840997853791,95840556390699]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13984+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13985 := params 0
abbrev ray13985 := rays 0
def bank13985 : Fin 1 → Cell := oneBank p13985 ray13985
theorem signs13985 : ∀ j, Signs p13985 (bank13985 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13986 := params 1
abbrev ray13986 := rays 1
def bank13986 : Fin 1 → Cell := oneBank p13986 ray13986
theorem signs13986 : ∀ j, Signs p13986 (bank13986 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13987 := params 2
abbrev ray13987 := rays 2
def bank13987 : Fin 1 → Cell := oneBank p13987 ray13987
theorem signs13987 : ∀ j, Signs p13987 (bank13987 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13988 := params 3
abbrev ray13988 := rays 3
def bank13988 : Fin 1 → Cell := oneBank p13988 ray13988
theorem signs13988 : ∀ j, Signs p13988 (bank13988 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13989 := params 4
abbrev ray13989 := rays 4
def bank13989 : Fin 1 → Cell := oneBank p13989 ray13989
theorem signs13989 : ∀ j, Signs p13989 (bank13989 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13990 := params 5
abbrev ray13990 := rays 5
def bank13990 : Fin 1 → Cell := oneBank p13990 ray13990
theorem signs13990 : ∀ j, Signs p13990 (bank13990 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13991 := params 6
abbrev ray13991 := rays 6
def bank13991 : Fin 1 → Cell := oneBank p13991 ray13991
theorem signs13991 : ∀ j, Signs p13991 (bank13991 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13992 := params 7
abbrev ray13992 := rays 7
def bank13992 : Fin 1 → Cell := oneBank p13992 ray13992
theorem signs13992 : ∀ j, Signs p13992 (bank13992 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13993 := params 8
abbrev ray13993 := rays 8
def bank13993 : Fin 1 → Cell := oneBank p13993 ray13993
theorem signs13993 : ∀ j, Signs p13993 (bank13993 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13994 := params 9
abbrev ray13994 := rays 9
def bank13994 : Fin 1 → Cell := oneBank p13994 ray13994
theorem signs13994 : ∀ j, Signs p13994 (bank13994 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13995 := params 10
abbrev ray13995 := rays 10
def bank13995 : Fin 1 → Cell := oneBank p13995 ray13995
theorem signs13995 : ∀ j, Signs p13995 (bank13995 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13996 := params 11
abbrev ray13996 := rays 11
def bank13996 : Fin 1 → Cell := oneBank p13996 ray13996
theorem signs13996 : ∀ j, Signs p13996 (bank13996 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13997 := params 12
abbrev ray13997 := rays 12
def bank13997 : Fin 1 → Cell := oneBank p13997 ray13997
theorem signs13997 : ∀ j, Signs p13997 (bank13997 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13998 := params 13
abbrev ray13998 := rays 13
def bank13998 : Fin 1 → Cell := oneBank p13998 ray13998
theorem signs13998 : ∀ j, Signs p13998 (bank13998 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13999 := params 14
abbrev ray13999 := rays 14
def bank13999 : Fin 1 → Cell := oneBank p13999 ray13999
theorem signs13999 : ∀ j, Signs p13999 (bank13999 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14000 := params 15
abbrev ray14000 := rays 15
def bank14000 : Fin 1 → Cell := oneBank p14000 ray14000
theorem signs14000 : ∀ j, Signs p14000 (bank14000 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14001 := params 16
abbrev ray14001 := rays 16
def bank14001 : Fin 1 → Cell := oneBank p14001 ray14001
theorem signs14001 : ∀ j, Signs p14001 (bank14001 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14002 := params 17
abbrev ray14002 := rays 17
def bank14002 : Fin 1 → Cell := oneBank p14002 ray14002
theorem signs14002 : ∀ j, Signs p14002 (bank14002 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14003 := params 18
abbrev ray14003 := rays 18
def bank14003 : Fin 1 → Cell := oneBank p14003 ray14003
theorem signs14003 : ∀ j, Signs p14003 (bank14003 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14004 := params 19
abbrev ray14004 := rays 19
def bank14004 : Fin 1 → Cell := oneBank p14004 ray14004
theorem signs14004 : ∀ j, Signs p14004 (bank14004 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14005 := params 20
abbrev ray14005 := rays 20
def bank14005 : Fin 1 → Cell := oneBank p14005 ray14005
theorem signs14005 : ∀ j, Signs p14005 (bank14005 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14006 := params 21
abbrev ray14006 := rays 21
def bank14006 : Fin 1 → Cell := oneBank p14006 ray14006
theorem signs14006 : ∀ j, Signs p14006 (bank14006 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14007 := params 22
abbrev ray14007 := rays 22
def bank14007 : Fin 1 → Cell := oneBank p14007 ray14007
theorem signs14007 : ∀ j, Signs p14007 (bank14007 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14008 := params 23
abbrev ray14008 := rays 23
def bank14008 : Fin 1 → Cell := oneBank p14008 ray14008
theorem signs14008 : ∀ j, Signs p14008 (bank14008 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14009 := params 24
abbrev ray14009 := rays 24
def bank14009 : Fin 1 → Cell := oneBank p14009 ray14009
theorem signs14009 : ∀ j, Signs p14009 (bank14009 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14010 := params 25
abbrev ray14010 := rays 25
def bank14010 : Fin 1 → Cell := oneBank p14010 ray14010
theorem signs14010 : ∀ j, Signs p14010 (bank14010 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14011 := params 26
abbrev ray14011 := rays 26
def bank14011 : Fin 1 → Cell := oneBank p14011 ray14011
theorem signs14011 : ∀ j, Signs p14011 (bank14011 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14012 := params 27
abbrev ray14012 := rays 27
def bank14012 : Fin 1 → Cell := oneBank p14012 ray14012
theorem signs14012 : ∀ j, Signs p14012 (bank14012 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14013 := params 28
abbrev ray14013 := rays 28
def bank14013 : Fin 1 → Cell := oneBank p14013 ray14013
theorem signs14013 : ∀ j, Signs p14013 (bank14013 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14014 := params 29
abbrev ray14014 := rays 29
def bank14014 : Fin 1 → Cell := oneBank p14014 ray14014
theorem signs14014 : ∀ j, Signs p14014 (bank14014 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14015 := params 30
abbrev ray14015 := rays 30
def bank14015 : Fin 1 → Cell := oneBank p14015 ray14015
theorem signs14015 : ∀ j, Signs p14015 (bank14015 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14016 := params 31
abbrev ray14016 := rays 31
def bank14016 : Fin 1 → Cell := oneBank p14016 ray14016
theorem signs14016 : ∀ j, Signs p14016 (bank14016 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13985_14016
