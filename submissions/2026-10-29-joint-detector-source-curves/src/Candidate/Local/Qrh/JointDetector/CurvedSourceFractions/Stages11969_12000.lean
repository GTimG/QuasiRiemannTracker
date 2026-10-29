/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11969_12000
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96709509297211,96709103629026,96708697941472,96708292234550,96707886508260,96707480762602,96707074997577,96706669213185,96706263409427,96705857586303,96705451743814,96705045881960,96704640000741,96704234100158,96703828180212,96703422240902,96703016282230,96702610304195,96702204306798,96701798290040,96701392253921,96700986198441,96700580123601,96700174029401,96699767915842,96699361782924,96698955630647,96698549459012,96698143268020,96697737057671,96697330827965,96696924578902,96696518310484]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11968+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11969 := params 0
abbrev ray11969 := rays 0
def bank11969 : Fin 2 → Cell := twoBank p11969 ray11969
theorem signs11969 : ∀ j, Signs p11969 (bank11969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11970 := params 1
abbrev ray11970 := rays 1
def bank11970 : Fin 2 → Cell := twoBank p11970 ray11970
theorem signs11970 : ∀ j, Signs p11970 (bank11970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11971 := params 2
abbrev ray11971 := rays 2
def bank11971 : Fin 2 → Cell := twoBank p11971 ray11971
theorem signs11971 : ∀ j, Signs p11971 (bank11971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11972 := params 3
abbrev ray11972 := rays 3
def bank11972 : Fin 2 → Cell := twoBank p11972 ray11972
theorem signs11972 : ∀ j, Signs p11972 (bank11972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11973 := params 4
abbrev ray11973 := rays 4
def bank11973 : Fin 2 → Cell := twoBank p11973 ray11973
theorem signs11973 : ∀ j, Signs p11973 (bank11973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11974 := params 5
abbrev ray11974 := rays 5
def bank11974 : Fin 2 → Cell := twoBank p11974 ray11974
theorem signs11974 : ∀ j, Signs p11974 (bank11974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11975 := params 6
abbrev ray11975 := rays 6
def bank11975 : Fin 2 → Cell := twoBank p11975 ray11975
theorem signs11975 : ∀ j, Signs p11975 (bank11975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11976 := params 7
abbrev ray11976 := rays 7
def bank11976 : Fin 2 → Cell := twoBank p11976 ray11976
theorem signs11976 : ∀ j, Signs p11976 (bank11976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11977 := params 8
abbrev ray11977 := rays 8
def bank11977 : Fin 2 → Cell := twoBank p11977 ray11977
theorem signs11977 : ∀ j, Signs p11977 (bank11977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11978 := params 9
abbrev ray11978 := rays 9
def bank11978 : Fin 2 → Cell := twoBank p11978 ray11978
theorem signs11978 : ∀ j, Signs p11978 (bank11978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11979 := params 10
abbrev ray11979 := rays 10
def bank11979 : Fin 2 → Cell := twoBank p11979 ray11979
theorem signs11979 : ∀ j, Signs p11979 (bank11979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11980 := params 11
abbrev ray11980 := rays 11
def bank11980 : Fin 2 → Cell := twoBank p11980 ray11980
theorem signs11980 : ∀ j, Signs p11980 (bank11980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11981 := params 12
abbrev ray11981 := rays 12
def bank11981 : Fin 2 → Cell := twoBank p11981 ray11981
theorem signs11981 : ∀ j, Signs p11981 (bank11981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11982 := params 13
abbrev ray11982 := rays 13
def bank11982 : Fin 2 → Cell := twoBank p11982 ray11982
theorem signs11982 : ∀ j, Signs p11982 (bank11982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11983 := params 14
abbrev ray11983 := rays 14
def bank11983 : Fin 2 → Cell := twoBank p11983 ray11983
theorem signs11983 : ∀ j, Signs p11983 (bank11983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11984 := params 15
abbrev ray11984 := rays 15
def bank11984 : Fin 2 → Cell := twoBank p11984 ray11984
theorem signs11984 : ∀ j, Signs p11984 (bank11984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11985 := params 16
abbrev ray11985 := rays 16
def bank11985 : Fin 2 → Cell := twoBank p11985 ray11985
theorem signs11985 : ∀ j, Signs p11985 (bank11985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11986 := params 17
abbrev ray11986 := rays 17
def bank11986 : Fin 2 → Cell := twoBank p11986 ray11986
theorem signs11986 : ∀ j, Signs p11986 (bank11986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11987 := params 18
abbrev ray11987 := rays 18
def bank11987 : Fin 2 → Cell := twoBank p11987 ray11987
theorem signs11987 : ∀ j, Signs p11987 (bank11987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11988 := params 19
abbrev ray11988 := rays 19
def bank11988 : Fin 2 → Cell := twoBank p11988 ray11988
theorem signs11988 : ∀ j, Signs p11988 (bank11988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11989 := params 20
abbrev ray11989 := rays 20
def bank11989 : Fin 2 → Cell := twoBank p11989 ray11989
theorem signs11989 : ∀ j, Signs p11989 (bank11989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11990 := params 21
abbrev ray11990 := rays 21
def bank11990 : Fin 2 → Cell := twoBank p11990 ray11990
theorem signs11990 : ∀ j, Signs p11990 (bank11990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11991 := params 22
abbrev ray11991 := rays 22
def bank11991 : Fin 2 → Cell := twoBank p11991 ray11991
theorem signs11991 : ∀ j, Signs p11991 (bank11991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11992 := params 23
abbrev ray11992 := rays 23
def bank11992 : Fin 2 → Cell := twoBank p11992 ray11992
theorem signs11992 : ∀ j, Signs p11992 (bank11992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11993 := params 24
abbrev ray11993 := rays 24
def bank11993 : Fin 2 → Cell := twoBank p11993 ray11993
theorem signs11993 : ∀ j, Signs p11993 (bank11993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11994 := params 25
abbrev ray11994 := rays 25
def bank11994 : Fin 2 → Cell := twoBank p11994 ray11994
theorem signs11994 : ∀ j, Signs p11994 (bank11994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11995 := params 26
abbrev ray11995 := rays 26
def bank11995 : Fin 2 → Cell := twoBank p11995 ray11995
theorem signs11995 : ∀ j, Signs p11995 (bank11995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11996 := params 27
abbrev ray11996 := rays 27
def bank11996 : Fin 2 → Cell := twoBank p11996 ray11996
theorem signs11996 : ∀ j, Signs p11996 (bank11996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11997 := params 28
abbrev ray11997 := rays 28
def bank11997 : Fin 2 → Cell := twoBank p11997 ray11997
theorem signs11997 : ∀ j, Signs p11997 (bank11997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11998 := params 29
abbrev ray11998 := rays 29
def bank11998 : Fin 2 → Cell := twoBank p11998 ray11998
theorem signs11998 : ∀ j, Signs p11998 (bank11998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11999 := params 30
abbrev ray11999 := rays 30
def bank11999 : Fin 2 → Cell := twoBank p11999 ray11999
theorem signs11999 : ∀ j, Signs p11999 (bank11999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12000 := params 31
abbrev ray12000 := rays 31
def bank12000 : Fin 2 → Cell := twoBank p12000 ray12000
theorem signs12000 : ∀ j, Signs p12000 (bank12000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11969_12000
