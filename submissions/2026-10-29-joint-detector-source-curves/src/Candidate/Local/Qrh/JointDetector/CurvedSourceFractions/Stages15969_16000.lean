/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15969_16000
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94948103420017,94947630555467,94947157674924,94946684778388,94946211865859,94945738937336,94945265992820,94944793032311,94944320055809,94943847063314,94943374054826,94942901030345,94942427989871,94941954933404,94941481860944,94941008772491,94940535668045,94940062547607,94939589411176,94939116258752,94938643090336,94938169905927,94937696705525,94937223489131,94936750256744,94936277008365,94935803743994,94935330463630,94934857167274,94934383854925,94933910526584,94933437182251,94932963821926]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15968+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15969 := params 0
abbrev ray15969 := rays 0
def bank15969 : Fin 1 → Cell := oneBank p15969 ray15969
theorem signs15969 : ∀ j, Signs p15969 (bank15969 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15970 := params 1
abbrev ray15970 := rays 1
def bank15970 : Fin 1 → Cell := oneBank p15970 ray15970
theorem signs15970 : ∀ j, Signs p15970 (bank15970 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15971 := params 2
abbrev ray15971 := rays 2
def bank15971 : Fin 1 → Cell := oneBank p15971 ray15971
theorem signs15971 : ∀ j, Signs p15971 (bank15971 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15972 := params 3
abbrev ray15972 := rays 3
def bank15972 : Fin 1 → Cell := oneBank p15972 ray15972
theorem signs15972 : ∀ j, Signs p15972 (bank15972 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15973 := params 4
abbrev ray15973 := rays 4
def bank15973 : Fin 1 → Cell := oneBank p15973 ray15973
theorem signs15973 : ∀ j, Signs p15973 (bank15973 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15974 := params 5
abbrev ray15974 := rays 5
def bank15974 : Fin 1 → Cell := oneBank p15974 ray15974
theorem signs15974 : ∀ j, Signs p15974 (bank15974 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15975 := params 6
abbrev ray15975 := rays 6
def bank15975 : Fin 1 → Cell := oneBank p15975 ray15975
theorem signs15975 : ∀ j, Signs p15975 (bank15975 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15976 := params 7
abbrev ray15976 := rays 7
def bank15976 : Fin 1 → Cell := oneBank p15976 ray15976
theorem signs15976 : ∀ j, Signs p15976 (bank15976 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15977 := params 8
abbrev ray15977 := rays 8
def bank15977 : Fin 1 → Cell := oneBank p15977 ray15977
theorem signs15977 : ∀ j, Signs p15977 (bank15977 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15978 := params 9
abbrev ray15978 := rays 9
def bank15978 : Fin 1 → Cell := oneBank p15978 ray15978
theorem signs15978 : ∀ j, Signs p15978 (bank15978 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15979 := params 10
abbrev ray15979 := rays 10
def bank15979 : Fin 1 → Cell := oneBank p15979 ray15979
theorem signs15979 : ∀ j, Signs p15979 (bank15979 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15980 := params 11
abbrev ray15980 := rays 11
def bank15980 : Fin 1 → Cell := oneBank p15980 ray15980
theorem signs15980 : ∀ j, Signs p15980 (bank15980 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15981 := params 12
abbrev ray15981 := rays 12
def bank15981 : Fin 1 → Cell := oneBank p15981 ray15981
theorem signs15981 : ∀ j, Signs p15981 (bank15981 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15982 := params 13
abbrev ray15982 := rays 13
def bank15982 : Fin 1 → Cell := oneBank p15982 ray15982
theorem signs15982 : ∀ j, Signs p15982 (bank15982 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15983 := params 14
abbrev ray15983 := rays 14
def bank15983 : Fin 1 → Cell := oneBank p15983 ray15983
theorem signs15983 : ∀ j, Signs p15983 (bank15983 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15984 := params 15
abbrev ray15984 := rays 15
def bank15984 : Fin 1 → Cell := oneBank p15984 ray15984
theorem signs15984 : ∀ j, Signs p15984 (bank15984 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15985 := params 16
abbrev ray15985 := rays 16
def bank15985 : Fin 1 → Cell := oneBank p15985 ray15985
theorem signs15985 : ∀ j, Signs p15985 (bank15985 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15986 := params 17
abbrev ray15986 := rays 17
def bank15986 : Fin 1 → Cell := oneBank p15986 ray15986
theorem signs15986 : ∀ j, Signs p15986 (bank15986 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15987 := params 18
abbrev ray15987 := rays 18
def bank15987 : Fin 1 → Cell := oneBank p15987 ray15987
theorem signs15987 : ∀ j, Signs p15987 (bank15987 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15988 := params 19
abbrev ray15988 := rays 19
def bank15988 : Fin 1 → Cell := oneBank p15988 ray15988
theorem signs15988 : ∀ j, Signs p15988 (bank15988 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15989 := params 20
abbrev ray15989 := rays 20
def bank15989 : Fin 1 → Cell := oneBank p15989 ray15989
theorem signs15989 : ∀ j, Signs p15989 (bank15989 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15990 := params 21
abbrev ray15990 := rays 21
def bank15990 : Fin 1 → Cell := oneBank p15990 ray15990
theorem signs15990 : ∀ j, Signs p15990 (bank15990 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15991 := params 22
abbrev ray15991 := rays 22
def bank15991 : Fin 1 → Cell := oneBank p15991 ray15991
theorem signs15991 : ∀ j, Signs p15991 (bank15991 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15992 := params 23
abbrev ray15992 := rays 23
def bank15992 : Fin 1 → Cell := oneBank p15992 ray15992
theorem signs15992 : ∀ j, Signs p15992 (bank15992 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15993 := params 24
abbrev ray15993 := rays 24
def bank15993 : Fin 1 → Cell := oneBank p15993 ray15993
theorem signs15993 : ∀ j, Signs p15993 (bank15993 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15994 := params 25
abbrev ray15994 := rays 25
def bank15994 : Fin 1 → Cell := oneBank p15994 ray15994
theorem signs15994 : ∀ j, Signs p15994 (bank15994 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15995 := params 26
abbrev ray15995 := rays 26
def bank15995 : Fin 1 → Cell := oneBank p15995 ray15995
theorem signs15995 : ∀ j, Signs p15995 (bank15995 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15996 := params 27
abbrev ray15996 := rays 27
def bank15996 : Fin 1 → Cell := oneBank p15996 ray15996
theorem signs15996 : ∀ j, Signs p15996 (bank15996 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15997 := params 28
abbrev ray15997 := rays 28
def bank15997 : Fin 1 → Cell := oneBank p15997 ray15997
theorem signs15997 : ∀ j, Signs p15997 (bank15997 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15998 := params 29
abbrev ray15998 := rays 29
def bank15998 : Fin 1 → Cell := oneBank p15998 ray15998
theorem signs15998 : ∀ j, Signs p15998 (bank15998 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15999 := params 30
abbrev ray15999 := rays 30
def bank15999 : Fin 1 → Cell := oneBank p15999 ray15999
theorem signs15999 : ∀ j, Signs p15999 (bank15999 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16000 := params 31
abbrev ray16000 := rays 31
def bank16000 : Fin 1 → Cell := oneBank p16000 ray16000
theorem signs16000 : ∀ j, Signs p16000 (bank16000 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15969_16000
