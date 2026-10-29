/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16961_16992
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94471163737732,94470675014552,94470186275380,94469697520215,94469208749058,94468719961909,94468231158767,94467742339633,94467253504507,94466764653388,94466275786277,94465786903173,94465298004076,94464809088987,94464320157905,94463831210830,94463342247763,94462853268703,94462364273650,94461875262604,94461386235565,94460897192533,94460408133508,94459919058490,94459429967479,94458940860475,94458451737478,94457962598488,94457473443505,94456984272528,94456495085558,94456005882595,94455516663638]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16960+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16961 := params 0
abbrev ray16961 := rays 0
def bank16961 : Fin 1 → Cell := oneBank p16961 ray16961
theorem signs16961 : ∀ j, Signs p16961 (bank16961 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16962 := params 1
abbrev ray16962 := rays 1
def bank16962 : Fin 1 → Cell := oneBank p16962 ray16962
theorem signs16962 : ∀ j, Signs p16962 (bank16962 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16963 := params 2
abbrev ray16963 := rays 2
def bank16963 : Fin 1 → Cell := oneBank p16963 ray16963
theorem signs16963 : ∀ j, Signs p16963 (bank16963 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16964 := params 3
abbrev ray16964 := rays 3
def bank16964 : Fin 1 → Cell := oneBank p16964 ray16964
theorem signs16964 : ∀ j, Signs p16964 (bank16964 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16965 := params 4
abbrev ray16965 := rays 4
def bank16965 : Fin 1 → Cell := oneBank p16965 ray16965
theorem signs16965 : ∀ j, Signs p16965 (bank16965 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16966 := params 5
abbrev ray16966 := rays 5
def bank16966 : Fin 1 → Cell := oneBank p16966 ray16966
theorem signs16966 : ∀ j, Signs p16966 (bank16966 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16967 := params 6
abbrev ray16967 := rays 6
def bank16967 : Fin 1 → Cell := oneBank p16967 ray16967
theorem signs16967 : ∀ j, Signs p16967 (bank16967 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16968 := params 7
abbrev ray16968 := rays 7
def bank16968 : Fin 1 → Cell := oneBank p16968 ray16968
theorem signs16968 : ∀ j, Signs p16968 (bank16968 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16969 := params 8
abbrev ray16969 := rays 8
def bank16969 : Fin 1 → Cell := oneBank p16969 ray16969
theorem signs16969 : ∀ j, Signs p16969 (bank16969 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16970 := params 9
abbrev ray16970 := rays 9
def bank16970 : Fin 1 → Cell := oneBank p16970 ray16970
theorem signs16970 : ∀ j, Signs p16970 (bank16970 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16971 := params 10
abbrev ray16971 := rays 10
def bank16971 : Fin 1 → Cell := oneBank p16971 ray16971
theorem signs16971 : ∀ j, Signs p16971 (bank16971 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16972 := params 11
abbrev ray16972 := rays 11
def bank16972 : Fin 1 → Cell := oneBank p16972 ray16972
theorem signs16972 : ∀ j, Signs p16972 (bank16972 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16973 := params 12
abbrev ray16973 := rays 12
def bank16973 : Fin 1 → Cell := oneBank p16973 ray16973
theorem signs16973 : ∀ j, Signs p16973 (bank16973 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16974 := params 13
abbrev ray16974 := rays 13
def bank16974 : Fin 1 → Cell := oneBank p16974 ray16974
theorem signs16974 : ∀ j, Signs p16974 (bank16974 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16975 := params 14
abbrev ray16975 := rays 14
def bank16975 : Fin 1 → Cell := oneBank p16975 ray16975
theorem signs16975 : ∀ j, Signs p16975 (bank16975 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16976 := params 15
abbrev ray16976 := rays 15
def bank16976 : Fin 1 → Cell := oneBank p16976 ray16976
theorem signs16976 : ∀ j, Signs p16976 (bank16976 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16977 := params 16
abbrev ray16977 := rays 16
def bank16977 : Fin 1 → Cell := oneBank p16977 ray16977
theorem signs16977 : ∀ j, Signs p16977 (bank16977 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16978 := params 17
abbrev ray16978 := rays 17
def bank16978 : Fin 1 → Cell := oneBank p16978 ray16978
theorem signs16978 : ∀ j, Signs p16978 (bank16978 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16979 := params 18
abbrev ray16979 := rays 18
def bank16979 : Fin 1 → Cell := oneBank p16979 ray16979
theorem signs16979 : ∀ j, Signs p16979 (bank16979 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16980 := params 19
abbrev ray16980 := rays 19
def bank16980 : Fin 1 → Cell := oneBank p16980 ray16980
theorem signs16980 : ∀ j, Signs p16980 (bank16980 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16981 := params 20
abbrev ray16981 := rays 20
def bank16981 : Fin 1 → Cell := oneBank p16981 ray16981
theorem signs16981 : ∀ j, Signs p16981 (bank16981 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16982 := params 21
abbrev ray16982 := rays 21
def bank16982 : Fin 1 → Cell := oneBank p16982 ray16982
theorem signs16982 : ∀ j, Signs p16982 (bank16982 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16983 := params 22
abbrev ray16983 := rays 22
def bank16983 : Fin 1 → Cell := oneBank p16983 ray16983
theorem signs16983 : ∀ j, Signs p16983 (bank16983 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16984 := params 23
abbrev ray16984 := rays 23
def bank16984 : Fin 1 → Cell := oneBank p16984 ray16984
theorem signs16984 : ∀ j, Signs p16984 (bank16984 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16985 := params 24
abbrev ray16985 := rays 24
def bank16985 : Fin 1 → Cell := oneBank p16985 ray16985
theorem signs16985 : ∀ j, Signs p16985 (bank16985 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16986 := params 25
abbrev ray16986 := rays 25
def bank16986 : Fin 1 → Cell := oneBank p16986 ray16986
theorem signs16986 : ∀ j, Signs p16986 (bank16986 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16987 := params 26
abbrev ray16987 := rays 26
def bank16987 : Fin 1 → Cell := oneBank p16987 ray16987
theorem signs16987 : ∀ j, Signs p16987 (bank16987 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16988 := params 27
abbrev ray16988 := rays 27
def bank16988 : Fin 1 → Cell := oneBank p16988 ray16988
theorem signs16988 : ∀ j, Signs p16988 (bank16988 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16989 := params 28
abbrev ray16989 := rays 28
def bank16989 : Fin 1 → Cell := oneBank p16989 ray16989
theorem signs16989 : ∀ j, Signs p16989 (bank16989 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16990 := params 29
abbrev ray16990 := rays 29
def bank16990 : Fin 1 → Cell := oneBank p16990 ray16990
theorem signs16990 : ∀ j, Signs p16990 (bank16990 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16991 := params 30
abbrev ray16991 := rays 30
def bank16991 : Fin 1 → Cell := oneBank p16991 ray16991
theorem signs16991 : ∀ j, Signs p16991 (bank16991 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16992 := params 31
abbrev ray16992 := rays 31
def bank16992 : Fin 1 → Cell := oneBank p16992 ray16992
theorem signs16992 : ∀ j, Signs p16992 (bank16992 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16961_16992
