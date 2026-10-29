/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03969_04000
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99286833188600,99286602165136,99286371116475,99286140042617,99285908943564,99285677819317,99285446669877,99285215495245,99284984295422,99284753070409,99284521820208,99284290544819,99284059244244,99283827918484,99283596567540,99283365191413,99283133790104,99282902363614,99282670911945,99282439435098,99282207933073,99281976405872,99281744853496,99281513275946,99281281673224,99281050045330,99280818392265,99280586714031,99280355010629,99280123282060,99279891528325,99279659749425,99279427945361]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3968+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3969 := params 0
abbrev ray3969 := rays 0
def bank3969 : Fin 2 → Cell := twoBank p3969 ray3969
theorem signs3969 : ∀ j, Signs p3969 (bank3969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3970 := params 1
abbrev ray3970 := rays 1
def bank3970 : Fin 2 → Cell := twoBank p3970 ray3970
theorem signs3970 : ∀ j, Signs p3970 (bank3970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3971 := params 2
abbrev ray3971 := rays 2
def bank3971 : Fin 2 → Cell := twoBank p3971 ray3971
theorem signs3971 : ∀ j, Signs p3971 (bank3971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3972 := params 3
abbrev ray3972 := rays 3
def bank3972 : Fin 2 → Cell := twoBank p3972 ray3972
theorem signs3972 : ∀ j, Signs p3972 (bank3972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3973 := params 4
abbrev ray3973 := rays 4
def bank3973 : Fin 2 → Cell := twoBank p3973 ray3973
theorem signs3973 : ∀ j, Signs p3973 (bank3973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3974 := params 5
abbrev ray3974 := rays 5
def bank3974 : Fin 2 → Cell := twoBank p3974 ray3974
theorem signs3974 : ∀ j, Signs p3974 (bank3974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3975 := params 6
abbrev ray3975 := rays 6
def bank3975 : Fin 2 → Cell := twoBank p3975 ray3975
theorem signs3975 : ∀ j, Signs p3975 (bank3975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3976 := params 7
abbrev ray3976 := rays 7
def bank3976 : Fin 2 → Cell := twoBank p3976 ray3976
theorem signs3976 : ∀ j, Signs p3976 (bank3976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3977 := params 8
abbrev ray3977 := rays 8
def bank3977 : Fin 2 → Cell := twoBank p3977 ray3977
theorem signs3977 : ∀ j, Signs p3977 (bank3977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3978 := params 9
abbrev ray3978 := rays 9
def bank3978 : Fin 2 → Cell := twoBank p3978 ray3978
theorem signs3978 : ∀ j, Signs p3978 (bank3978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3979 := params 10
abbrev ray3979 := rays 10
def bank3979 : Fin 2 → Cell := twoBank p3979 ray3979
theorem signs3979 : ∀ j, Signs p3979 (bank3979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3980 := params 11
abbrev ray3980 := rays 11
def bank3980 : Fin 2 → Cell := twoBank p3980 ray3980
theorem signs3980 : ∀ j, Signs p3980 (bank3980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3981 := params 12
abbrev ray3981 := rays 12
def bank3981 : Fin 2 → Cell := twoBank p3981 ray3981
theorem signs3981 : ∀ j, Signs p3981 (bank3981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3982 := params 13
abbrev ray3982 := rays 13
def bank3982 : Fin 2 → Cell := twoBank p3982 ray3982
theorem signs3982 : ∀ j, Signs p3982 (bank3982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3983 := params 14
abbrev ray3983 := rays 14
def bank3983 : Fin 2 → Cell := twoBank p3983 ray3983
theorem signs3983 : ∀ j, Signs p3983 (bank3983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3984 := params 15
abbrev ray3984 := rays 15
def bank3984 : Fin 2 → Cell := twoBank p3984 ray3984
theorem signs3984 : ∀ j, Signs p3984 (bank3984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3985 := params 16
abbrev ray3985 := rays 16
def bank3985 : Fin 2 → Cell := twoBank p3985 ray3985
theorem signs3985 : ∀ j, Signs p3985 (bank3985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3986 := params 17
abbrev ray3986 := rays 17
def bank3986 : Fin 2 → Cell := twoBank p3986 ray3986
theorem signs3986 : ∀ j, Signs p3986 (bank3986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3987 := params 18
abbrev ray3987 := rays 18
def bank3987 : Fin 2 → Cell := twoBank p3987 ray3987
theorem signs3987 : ∀ j, Signs p3987 (bank3987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3988 := params 19
abbrev ray3988 := rays 19
def bank3988 : Fin 2 → Cell := twoBank p3988 ray3988
theorem signs3988 : ∀ j, Signs p3988 (bank3988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3989 := params 20
abbrev ray3989 := rays 20
def bank3989 : Fin 2 → Cell := twoBank p3989 ray3989
theorem signs3989 : ∀ j, Signs p3989 (bank3989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3990 := params 21
abbrev ray3990 := rays 21
def bank3990 : Fin 2 → Cell := twoBank p3990 ray3990
theorem signs3990 : ∀ j, Signs p3990 (bank3990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3991 := params 22
abbrev ray3991 := rays 22
def bank3991 : Fin 2 → Cell := twoBank p3991 ray3991
theorem signs3991 : ∀ j, Signs p3991 (bank3991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3992 := params 23
abbrev ray3992 := rays 23
def bank3992 : Fin 2 → Cell := twoBank p3992 ray3992
theorem signs3992 : ∀ j, Signs p3992 (bank3992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3993 := params 24
abbrev ray3993 := rays 24
def bank3993 : Fin 2 → Cell := twoBank p3993 ray3993
theorem signs3993 : ∀ j, Signs p3993 (bank3993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3994 := params 25
abbrev ray3994 := rays 25
def bank3994 : Fin 2 → Cell := twoBank p3994 ray3994
theorem signs3994 : ∀ j, Signs p3994 (bank3994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3995 := params 26
abbrev ray3995 := rays 26
def bank3995 : Fin 2 → Cell := twoBank p3995 ray3995
theorem signs3995 : ∀ j, Signs p3995 (bank3995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3996 := params 27
abbrev ray3996 := rays 27
def bank3996 : Fin 2 → Cell := twoBank p3996 ray3996
theorem signs3996 : ∀ j, Signs p3996 (bank3996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3997 := params 28
abbrev ray3997 := rays 28
def bank3997 : Fin 2 → Cell := twoBank p3997 ray3997
theorem signs3997 : ∀ j, Signs p3997 (bank3997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3998 := params 29
abbrev ray3998 := rays 29
def bank3998 : Fin 2 → Cell := twoBank p3998 ray3998
theorem signs3998 : ∀ j, Signs p3998 (bank3998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3999 := params 30
abbrev ray3999 := rays 30
def bank3999 : Fin 2 → Cell := twoBank p3999 ray3999
theorem signs3999 : ∀ j, Signs p3999 (bank3999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4000 := params 31
abbrev ray4000 := rays 31
def bank4000 : Fin 2 → Cell := twoBank p4000 ray4000
theorem signs4000 : ∀ j, Signs p4000 (bank4000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03969_04000
