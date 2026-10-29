/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04961_04992
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99045450187671,99045194701642,99044939191471,99044683657159,99044428098707,99044172516116,99043916909386,99043661278519,99043405623516,99043149944378,99042894241105,99042638513699,99042382762161,99042126986492,99041871186693,99041615362764,99041359514707,99041103642523,99040847746213,99040591825777,99040335881217,99040079912534,99039823919729,99039567902803,99039311861756,99039055796590,99038799707306,99038543593905,99038287456387,99038031294754,99037775109007,99037518899147,99037262665174]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4960+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4961 := params 0
abbrev ray4961 := rays 0
def bank4961 : Fin 2 → Cell := twoBank p4961 ray4961
theorem signs4961 : ∀ j, Signs p4961 (bank4961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4962 := params 1
abbrev ray4962 := rays 1
def bank4962 : Fin 2 → Cell := twoBank p4962 ray4962
theorem signs4962 : ∀ j, Signs p4962 (bank4962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4963 := params 2
abbrev ray4963 := rays 2
def bank4963 : Fin 2 → Cell := twoBank p4963 ray4963
theorem signs4963 : ∀ j, Signs p4963 (bank4963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4964 := params 3
abbrev ray4964 := rays 3
def bank4964 : Fin 2 → Cell := twoBank p4964 ray4964
theorem signs4964 : ∀ j, Signs p4964 (bank4964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4965 := params 4
abbrev ray4965 := rays 4
def bank4965 : Fin 2 → Cell := twoBank p4965 ray4965
theorem signs4965 : ∀ j, Signs p4965 (bank4965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4966 := params 5
abbrev ray4966 := rays 5
def bank4966 : Fin 2 → Cell := twoBank p4966 ray4966
theorem signs4966 : ∀ j, Signs p4966 (bank4966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4967 := params 6
abbrev ray4967 := rays 6
def bank4967 : Fin 2 → Cell := twoBank p4967 ray4967
theorem signs4967 : ∀ j, Signs p4967 (bank4967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4968 := params 7
abbrev ray4968 := rays 7
def bank4968 : Fin 2 → Cell := twoBank p4968 ray4968
theorem signs4968 : ∀ j, Signs p4968 (bank4968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4969 := params 8
abbrev ray4969 := rays 8
def bank4969 : Fin 2 → Cell := twoBank p4969 ray4969
theorem signs4969 : ∀ j, Signs p4969 (bank4969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4970 := params 9
abbrev ray4970 := rays 9
def bank4970 : Fin 2 → Cell := twoBank p4970 ray4970
theorem signs4970 : ∀ j, Signs p4970 (bank4970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4971 := params 10
abbrev ray4971 := rays 10
def bank4971 : Fin 2 → Cell := twoBank p4971 ray4971
theorem signs4971 : ∀ j, Signs p4971 (bank4971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4972 := params 11
abbrev ray4972 := rays 11
def bank4972 : Fin 2 → Cell := twoBank p4972 ray4972
theorem signs4972 : ∀ j, Signs p4972 (bank4972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4973 := params 12
abbrev ray4973 := rays 12
def bank4973 : Fin 2 → Cell := twoBank p4973 ray4973
theorem signs4973 : ∀ j, Signs p4973 (bank4973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4974 := params 13
abbrev ray4974 := rays 13
def bank4974 : Fin 2 → Cell := twoBank p4974 ray4974
theorem signs4974 : ∀ j, Signs p4974 (bank4974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4975 := params 14
abbrev ray4975 := rays 14
def bank4975 : Fin 2 → Cell := twoBank p4975 ray4975
theorem signs4975 : ∀ j, Signs p4975 (bank4975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4976 := params 15
abbrev ray4976 := rays 15
def bank4976 : Fin 2 → Cell := twoBank p4976 ray4976
theorem signs4976 : ∀ j, Signs p4976 (bank4976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4977 := params 16
abbrev ray4977 := rays 16
def bank4977 : Fin 2 → Cell := twoBank p4977 ray4977
theorem signs4977 : ∀ j, Signs p4977 (bank4977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4978 := params 17
abbrev ray4978 := rays 17
def bank4978 : Fin 2 → Cell := twoBank p4978 ray4978
theorem signs4978 : ∀ j, Signs p4978 (bank4978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4979 := params 18
abbrev ray4979 := rays 18
def bank4979 : Fin 2 → Cell := twoBank p4979 ray4979
theorem signs4979 : ∀ j, Signs p4979 (bank4979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4980 := params 19
abbrev ray4980 := rays 19
def bank4980 : Fin 2 → Cell := twoBank p4980 ray4980
theorem signs4980 : ∀ j, Signs p4980 (bank4980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4981 := params 20
abbrev ray4981 := rays 20
def bank4981 : Fin 2 → Cell := twoBank p4981 ray4981
theorem signs4981 : ∀ j, Signs p4981 (bank4981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4982 := params 21
abbrev ray4982 := rays 21
def bank4982 : Fin 2 → Cell := twoBank p4982 ray4982
theorem signs4982 : ∀ j, Signs p4982 (bank4982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4983 := params 22
abbrev ray4983 := rays 22
def bank4983 : Fin 2 → Cell := twoBank p4983 ray4983
theorem signs4983 : ∀ j, Signs p4983 (bank4983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4984 := params 23
abbrev ray4984 := rays 23
def bank4984 : Fin 2 → Cell := twoBank p4984 ray4984
theorem signs4984 : ∀ j, Signs p4984 (bank4984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4985 := params 24
abbrev ray4985 := rays 24
def bank4985 : Fin 2 → Cell := twoBank p4985 ray4985
theorem signs4985 : ∀ j, Signs p4985 (bank4985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4986 := params 25
abbrev ray4986 := rays 25
def bank4986 : Fin 2 → Cell := twoBank p4986 ray4986
theorem signs4986 : ∀ j, Signs p4986 (bank4986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4987 := params 26
abbrev ray4987 := rays 26
def bank4987 : Fin 2 → Cell := twoBank p4987 ray4987
theorem signs4987 : ∀ j, Signs p4987 (bank4987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4988 := params 27
abbrev ray4988 := rays 27
def bank4988 : Fin 2 → Cell := twoBank p4988 ray4988
theorem signs4988 : ∀ j, Signs p4988 (bank4988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4989 := params 28
abbrev ray4989 := rays 28
def bank4989 : Fin 2 → Cell := twoBank p4989 ray4989
theorem signs4989 : ∀ j, Signs p4989 (bank4989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4990 := params 29
abbrev ray4990 := rays 29
def bank4990 : Fin 2 → Cell := twoBank p4990 ray4990
theorem signs4990 : ∀ j, Signs p4990 (bank4990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4991 := params 30
abbrev ray4991 := rays 30
def bank4991 : Fin 2 → Cell := twoBank p4991 ray4991
theorem signs4991 : ∀ j, Signs p4991 (bank4991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4992 := params 31
abbrev ray4992 := rays 31
def bank4992 : Fin 2 → Cell := twoBank p4992 ray4992
theorem signs4992 : ∀ j, Signs p4992 (bank4992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04961_04992
