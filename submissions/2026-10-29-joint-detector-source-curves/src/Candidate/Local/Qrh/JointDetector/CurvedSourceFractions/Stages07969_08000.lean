/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07969_08000
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98171923695709,98171599624546,98171275531775,98170951417397,98170627281413,98170303123823,98169978944628,98169654743829,98169330521426,98169006277421,98168682011813,98168357724604,98168033415794,98167709085384,98167384733375,98167060359767,98166735964561,98166411547758,98166087109358,98165762649362,98165438167771,98165113664586,98164789139807,98164464593435,98164140025471,98163815435915,98163490824768,98163166192031,98162841537704,98162516861788,98162192164284,98161867445193,98161542704515]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7968+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7969 := params 0
abbrev ray7969 := rays 0
def bank7969 : Fin 2 → Cell := twoBank p7969 ray7969
theorem signs7969 : ∀ j, Signs p7969 (bank7969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7970 := params 1
abbrev ray7970 := rays 1
def bank7970 : Fin 2 → Cell := twoBank p7970 ray7970
theorem signs7970 : ∀ j, Signs p7970 (bank7970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7971 := params 2
abbrev ray7971 := rays 2
def bank7971 : Fin 2 → Cell := twoBank p7971 ray7971
theorem signs7971 : ∀ j, Signs p7971 (bank7971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7972 := params 3
abbrev ray7972 := rays 3
def bank7972 : Fin 2 → Cell := twoBank p7972 ray7972
theorem signs7972 : ∀ j, Signs p7972 (bank7972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7973 := params 4
abbrev ray7973 := rays 4
def bank7973 : Fin 2 → Cell := twoBank p7973 ray7973
theorem signs7973 : ∀ j, Signs p7973 (bank7973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7974 := params 5
abbrev ray7974 := rays 5
def bank7974 : Fin 2 → Cell := twoBank p7974 ray7974
theorem signs7974 : ∀ j, Signs p7974 (bank7974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7975 := params 6
abbrev ray7975 := rays 6
def bank7975 : Fin 2 → Cell := twoBank p7975 ray7975
theorem signs7975 : ∀ j, Signs p7975 (bank7975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7976 := params 7
abbrev ray7976 := rays 7
def bank7976 : Fin 2 → Cell := twoBank p7976 ray7976
theorem signs7976 : ∀ j, Signs p7976 (bank7976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7977 := params 8
abbrev ray7977 := rays 8
def bank7977 : Fin 2 → Cell := twoBank p7977 ray7977
theorem signs7977 : ∀ j, Signs p7977 (bank7977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7978 := params 9
abbrev ray7978 := rays 9
def bank7978 : Fin 2 → Cell := twoBank p7978 ray7978
theorem signs7978 : ∀ j, Signs p7978 (bank7978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7979 := params 10
abbrev ray7979 := rays 10
def bank7979 : Fin 2 → Cell := twoBank p7979 ray7979
theorem signs7979 : ∀ j, Signs p7979 (bank7979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7980 := params 11
abbrev ray7980 := rays 11
def bank7980 : Fin 2 → Cell := twoBank p7980 ray7980
theorem signs7980 : ∀ j, Signs p7980 (bank7980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7981 := params 12
abbrev ray7981 := rays 12
def bank7981 : Fin 2 → Cell := twoBank p7981 ray7981
theorem signs7981 : ∀ j, Signs p7981 (bank7981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7982 := params 13
abbrev ray7982 := rays 13
def bank7982 : Fin 2 → Cell := twoBank p7982 ray7982
theorem signs7982 : ∀ j, Signs p7982 (bank7982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7983 := params 14
abbrev ray7983 := rays 14
def bank7983 : Fin 2 → Cell := twoBank p7983 ray7983
theorem signs7983 : ∀ j, Signs p7983 (bank7983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7984 := params 15
abbrev ray7984 := rays 15
def bank7984 : Fin 2 → Cell := twoBank p7984 ray7984
theorem signs7984 : ∀ j, Signs p7984 (bank7984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7985 := params 16
abbrev ray7985 := rays 16
def bank7985 : Fin 2 → Cell := twoBank p7985 ray7985
theorem signs7985 : ∀ j, Signs p7985 (bank7985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7986 := params 17
abbrev ray7986 := rays 17
def bank7986 : Fin 2 → Cell := twoBank p7986 ray7986
theorem signs7986 : ∀ j, Signs p7986 (bank7986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7987 := params 18
abbrev ray7987 := rays 18
def bank7987 : Fin 2 → Cell := twoBank p7987 ray7987
theorem signs7987 : ∀ j, Signs p7987 (bank7987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7988 := params 19
abbrev ray7988 := rays 19
def bank7988 : Fin 2 → Cell := twoBank p7988 ray7988
theorem signs7988 : ∀ j, Signs p7988 (bank7988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7989 := params 20
abbrev ray7989 := rays 20
def bank7989 : Fin 2 → Cell := twoBank p7989 ray7989
theorem signs7989 : ∀ j, Signs p7989 (bank7989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7990 := params 21
abbrev ray7990 := rays 21
def bank7990 : Fin 2 → Cell := twoBank p7990 ray7990
theorem signs7990 : ∀ j, Signs p7990 (bank7990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7991 := params 22
abbrev ray7991 := rays 22
def bank7991 : Fin 2 → Cell := twoBank p7991 ray7991
theorem signs7991 : ∀ j, Signs p7991 (bank7991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7992 := params 23
abbrev ray7992 := rays 23
def bank7992 : Fin 2 → Cell := twoBank p7992 ray7992
theorem signs7992 : ∀ j, Signs p7992 (bank7992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7993 := params 24
abbrev ray7993 := rays 24
def bank7993 : Fin 2 → Cell := twoBank p7993 ray7993
theorem signs7993 : ∀ j, Signs p7993 (bank7993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7994 := params 25
abbrev ray7994 := rays 25
def bank7994 : Fin 2 → Cell := twoBank p7994 ray7994
theorem signs7994 : ∀ j, Signs p7994 (bank7994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7995 := params 26
abbrev ray7995 := rays 26
def bank7995 : Fin 2 → Cell := twoBank p7995 ray7995
theorem signs7995 : ∀ j, Signs p7995 (bank7995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7996 := params 27
abbrev ray7996 := rays 27
def bank7996 : Fin 2 → Cell := twoBank p7996 ray7996
theorem signs7996 : ∀ j, Signs p7996 (bank7996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7997 := params 28
abbrev ray7997 := rays 28
def bank7997 : Fin 2 → Cell := twoBank p7997 ray7997
theorem signs7997 : ∀ j, Signs p7997 (bank7997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7998 := params 29
abbrev ray7998 := rays 29
def bank7998 : Fin 2 → Cell := twoBank p7998 ray7998
theorem signs7998 : ∀ j, Signs p7998 (bank7998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7999 := params 30
abbrev ray7999 := rays 30
def bank7999 : Fin 2 → Cell := twoBank p7999 ray7999
theorem signs7999 : ∀ j, Signs p7999 (bank7999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8000 := params 31
abbrev ray8000 := rays 31
def bank8000 : Fin 2 → Cell := twoBank p8000 ray8000
theorem signs8000 : ∀ j, Signs p8000 (bank8000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07969_08000
