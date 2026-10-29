/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08961_08992
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97839934887009,97839589713466,97839244518973,97838899303532,97838554067143,97838208809806,97837863531522,97837518232292,97837172912116,97836827570995,97836482208930,97836136825921,97835791421969,97835445997075,97835100551239,97834755084461,97834409596743,97834064088085,97833718558487,97833373007951,97833027436477,97832681844065,97832336230716,97831990596431,97831644941210,97831299265054,97830953567964,97830607849940,97830262110983,97829916351094,97829570570273,97829224768520,97828878945837]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8960+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8961 := params 0
abbrev ray8961 := rays 0
def bank8961 : Fin 2 → Cell := twoBank p8961 ray8961
theorem signs8961 : ∀ j, Signs p8961 (bank8961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8962 := params 1
abbrev ray8962 := rays 1
def bank8962 : Fin 2 → Cell := twoBank p8962 ray8962
theorem signs8962 : ∀ j, Signs p8962 (bank8962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8963 := params 2
abbrev ray8963 := rays 2
def bank8963 : Fin 2 → Cell := twoBank p8963 ray8963
theorem signs8963 : ∀ j, Signs p8963 (bank8963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8964 := params 3
abbrev ray8964 := rays 3
def bank8964 : Fin 2 → Cell := twoBank p8964 ray8964
theorem signs8964 : ∀ j, Signs p8964 (bank8964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8965 := params 4
abbrev ray8965 := rays 4
def bank8965 : Fin 2 → Cell := twoBank p8965 ray8965
theorem signs8965 : ∀ j, Signs p8965 (bank8965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8966 := params 5
abbrev ray8966 := rays 5
def bank8966 : Fin 2 → Cell := twoBank p8966 ray8966
theorem signs8966 : ∀ j, Signs p8966 (bank8966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8967 := params 6
abbrev ray8967 := rays 6
def bank8967 : Fin 2 → Cell := twoBank p8967 ray8967
theorem signs8967 : ∀ j, Signs p8967 (bank8967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8968 := params 7
abbrev ray8968 := rays 7
def bank8968 : Fin 2 → Cell := twoBank p8968 ray8968
theorem signs8968 : ∀ j, Signs p8968 (bank8968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8969 := params 8
abbrev ray8969 := rays 8
def bank8969 : Fin 2 → Cell := twoBank p8969 ray8969
theorem signs8969 : ∀ j, Signs p8969 (bank8969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8970 := params 9
abbrev ray8970 := rays 9
def bank8970 : Fin 2 → Cell := twoBank p8970 ray8970
theorem signs8970 : ∀ j, Signs p8970 (bank8970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8971 := params 10
abbrev ray8971 := rays 10
def bank8971 : Fin 2 → Cell := twoBank p8971 ray8971
theorem signs8971 : ∀ j, Signs p8971 (bank8971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8972 := params 11
abbrev ray8972 := rays 11
def bank8972 : Fin 2 → Cell := twoBank p8972 ray8972
theorem signs8972 : ∀ j, Signs p8972 (bank8972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8973 := params 12
abbrev ray8973 := rays 12
def bank8973 : Fin 2 → Cell := twoBank p8973 ray8973
theorem signs8973 : ∀ j, Signs p8973 (bank8973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8974 := params 13
abbrev ray8974 := rays 13
def bank8974 : Fin 2 → Cell := twoBank p8974 ray8974
theorem signs8974 : ∀ j, Signs p8974 (bank8974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8975 := params 14
abbrev ray8975 := rays 14
def bank8975 : Fin 2 → Cell := twoBank p8975 ray8975
theorem signs8975 : ∀ j, Signs p8975 (bank8975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8976 := params 15
abbrev ray8976 := rays 15
def bank8976 : Fin 2 → Cell := twoBank p8976 ray8976
theorem signs8976 : ∀ j, Signs p8976 (bank8976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8977 := params 16
abbrev ray8977 := rays 16
def bank8977 : Fin 2 → Cell := twoBank p8977 ray8977
theorem signs8977 : ∀ j, Signs p8977 (bank8977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8978 := params 17
abbrev ray8978 := rays 17
def bank8978 : Fin 2 → Cell := twoBank p8978 ray8978
theorem signs8978 : ∀ j, Signs p8978 (bank8978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8979 := params 18
abbrev ray8979 := rays 18
def bank8979 : Fin 2 → Cell := twoBank p8979 ray8979
theorem signs8979 : ∀ j, Signs p8979 (bank8979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8980 := params 19
abbrev ray8980 := rays 19
def bank8980 : Fin 2 → Cell := twoBank p8980 ray8980
theorem signs8980 : ∀ j, Signs p8980 (bank8980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8981 := params 20
abbrev ray8981 := rays 20
def bank8981 : Fin 2 → Cell := twoBank p8981 ray8981
theorem signs8981 : ∀ j, Signs p8981 (bank8981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8982 := params 21
abbrev ray8982 := rays 21
def bank8982 : Fin 2 → Cell := twoBank p8982 ray8982
theorem signs8982 : ∀ j, Signs p8982 (bank8982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8983 := params 22
abbrev ray8983 := rays 22
def bank8983 : Fin 2 → Cell := twoBank p8983 ray8983
theorem signs8983 : ∀ j, Signs p8983 (bank8983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8984 := params 23
abbrev ray8984 := rays 23
def bank8984 : Fin 2 → Cell := twoBank p8984 ray8984
theorem signs8984 : ∀ j, Signs p8984 (bank8984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8985 := params 24
abbrev ray8985 := rays 24
def bank8985 : Fin 2 → Cell := twoBank p8985 ray8985
theorem signs8985 : ∀ j, Signs p8985 (bank8985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8986 := params 25
abbrev ray8986 := rays 25
def bank8986 : Fin 2 → Cell := twoBank p8986 ray8986
theorem signs8986 : ∀ j, Signs p8986 (bank8986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8987 := params 26
abbrev ray8987 := rays 26
def bank8987 : Fin 2 → Cell := twoBank p8987 ray8987
theorem signs8987 : ∀ j, Signs p8987 (bank8987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8988 := params 27
abbrev ray8988 := rays 27
def bank8988 : Fin 2 → Cell := twoBank p8988 ray8988
theorem signs8988 : ∀ j, Signs p8988 (bank8988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8989 := params 28
abbrev ray8989 := rays 28
def bank8989 : Fin 2 → Cell := twoBank p8989 ray8989
theorem signs8989 : ∀ j, Signs p8989 (bank8989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8990 := params 29
abbrev ray8990 := rays 29
def bank8990 : Fin 2 → Cell := twoBank p8990 ray8990
theorem signs8990 : ∀ j, Signs p8990 (bank8990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8991 := params 30
abbrev ray8991 := rays 30
def bank8991 : Fin 2 → Cell := twoBank p8991 ray8991
theorem signs8991 : ∀ j, Signs p8991 (bank8991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8992 := params 31
abbrev ray8992 := rays 31
def bank8992 : Fin 2 → Cell := twoBank p8992 ray8992
theorem signs8992 : ∀ j, Signs p8992 (bank8992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08961_08992
