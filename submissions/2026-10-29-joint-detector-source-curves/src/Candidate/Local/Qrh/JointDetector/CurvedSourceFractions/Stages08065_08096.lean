/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08065_08096
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98140714432679,98140388290361,98140062126502,98139735941103,98139409734165,98139083505688,98138757255674,98138430984122,98138104691034,98137778376410,98137452040251,98137125682557,98136799303330,98136472902570,98136146480277,98135820036453,98135493571098,98135167084212,98134840575797,98134514045853,98134187494381,98133860921381,98133534326854,98133207710801,98132881073223,98132554414120,98132227733493,98131901031343,98131574307670,98131247562475,98130920795759,98130594007522,98130267197765]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8064+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8065 := params 0
abbrev ray8065 := rays 0
def bank8065 : Fin 2 → Cell := twoBank p8065 ray8065
theorem signs8065 : ∀ j, Signs p8065 (bank8065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8066 := params 1
abbrev ray8066 := rays 1
def bank8066 : Fin 2 → Cell := twoBank p8066 ray8066
theorem signs8066 : ∀ j, Signs p8066 (bank8066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8067 := params 2
abbrev ray8067 := rays 2
def bank8067 : Fin 2 → Cell := twoBank p8067 ray8067
theorem signs8067 : ∀ j, Signs p8067 (bank8067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8068 := params 3
abbrev ray8068 := rays 3
def bank8068 : Fin 2 → Cell := twoBank p8068 ray8068
theorem signs8068 : ∀ j, Signs p8068 (bank8068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8069 := params 4
abbrev ray8069 := rays 4
def bank8069 : Fin 2 → Cell := twoBank p8069 ray8069
theorem signs8069 : ∀ j, Signs p8069 (bank8069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8070 := params 5
abbrev ray8070 := rays 5
def bank8070 : Fin 2 → Cell := twoBank p8070 ray8070
theorem signs8070 : ∀ j, Signs p8070 (bank8070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8071 := params 6
abbrev ray8071 := rays 6
def bank8071 : Fin 2 → Cell := twoBank p8071 ray8071
theorem signs8071 : ∀ j, Signs p8071 (bank8071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8072 := params 7
abbrev ray8072 := rays 7
def bank8072 : Fin 2 → Cell := twoBank p8072 ray8072
theorem signs8072 : ∀ j, Signs p8072 (bank8072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8073 := params 8
abbrev ray8073 := rays 8
def bank8073 : Fin 2 → Cell := twoBank p8073 ray8073
theorem signs8073 : ∀ j, Signs p8073 (bank8073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8074 := params 9
abbrev ray8074 := rays 9
def bank8074 : Fin 2 → Cell := twoBank p8074 ray8074
theorem signs8074 : ∀ j, Signs p8074 (bank8074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8075 := params 10
abbrev ray8075 := rays 10
def bank8075 : Fin 2 → Cell := twoBank p8075 ray8075
theorem signs8075 : ∀ j, Signs p8075 (bank8075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8076 := params 11
abbrev ray8076 := rays 11
def bank8076 : Fin 2 → Cell := twoBank p8076 ray8076
theorem signs8076 : ∀ j, Signs p8076 (bank8076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8077 := params 12
abbrev ray8077 := rays 12
def bank8077 : Fin 2 → Cell := twoBank p8077 ray8077
theorem signs8077 : ∀ j, Signs p8077 (bank8077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8078 := params 13
abbrev ray8078 := rays 13
def bank8078 : Fin 2 → Cell := twoBank p8078 ray8078
theorem signs8078 : ∀ j, Signs p8078 (bank8078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8079 := params 14
abbrev ray8079 := rays 14
def bank8079 : Fin 2 → Cell := twoBank p8079 ray8079
theorem signs8079 : ∀ j, Signs p8079 (bank8079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8080 := params 15
abbrev ray8080 := rays 15
def bank8080 : Fin 2 → Cell := twoBank p8080 ray8080
theorem signs8080 : ∀ j, Signs p8080 (bank8080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8081 := params 16
abbrev ray8081 := rays 16
def bank8081 : Fin 2 → Cell := twoBank p8081 ray8081
theorem signs8081 : ∀ j, Signs p8081 (bank8081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8082 := params 17
abbrev ray8082 := rays 17
def bank8082 : Fin 2 → Cell := twoBank p8082 ray8082
theorem signs8082 : ∀ j, Signs p8082 (bank8082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8083 := params 18
abbrev ray8083 := rays 18
def bank8083 : Fin 2 → Cell := twoBank p8083 ray8083
theorem signs8083 : ∀ j, Signs p8083 (bank8083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8084 := params 19
abbrev ray8084 := rays 19
def bank8084 : Fin 2 → Cell := twoBank p8084 ray8084
theorem signs8084 : ∀ j, Signs p8084 (bank8084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8085 := params 20
abbrev ray8085 := rays 20
def bank8085 : Fin 2 → Cell := twoBank p8085 ray8085
theorem signs8085 : ∀ j, Signs p8085 (bank8085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8086 := params 21
abbrev ray8086 := rays 21
def bank8086 : Fin 2 → Cell := twoBank p8086 ray8086
theorem signs8086 : ∀ j, Signs p8086 (bank8086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8087 := params 22
abbrev ray8087 := rays 22
def bank8087 : Fin 2 → Cell := twoBank p8087 ray8087
theorem signs8087 : ∀ j, Signs p8087 (bank8087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8088 := params 23
abbrev ray8088 := rays 23
def bank8088 : Fin 2 → Cell := twoBank p8088 ray8088
theorem signs8088 : ∀ j, Signs p8088 (bank8088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8089 := params 24
abbrev ray8089 := rays 24
def bank8089 : Fin 2 → Cell := twoBank p8089 ray8089
theorem signs8089 : ∀ j, Signs p8089 (bank8089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8090 := params 25
abbrev ray8090 := rays 25
def bank8090 : Fin 2 → Cell := twoBank p8090 ray8090
theorem signs8090 : ∀ j, Signs p8090 (bank8090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8091 := params 26
abbrev ray8091 := rays 26
def bank8091 : Fin 2 → Cell := twoBank p8091 ray8091
theorem signs8091 : ∀ j, Signs p8091 (bank8091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8092 := params 27
abbrev ray8092 := rays 27
def bank8092 : Fin 2 → Cell := twoBank p8092 ray8092
theorem signs8092 : ∀ j, Signs p8092 (bank8092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8093 := params 28
abbrev ray8093 := rays 28
def bank8093 : Fin 2 → Cell := twoBank p8093 ray8093
theorem signs8093 : ∀ j, Signs p8093 (bank8093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8094 := params 29
abbrev ray8094 := rays 29
def bank8094 : Fin 2 → Cell := twoBank p8094 ray8094
theorem signs8094 : ∀ j, Signs p8094 (bank8094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8095 := params 30
abbrev ray8095 := rays 30
def bank8095 : Fin 2 → Cell := twoBank p8095 ray8095
theorem signs8095 : ∀ j, Signs p8095 (bank8095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8096 := params 31
abbrev ray8096 := rays 31
def bank8096 : Fin 2 → Cell := twoBank p8096 ray8096
theorem signs8096 : ∀ j, Signs p8096 (bank8096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08065_08096
