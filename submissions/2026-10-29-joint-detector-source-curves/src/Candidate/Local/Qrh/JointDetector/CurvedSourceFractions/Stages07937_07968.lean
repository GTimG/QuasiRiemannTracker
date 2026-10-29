/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07937_07968
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98182282559791,98181959180449,98181635779477,98181312356875,98180988912644,98180665446785,98180341959299,98180018450186,98179694919447,98179371367082,98179047793093,98178724197480,98178400580243,98178076941384,98177753280903,98177429598801,98177105895078,98176782169736,98176458422775,98176134654195,98175810863998,98175487052184,98175163218753,98174839363707,98174515487046,98174191588771,98173867668882,98173543727381,98173219764268,98172895779543,98172571773208,98172247745263,98171923695709]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7936+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7937 := params 0
abbrev ray7937 := rays 0
def bank7937 : Fin 2 → Cell := twoBank p7937 ray7937
theorem signs7937 : ∀ j, Signs p7937 (bank7937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7938 := params 1
abbrev ray7938 := rays 1
def bank7938 : Fin 2 → Cell := twoBank p7938 ray7938
theorem signs7938 : ∀ j, Signs p7938 (bank7938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7939 := params 2
abbrev ray7939 := rays 2
def bank7939 : Fin 2 → Cell := twoBank p7939 ray7939
theorem signs7939 : ∀ j, Signs p7939 (bank7939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7940 := params 3
abbrev ray7940 := rays 3
def bank7940 : Fin 2 → Cell := twoBank p7940 ray7940
theorem signs7940 : ∀ j, Signs p7940 (bank7940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7941 := params 4
abbrev ray7941 := rays 4
def bank7941 : Fin 2 → Cell := twoBank p7941 ray7941
theorem signs7941 : ∀ j, Signs p7941 (bank7941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7942 := params 5
abbrev ray7942 := rays 5
def bank7942 : Fin 2 → Cell := twoBank p7942 ray7942
theorem signs7942 : ∀ j, Signs p7942 (bank7942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7943 := params 6
abbrev ray7943 := rays 6
def bank7943 : Fin 2 → Cell := twoBank p7943 ray7943
theorem signs7943 : ∀ j, Signs p7943 (bank7943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7944 := params 7
abbrev ray7944 := rays 7
def bank7944 : Fin 2 → Cell := twoBank p7944 ray7944
theorem signs7944 : ∀ j, Signs p7944 (bank7944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7945 := params 8
abbrev ray7945 := rays 8
def bank7945 : Fin 2 → Cell := twoBank p7945 ray7945
theorem signs7945 : ∀ j, Signs p7945 (bank7945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7946 := params 9
abbrev ray7946 := rays 9
def bank7946 : Fin 2 → Cell := twoBank p7946 ray7946
theorem signs7946 : ∀ j, Signs p7946 (bank7946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7947 := params 10
abbrev ray7947 := rays 10
def bank7947 : Fin 2 → Cell := twoBank p7947 ray7947
theorem signs7947 : ∀ j, Signs p7947 (bank7947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7948 := params 11
abbrev ray7948 := rays 11
def bank7948 : Fin 2 → Cell := twoBank p7948 ray7948
theorem signs7948 : ∀ j, Signs p7948 (bank7948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7949 := params 12
abbrev ray7949 := rays 12
def bank7949 : Fin 2 → Cell := twoBank p7949 ray7949
theorem signs7949 : ∀ j, Signs p7949 (bank7949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7950 := params 13
abbrev ray7950 := rays 13
def bank7950 : Fin 2 → Cell := twoBank p7950 ray7950
theorem signs7950 : ∀ j, Signs p7950 (bank7950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7951 := params 14
abbrev ray7951 := rays 14
def bank7951 : Fin 2 → Cell := twoBank p7951 ray7951
theorem signs7951 : ∀ j, Signs p7951 (bank7951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7952 := params 15
abbrev ray7952 := rays 15
def bank7952 : Fin 2 → Cell := twoBank p7952 ray7952
theorem signs7952 : ∀ j, Signs p7952 (bank7952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7953 := params 16
abbrev ray7953 := rays 16
def bank7953 : Fin 2 → Cell := twoBank p7953 ray7953
theorem signs7953 : ∀ j, Signs p7953 (bank7953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7954 := params 17
abbrev ray7954 := rays 17
def bank7954 : Fin 2 → Cell := twoBank p7954 ray7954
theorem signs7954 : ∀ j, Signs p7954 (bank7954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7955 := params 18
abbrev ray7955 := rays 18
def bank7955 : Fin 2 → Cell := twoBank p7955 ray7955
theorem signs7955 : ∀ j, Signs p7955 (bank7955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7956 := params 19
abbrev ray7956 := rays 19
def bank7956 : Fin 2 → Cell := twoBank p7956 ray7956
theorem signs7956 : ∀ j, Signs p7956 (bank7956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7957 := params 20
abbrev ray7957 := rays 20
def bank7957 : Fin 2 → Cell := twoBank p7957 ray7957
theorem signs7957 : ∀ j, Signs p7957 (bank7957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7958 := params 21
abbrev ray7958 := rays 21
def bank7958 : Fin 2 → Cell := twoBank p7958 ray7958
theorem signs7958 : ∀ j, Signs p7958 (bank7958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7959 := params 22
abbrev ray7959 := rays 22
def bank7959 : Fin 2 → Cell := twoBank p7959 ray7959
theorem signs7959 : ∀ j, Signs p7959 (bank7959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7960 := params 23
abbrev ray7960 := rays 23
def bank7960 : Fin 2 → Cell := twoBank p7960 ray7960
theorem signs7960 : ∀ j, Signs p7960 (bank7960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7961 := params 24
abbrev ray7961 := rays 24
def bank7961 : Fin 2 → Cell := twoBank p7961 ray7961
theorem signs7961 : ∀ j, Signs p7961 (bank7961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7962 := params 25
abbrev ray7962 := rays 25
def bank7962 : Fin 2 → Cell := twoBank p7962 ray7962
theorem signs7962 : ∀ j, Signs p7962 (bank7962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7963 := params 26
abbrev ray7963 := rays 26
def bank7963 : Fin 2 → Cell := twoBank p7963 ray7963
theorem signs7963 : ∀ j, Signs p7963 (bank7963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7964 := params 27
abbrev ray7964 := rays 27
def bank7964 : Fin 2 → Cell := twoBank p7964 ray7964
theorem signs7964 : ∀ j, Signs p7964 (bank7964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7965 := params 28
abbrev ray7965 := rays 28
def bank7965 : Fin 2 → Cell := twoBank p7965 ray7965
theorem signs7965 : ∀ j, Signs p7965 (bank7965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7966 := params 29
abbrev ray7966 := rays 29
def bank7966 : Fin 2 → Cell := twoBank p7966 ray7966
theorem signs7966 : ∀ j, Signs p7966 (bank7966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7967 := params 30
abbrev ray7967 := rays 30
def bank7967 : Fin 2 → Cell := twoBank p7967 ray7967
theorem signs7967 : ∀ j, Signs p7967 (bank7967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7968 := params 31
abbrev ray7968 := rays 31
def bank7968 : Fin 2 → Cell := twoBank p7968 ray7968
theorem signs7968 : ∀ j, Signs p7968 (bank7968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07937_07968
