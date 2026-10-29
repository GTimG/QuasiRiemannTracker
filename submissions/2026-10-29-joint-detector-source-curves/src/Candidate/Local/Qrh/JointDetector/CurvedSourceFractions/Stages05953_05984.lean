/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05953_05984
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98780298992492,98780020030680,98779741045662,98779462037440,98779183006014,98778903951385,98778624873554,98778345772522,98778066648290,98777787500859,98777508330230,98777229136403,98776949919380,98776670679161,98776391415747,98776112129139,98775832819338,98775553486345,98775274130161,98774994750786,98774715348222,98774435922469,98774156473529,98773877001402,98773597506089,98773317987591,98773038445909,98772758881044,98772479292996,98772199681767,98771920047357,98771640389767,98771360708999]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5952+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5953 := params 0
abbrev ray5953 := rays 0
def bank5953 : Fin 2 → Cell := twoBank p5953 ray5953
theorem signs5953 : ∀ j, Signs p5953 (bank5953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5954 := params 1
abbrev ray5954 := rays 1
def bank5954 : Fin 2 → Cell := twoBank p5954 ray5954
theorem signs5954 : ∀ j, Signs p5954 (bank5954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5955 := params 2
abbrev ray5955 := rays 2
def bank5955 : Fin 2 → Cell := twoBank p5955 ray5955
theorem signs5955 : ∀ j, Signs p5955 (bank5955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5956 := params 3
abbrev ray5956 := rays 3
def bank5956 : Fin 2 → Cell := twoBank p5956 ray5956
theorem signs5956 : ∀ j, Signs p5956 (bank5956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5957 := params 4
abbrev ray5957 := rays 4
def bank5957 : Fin 2 → Cell := twoBank p5957 ray5957
theorem signs5957 : ∀ j, Signs p5957 (bank5957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5958 := params 5
abbrev ray5958 := rays 5
def bank5958 : Fin 2 → Cell := twoBank p5958 ray5958
theorem signs5958 : ∀ j, Signs p5958 (bank5958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5959 := params 6
abbrev ray5959 := rays 6
def bank5959 : Fin 2 → Cell := twoBank p5959 ray5959
theorem signs5959 : ∀ j, Signs p5959 (bank5959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5960 := params 7
abbrev ray5960 := rays 7
def bank5960 : Fin 2 → Cell := twoBank p5960 ray5960
theorem signs5960 : ∀ j, Signs p5960 (bank5960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5961 := params 8
abbrev ray5961 := rays 8
def bank5961 : Fin 2 → Cell := twoBank p5961 ray5961
theorem signs5961 : ∀ j, Signs p5961 (bank5961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5962 := params 9
abbrev ray5962 := rays 9
def bank5962 : Fin 2 → Cell := twoBank p5962 ray5962
theorem signs5962 : ∀ j, Signs p5962 (bank5962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5963 := params 10
abbrev ray5963 := rays 10
def bank5963 : Fin 2 → Cell := twoBank p5963 ray5963
theorem signs5963 : ∀ j, Signs p5963 (bank5963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5964 := params 11
abbrev ray5964 := rays 11
def bank5964 : Fin 2 → Cell := twoBank p5964 ray5964
theorem signs5964 : ∀ j, Signs p5964 (bank5964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5965 := params 12
abbrev ray5965 := rays 12
def bank5965 : Fin 2 → Cell := twoBank p5965 ray5965
theorem signs5965 : ∀ j, Signs p5965 (bank5965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5966 := params 13
abbrev ray5966 := rays 13
def bank5966 : Fin 2 → Cell := twoBank p5966 ray5966
theorem signs5966 : ∀ j, Signs p5966 (bank5966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5967 := params 14
abbrev ray5967 := rays 14
def bank5967 : Fin 2 → Cell := twoBank p5967 ray5967
theorem signs5967 : ∀ j, Signs p5967 (bank5967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5968 := params 15
abbrev ray5968 := rays 15
def bank5968 : Fin 2 → Cell := twoBank p5968 ray5968
theorem signs5968 : ∀ j, Signs p5968 (bank5968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5969 := params 16
abbrev ray5969 := rays 16
def bank5969 : Fin 2 → Cell := twoBank p5969 ray5969
theorem signs5969 : ∀ j, Signs p5969 (bank5969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5970 := params 17
abbrev ray5970 := rays 17
def bank5970 : Fin 2 → Cell := twoBank p5970 ray5970
theorem signs5970 : ∀ j, Signs p5970 (bank5970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5971 := params 18
abbrev ray5971 := rays 18
def bank5971 : Fin 2 → Cell := twoBank p5971 ray5971
theorem signs5971 : ∀ j, Signs p5971 (bank5971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5972 := params 19
abbrev ray5972 := rays 19
def bank5972 : Fin 2 → Cell := twoBank p5972 ray5972
theorem signs5972 : ∀ j, Signs p5972 (bank5972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5973 := params 20
abbrev ray5973 := rays 20
def bank5973 : Fin 2 → Cell := twoBank p5973 ray5973
theorem signs5973 : ∀ j, Signs p5973 (bank5973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5974 := params 21
abbrev ray5974 := rays 21
def bank5974 : Fin 2 → Cell := twoBank p5974 ray5974
theorem signs5974 : ∀ j, Signs p5974 (bank5974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5975 := params 22
abbrev ray5975 := rays 22
def bank5975 : Fin 2 → Cell := twoBank p5975 ray5975
theorem signs5975 : ∀ j, Signs p5975 (bank5975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5976 := params 23
abbrev ray5976 := rays 23
def bank5976 : Fin 2 → Cell := twoBank p5976 ray5976
theorem signs5976 : ∀ j, Signs p5976 (bank5976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5977 := params 24
abbrev ray5977 := rays 24
def bank5977 : Fin 2 → Cell := twoBank p5977 ray5977
theorem signs5977 : ∀ j, Signs p5977 (bank5977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5978 := params 25
abbrev ray5978 := rays 25
def bank5978 : Fin 2 → Cell := twoBank p5978 ray5978
theorem signs5978 : ∀ j, Signs p5978 (bank5978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5979 := params 26
abbrev ray5979 := rays 26
def bank5979 : Fin 2 → Cell := twoBank p5979 ray5979
theorem signs5979 : ∀ j, Signs p5979 (bank5979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5980 := params 27
abbrev ray5980 := rays 27
def bank5980 : Fin 2 → Cell := twoBank p5980 ray5980
theorem signs5980 : ∀ j, Signs p5980 (bank5980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5981 := params 28
abbrev ray5981 := rays 28
def bank5981 : Fin 2 → Cell := twoBank p5981 ray5981
theorem signs5981 : ∀ j, Signs p5981 (bank5981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5982 := params 29
abbrev ray5982 := rays 29
def bank5982 : Fin 2 → Cell := twoBank p5982 ray5982
theorem signs5982 : ∀ j, Signs p5982 (bank5982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5983 := params 30
abbrev ray5983 := rays 30
def bank5983 : Fin 2 → Cell := twoBank p5983 ray5983
theorem signs5983 : ∀ j, Signs p5983 (bank5983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5984 := params 31
abbrev ray5984 := rays 31
def bank5984 : Fin 2 → Cell := twoBank p5984 ray5984
theorem signs5984 : ∀ j, Signs p5984 (bank5984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05953_05984
