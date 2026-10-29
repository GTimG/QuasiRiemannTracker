/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08929_08960
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97850969375372,97850624872540,97850280348738,97849935803967,97849591238228,97849246651522,97848902043849,97848557415209,97848212765604,97847868095034,97847523403499,97847178691001,97846833957539,97846489203115,97846144427729,97845799631382,97845454814074,97845109975806,97844765116579,97844420236393,97844075335249,97843730413147,97843385470088,97843040506073,97842695521102,97842350515176,97842005488296,97841660440462,97841315371675,97840970281936,97840625171245,97840280039602,97839934887009]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8928+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8929 := params 0
abbrev ray8929 := rays 0
def bank8929 : Fin 2 → Cell := twoBank p8929 ray8929
theorem signs8929 : ∀ j, Signs p8929 (bank8929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8930 := params 1
abbrev ray8930 := rays 1
def bank8930 : Fin 2 → Cell := twoBank p8930 ray8930
theorem signs8930 : ∀ j, Signs p8930 (bank8930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8931 := params 2
abbrev ray8931 := rays 2
def bank8931 : Fin 2 → Cell := twoBank p8931 ray8931
theorem signs8931 : ∀ j, Signs p8931 (bank8931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8932 := params 3
abbrev ray8932 := rays 3
def bank8932 : Fin 2 → Cell := twoBank p8932 ray8932
theorem signs8932 : ∀ j, Signs p8932 (bank8932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8933 := params 4
abbrev ray8933 := rays 4
def bank8933 : Fin 2 → Cell := twoBank p8933 ray8933
theorem signs8933 : ∀ j, Signs p8933 (bank8933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8934 := params 5
abbrev ray8934 := rays 5
def bank8934 : Fin 2 → Cell := twoBank p8934 ray8934
theorem signs8934 : ∀ j, Signs p8934 (bank8934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8935 := params 6
abbrev ray8935 := rays 6
def bank8935 : Fin 2 → Cell := twoBank p8935 ray8935
theorem signs8935 : ∀ j, Signs p8935 (bank8935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8936 := params 7
abbrev ray8936 := rays 7
def bank8936 : Fin 2 → Cell := twoBank p8936 ray8936
theorem signs8936 : ∀ j, Signs p8936 (bank8936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8937 := params 8
abbrev ray8937 := rays 8
def bank8937 : Fin 2 → Cell := twoBank p8937 ray8937
theorem signs8937 : ∀ j, Signs p8937 (bank8937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8938 := params 9
abbrev ray8938 := rays 9
def bank8938 : Fin 2 → Cell := twoBank p8938 ray8938
theorem signs8938 : ∀ j, Signs p8938 (bank8938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8939 := params 10
abbrev ray8939 := rays 10
def bank8939 : Fin 2 → Cell := twoBank p8939 ray8939
theorem signs8939 : ∀ j, Signs p8939 (bank8939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8940 := params 11
abbrev ray8940 := rays 11
def bank8940 : Fin 2 → Cell := twoBank p8940 ray8940
theorem signs8940 : ∀ j, Signs p8940 (bank8940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8941 := params 12
abbrev ray8941 := rays 12
def bank8941 : Fin 2 → Cell := twoBank p8941 ray8941
theorem signs8941 : ∀ j, Signs p8941 (bank8941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8942 := params 13
abbrev ray8942 := rays 13
def bank8942 : Fin 2 → Cell := twoBank p8942 ray8942
theorem signs8942 : ∀ j, Signs p8942 (bank8942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8943 := params 14
abbrev ray8943 := rays 14
def bank8943 : Fin 2 → Cell := twoBank p8943 ray8943
theorem signs8943 : ∀ j, Signs p8943 (bank8943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8944 := params 15
abbrev ray8944 := rays 15
def bank8944 : Fin 2 → Cell := twoBank p8944 ray8944
theorem signs8944 : ∀ j, Signs p8944 (bank8944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8945 := params 16
abbrev ray8945 := rays 16
def bank8945 : Fin 2 → Cell := twoBank p8945 ray8945
theorem signs8945 : ∀ j, Signs p8945 (bank8945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8946 := params 17
abbrev ray8946 := rays 17
def bank8946 : Fin 2 → Cell := twoBank p8946 ray8946
theorem signs8946 : ∀ j, Signs p8946 (bank8946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8947 := params 18
abbrev ray8947 := rays 18
def bank8947 : Fin 2 → Cell := twoBank p8947 ray8947
theorem signs8947 : ∀ j, Signs p8947 (bank8947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8948 := params 19
abbrev ray8948 := rays 19
def bank8948 : Fin 2 → Cell := twoBank p8948 ray8948
theorem signs8948 : ∀ j, Signs p8948 (bank8948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8949 := params 20
abbrev ray8949 := rays 20
def bank8949 : Fin 2 → Cell := twoBank p8949 ray8949
theorem signs8949 : ∀ j, Signs p8949 (bank8949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8950 := params 21
abbrev ray8950 := rays 21
def bank8950 : Fin 2 → Cell := twoBank p8950 ray8950
theorem signs8950 : ∀ j, Signs p8950 (bank8950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8951 := params 22
abbrev ray8951 := rays 22
def bank8951 : Fin 2 → Cell := twoBank p8951 ray8951
theorem signs8951 : ∀ j, Signs p8951 (bank8951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8952 := params 23
abbrev ray8952 := rays 23
def bank8952 : Fin 2 → Cell := twoBank p8952 ray8952
theorem signs8952 : ∀ j, Signs p8952 (bank8952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8953 := params 24
abbrev ray8953 := rays 24
def bank8953 : Fin 2 → Cell := twoBank p8953 ray8953
theorem signs8953 : ∀ j, Signs p8953 (bank8953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8954 := params 25
abbrev ray8954 := rays 25
def bank8954 : Fin 2 → Cell := twoBank p8954 ray8954
theorem signs8954 : ∀ j, Signs p8954 (bank8954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8955 := params 26
abbrev ray8955 := rays 26
def bank8955 : Fin 2 → Cell := twoBank p8955 ray8955
theorem signs8955 : ∀ j, Signs p8955 (bank8955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8956 := params 27
abbrev ray8956 := rays 27
def bank8956 : Fin 2 → Cell := twoBank p8956 ray8956
theorem signs8956 : ∀ j, Signs p8956 (bank8956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8957 := params 28
abbrev ray8957 := rays 28
def bank8957 : Fin 2 → Cell := twoBank p8957 ray8957
theorem signs8957 : ∀ j, Signs p8957 (bank8957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8958 := params 29
abbrev ray8958 := rays 29
def bank8958 : Fin 2 → Cell := twoBank p8958 ray8958
theorem signs8958 : ∀ j, Signs p8958 (bank8958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8959 := params 30
abbrev ray8959 := rays 30
def bank8959 : Fin 2 → Cell := twoBank p8959 ray8959
theorem signs8959 : ∀ j, Signs p8959 (bank8959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8960 := params 31
abbrev ray8960 := rays 31
def bank8960 : Fin 2 → Cell := twoBank p8960 ray8960
theorem signs8960 : ∀ j, Signs p8960 (bank8960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08929_08960
