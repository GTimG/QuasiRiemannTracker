/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04929_04960
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99053612987490,99053358274542,99053103537420,99052848776124,99052593990656,99052339181017,99052084347208,99051829489229,99051574607082,99051319700768,99051064770287,99050809815641,99050554836831,99050299833857,99050044806721,99049789755424,99049534679967,99049279580350,99049024456575,99048769308643,99048514136555,99048258940311,99048003719913,99047748475362,99047493206659,99047237913804,99046982596799,99046727255645,99046471890343,99046216500893,99045961087297,99045705649556,99045450187671]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4928+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4929 := params 0
abbrev ray4929 := rays 0
def bank4929 : Fin 2 → Cell := twoBank p4929 ray4929
theorem signs4929 : ∀ j, Signs p4929 (bank4929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4930 := params 1
abbrev ray4930 := rays 1
def bank4930 : Fin 2 → Cell := twoBank p4930 ray4930
theorem signs4930 : ∀ j, Signs p4930 (bank4930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4931 := params 2
abbrev ray4931 := rays 2
def bank4931 : Fin 2 → Cell := twoBank p4931 ray4931
theorem signs4931 : ∀ j, Signs p4931 (bank4931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4932 := params 3
abbrev ray4932 := rays 3
def bank4932 : Fin 2 → Cell := twoBank p4932 ray4932
theorem signs4932 : ∀ j, Signs p4932 (bank4932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4933 := params 4
abbrev ray4933 := rays 4
def bank4933 : Fin 2 → Cell := twoBank p4933 ray4933
theorem signs4933 : ∀ j, Signs p4933 (bank4933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4934 := params 5
abbrev ray4934 := rays 5
def bank4934 : Fin 2 → Cell := twoBank p4934 ray4934
theorem signs4934 : ∀ j, Signs p4934 (bank4934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4935 := params 6
abbrev ray4935 := rays 6
def bank4935 : Fin 2 → Cell := twoBank p4935 ray4935
theorem signs4935 : ∀ j, Signs p4935 (bank4935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4936 := params 7
abbrev ray4936 := rays 7
def bank4936 : Fin 2 → Cell := twoBank p4936 ray4936
theorem signs4936 : ∀ j, Signs p4936 (bank4936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4937 := params 8
abbrev ray4937 := rays 8
def bank4937 : Fin 2 → Cell := twoBank p4937 ray4937
theorem signs4937 : ∀ j, Signs p4937 (bank4937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4938 := params 9
abbrev ray4938 := rays 9
def bank4938 : Fin 2 → Cell := twoBank p4938 ray4938
theorem signs4938 : ∀ j, Signs p4938 (bank4938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4939 := params 10
abbrev ray4939 := rays 10
def bank4939 : Fin 2 → Cell := twoBank p4939 ray4939
theorem signs4939 : ∀ j, Signs p4939 (bank4939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4940 := params 11
abbrev ray4940 := rays 11
def bank4940 : Fin 2 → Cell := twoBank p4940 ray4940
theorem signs4940 : ∀ j, Signs p4940 (bank4940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4941 := params 12
abbrev ray4941 := rays 12
def bank4941 : Fin 2 → Cell := twoBank p4941 ray4941
theorem signs4941 : ∀ j, Signs p4941 (bank4941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4942 := params 13
abbrev ray4942 := rays 13
def bank4942 : Fin 2 → Cell := twoBank p4942 ray4942
theorem signs4942 : ∀ j, Signs p4942 (bank4942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4943 := params 14
abbrev ray4943 := rays 14
def bank4943 : Fin 2 → Cell := twoBank p4943 ray4943
theorem signs4943 : ∀ j, Signs p4943 (bank4943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4944 := params 15
abbrev ray4944 := rays 15
def bank4944 : Fin 2 → Cell := twoBank p4944 ray4944
theorem signs4944 : ∀ j, Signs p4944 (bank4944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4945 := params 16
abbrev ray4945 := rays 16
def bank4945 : Fin 2 → Cell := twoBank p4945 ray4945
theorem signs4945 : ∀ j, Signs p4945 (bank4945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4946 := params 17
abbrev ray4946 := rays 17
def bank4946 : Fin 2 → Cell := twoBank p4946 ray4946
theorem signs4946 : ∀ j, Signs p4946 (bank4946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4947 := params 18
abbrev ray4947 := rays 18
def bank4947 : Fin 2 → Cell := twoBank p4947 ray4947
theorem signs4947 : ∀ j, Signs p4947 (bank4947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4948 := params 19
abbrev ray4948 := rays 19
def bank4948 : Fin 2 → Cell := twoBank p4948 ray4948
theorem signs4948 : ∀ j, Signs p4948 (bank4948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4949 := params 20
abbrev ray4949 := rays 20
def bank4949 : Fin 2 → Cell := twoBank p4949 ray4949
theorem signs4949 : ∀ j, Signs p4949 (bank4949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4950 := params 21
abbrev ray4950 := rays 21
def bank4950 : Fin 2 → Cell := twoBank p4950 ray4950
theorem signs4950 : ∀ j, Signs p4950 (bank4950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4951 := params 22
abbrev ray4951 := rays 22
def bank4951 : Fin 2 → Cell := twoBank p4951 ray4951
theorem signs4951 : ∀ j, Signs p4951 (bank4951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4952 := params 23
abbrev ray4952 := rays 23
def bank4952 : Fin 2 → Cell := twoBank p4952 ray4952
theorem signs4952 : ∀ j, Signs p4952 (bank4952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4953 := params 24
abbrev ray4953 := rays 24
def bank4953 : Fin 2 → Cell := twoBank p4953 ray4953
theorem signs4953 : ∀ j, Signs p4953 (bank4953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4954 := params 25
abbrev ray4954 := rays 25
def bank4954 : Fin 2 → Cell := twoBank p4954 ray4954
theorem signs4954 : ∀ j, Signs p4954 (bank4954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4955 := params 26
abbrev ray4955 := rays 26
def bank4955 : Fin 2 → Cell := twoBank p4955 ray4955
theorem signs4955 : ∀ j, Signs p4955 (bank4955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4956 := params 27
abbrev ray4956 := rays 27
def bank4956 : Fin 2 → Cell := twoBank p4956 ray4956
theorem signs4956 : ∀ j, Signs p4956 (bank4956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4957 := params 28
abbrev ray4957 := rays 28
def bank4957 : Fin 2 → Cell := twoBank p4957 ray4957
theorem signs4957 : ∀ j, Signs p4957 (bank4957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4958 := params 29
abbrev ray4958 := rays 29
def bank4958 : Fin 2 → Cell := twoBank p4958 ray4958
theorem signs4958 : ∀ j, Signs p4958 (bank4958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4959 := params 30
abbrev ray4959 := rays 30
def bank4959 : Fin 2 → Cell := twoBank p4959 ray4959
theorem signs4959 : ∀ j, Signs p4959 (bank4959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4960 := params 31
abbrev ray4960 := rays 31
def bank4960 : Fin 2 → Cell := twoBank p4960 ray4960
theorem signs4960 : ∀ j, Signs p4960 (bank4960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04929_04960
