/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03937_03968
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99294212628359,99293982411815,99293752170037,99293521903026,99293291610784,99293061293311,99292830950609,99292600582679,99292370189522,99292139771139,99291909327531,99291678858700,99291448364646,99291217845371,99290987300876,99290756731162,99290526136230,99290295516081,99290064870716,99289834200137,99289603504344,99289372783339,99289142037123,99288911265697,99288680469062,99288449647219,99288218800170,99287987927915,99287757030456,99287526107794,99287295159930,99287064186865,99286833188600]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3936+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3937 := params 0
abbrev ray3937 := rays 0
def bank3937 : Fin 2 → Cell := twoBank p3937 ray3937
theorem signs3937 : ∀ j, Signs p3937 (bank3937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3938 := params 1
abbrev ray3938 := rays 1
def bank3938 : Fin 2 → Cell := twoBank p3938 ray3938
theorem signs3938 : ∀ j, Signs p3938 (bank3938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3939 := params 2
abbrev ray3939 := rays 2
def bank3939 : Fin 2 → Cell := twoBank p3939 ray3939
theorem signs3939 : ∀ j, Signs p3939 (bank3939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3940 := params 3
abbrev ray3940 := rays 3
def bank3940 : Fin 2 → Cell := twoBank p3940 ray3940
theorem signs3940 : ∀ j, Signs p3940 (bank3940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3941 := params 4
abbrev ray3941 := rays 4
def bank3941 : Fin 2 → Cell := twoBank p3941 ray3941
theorem signs3941 : ∀ j, Signs p3941 (bank3941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3942 := params 5
abbrev ray3942 := rays 5
def bank3942 : Fin 2 → Cell := twoBank p3942 ray3942
theorem signs3942 : ∀ j, Signs p3942 (bank3942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3943 := params 6
abbrev ray3943 := rays 6
def bank3943 : Fin 2 → Cell := twoBank p3943 ray3943
theorem signs3943 : ∀ j, Signs p3943 (bank3943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3944 := params 7
abbrev ray3944 := rays 7
def bank3944 : Fin 2 → Cell := twoBank p3944 ray3944
theorem signs3944 : ∀ j, Signs p3944 (bank3944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3945 := params 8
abbrev ray3945 := rays 8
def bank3945 : Fin 2 → Cell := twoBank p3945 ray3945
theorem signs3945 : ∀ j, Signs p3945 (bank3945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3946 := params 9
abbrev ray3946 := rays 9
def bank3946 : Fin 2 → Cell := twoBank p3946 ray3946
theorem signs3946 : ∀ j, Signs p3946 (bank3946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3947 := params 10
abbrev ray3947 := rays 10
def bank3947 : Fin 2 → Cell := twoBank p3947 ray3947
theorem signs3947 : ∀ j, Signs p3947 (bank3947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3948 := params 11
abbrev ray3948 := rays 11
def bank3948 : Fin 2 → Cell := twoBank p3948 ray3948
theorem signs3948 : ∀ j, Signs p3948 (bank3948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3949 := params 12
abbrev ray3949 := rays 12
def bank3949 : Fin 2 → Cell := twoBank p3949 ray3949
theorem signs3949 : ∀ j, Signs p3949 (bank3949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3950 := params 13
abbrev ray3950 := rays 13
def bank3950 : Fin 2 → Cell := twoBank p3950 ray3950
theorem signs3950 : ∀ j, Signs p3950 (bank3950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3951 := params 14
abbrev ray3951 := rays 14
def bank3951 : Fin 2 → Cell := twoBank p3951 ray3951
theorem signs3951 : ∀ j, Signs p3951 (bank3951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3952 := params 15
abbrev ray3952 := rays 15
def bank3952 : Fin 2 → Cell := twoBank p3952 ray3952
theorem signs3952 : ∀ j, Signs p3952 (bank3952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3953 := params 16
abbrev ray3953 := rays 16
def bank3953 : Fin 2 → Cell := twoBank p3953 ray3953
theorem signs3953 : ∀ j, Signs p3953 (bank3953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3954 := params 17
abbrev ray3954 := rays 17
def bank3954 : Fin 2 → Cell := twoBank p3954 ray3954
theorem signs3954 : ∀ j, Signs p3954 (bank3954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3955 := params 18
abbrev ray3955 := rays 18
def bank3955 : Fin 2 → Cell := twoBank p3955 ray3955
theorem signs3955 : ∀ j, Signs p3955 (bank3955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3956 := params 19
abbrev ray3956 := rays 19
def bank3956 : Fin 2 → Cell := twoBank p3956 ray3956
theorem signs3956 : ∀ j, Signs p3956 (bank3956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3957 := params 20
abbrev ray3957 := rays 20
def bank3957 : Fin 2 → Cell := twoBank p3957 ray3957
theorem signs3957 : ∀ j, Signs p3957 (bank3957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3958 := params 21
abbrev ray3958 := rays 21
def bank3958 : Fin 2 → Cell := twoBank p3958 ray3958
theorem signs3958 : ∀ j, Signs p3958 (bank3958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3959 := params 22
abbrev ray3959 := rays 22
def bank3959 : Fin 2 → Cell := twoBank p3959 ray3959
theorem signs3959 : ∀ j, Signs p3959 (bank3959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3960 := params 23
abbrev ray3960 := rays 23
def bank3960 : Fin 2 → Cell := twoBank p3960 ray3960
theorem signs3960 : ∀ j, Signs p3960 (bank3960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3961 := params 24
abbrev ray3961 := rays 24
def bank3961 : Fin 2 → Cell := twoBank p3961 ray3961
theorem signs3961 : ∀ j, Signs p3961 (bank3961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3962 := params 25
abbrev ray3962 := rays 25
def bank3962 : Fin 2 → Cell := twoBank p3962 ray3962
theorem signs3962 : ∀ j, Signs p3962 (bank3962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3963 := params 26
abbrev ray3963 := rays 26
def bank3963 : Fin 2 → Cell := twoBank p3963 ray3963
theorem signs3963 : ∀ j, Signs p3963 (bank3963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3964 := params 27
abbrev ray3964 := rays 27
def bank3964 : Fin 2 → Cell := twoBank p3964 ray3964
theorem signs3964 : ∀ j, Signs p3964 (bank3964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3965 := params 28
abbrev ray3965 := rays 28
def bank3965 : Fin 2 → Cell := twoBank p3965 ray3965
theorem signs3965 : ∀ j, Signs p3965 (bank3965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3966 := params 29
abbrev ray3966 := rays 29
def bank3966 : Fin 2 → Cell := twoBank p3966 ray3966
theorem signs3966 : ∀ j, Signs p3966 (bank3966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3967 := params 30
abbrev ray3967 := rays 30
def bank3967 : Fin 2 → Cell := twoBank p3967 ray3967
theorem signs3967 : ∀ j, Signs p3967 (bank3967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3968 := params 31
abbrev ray3968 := rays 31
def bank3968 : Fin 2 → Cell := twoBank p3968 ray3968
theorem signs3968 : ∀ j, Signs p3968 (bank3968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03937_03968
