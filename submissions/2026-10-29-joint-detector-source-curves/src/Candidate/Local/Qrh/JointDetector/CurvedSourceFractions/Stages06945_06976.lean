/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06945_06976
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98492302778657,98492001217888,98491699634746,98491398029233,98491096401349,98490794751095,98490493078472,98490191383481,98489889666122,98489587926396,98489286164305,98488984379848,98488682573027,98488380743842,98488078892295,98487777018386,98487475122115,98487173203484,98486871262493,98486569299144,98486267313437,98485965305372,98485663274951,98485361222174,98485059147042,98484757049556,98484454929717,98484152787525,98483850622982,98483548436088,98483246226844,98482943995250,98482641741308]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6944+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6945 := params 0
abbrev ray6945 := rays 0
def bank6945 : Fin 2 → Cell := twoBank p6945 ray6945
theorem signs6945 : ∀ j, Signs p6945 (bank6945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6946 := params 1
abbrev ray6946 := rays 1
def bank6946 : Fin 2 → Cell := twoBank p6946 ray6946
theorem signs6946 : ∀ j, Signs p6946 (bank6946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6947 := params 2
abbrev ray6947 := rays 2
def bank6947 : Fin 2 → Cell := twoBank p6947 ray6947
theorem signs6947 : ∀ j, Signs p6947 (bank6947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6948 := params 3
abbrev ray6948 := rays 3
def bank6948 : Fin 2 → Cell := twoBank p6948 ray6948
theorem signs6948 : ∀ j, Signs p6948 (bank6948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6949 := params 4
abbrev ray6949 := rays 4
def bank6949 : Fin 2 → Cell := twoBank p6949 ray6949
theorem signs6949 : ∀ j, Signs p6949 (bank6949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6950 := params 5
abbrev ray6950 := rays 5
def bank6950 : Fin 2 → Cell := twoBank p6950 ray6950
theorem signs6950 : ∀ j, Signs p6950 (bank6950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6951 := params 6
abbrev ray6951 := rays 6
def bank6951 : Fin 2 → Cell := twoBank p6951 ray6951
theorem signs6951 : ∀ j, Signs p6951 (bank6951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6952 := params 7
abbrev ray6952 := rays 7
def bank6952 : Fin 2 → Cell := twoBank p6952 ray6952
theorem signs6952 : ∀ j, Signs p6952 (bank6952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6953 := params 8
abbrev ray6953 := rays 8
def bank6953 : Fin 2 → Cell := twoBank p6953 ray6953
theorem signs6953 : ∀ j, Signs p6953 (bank6953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6954 := params 9
abbrev ray6954 := rays 9
def bank6954 : Fin 2 → Cell := twoBank p6954 ray6954
theorem signs6954 : ∀ j, Signs p6954 (bank6954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6955 := params 10
abbrev ray6955 := rays 10
def bank6955 : Fin 2 → Cell := twoBank p6955 ray6955
theorem signs6955 : ∀ j, Signs p6955 (bank6955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6956 := params 11
abbrev ray6956 := rays 11
def bank6956 : Fin 2 → Cell := twoBank p6956 ray6956
theorem signs6956 : ∀ j, Signs p6956 (bank6956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6957 := params 12
abbrev ray6957 := rays 12
def bank6957 : Fin 2 → Cell := twoBank p6957 ray6957
theorem signs6957 : ∀ j, Signs p6957 (bank6957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6958 := params 13
abbrev ray6958 := rays 13
def bank6958 : Fin 2 → Cell := twoBank p6958 ray6958
theorem signs6958 : ∀ j, Signs p6958 (bank6958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6959 := params 14
abbrev ray6959 := rays 14
def bank6959 : Fin 2 → Cell := twoBank p6959 ray6959
theorem signs6959 : ∀ j, Signs p6959 (bank6959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6960 := params 15
abbrev ray6960 := rays 15
def bank6960 : Fin 2 → Cell := twoBank p6960 ray6960
theorem signs6960 : ∀ j, Signs p6960 (bank6960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6961 := params 16
abbrev ray6961 := rays 16
def bank6961 : Fin 2 → Cell := twoBank p6961 ray6961
theorem signs6961 : ∀ j, Signs p6961 (bank6961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6962 := params 17
abbrev ray6962 := rays 17
def bank6962 : Fin 2 → Cell := twoBank p6962 ray6962
theorem signs6962 : ∀ j, Signs p6962 (bank6962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6963 := params 18
abbrev ray6963 := rays 18
def bank6963 : Fin 2 → Cell := twoBank p6963 ray6963
theorem signs6963 : ∀ j, Signs p6963 (bank6963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6964 := params 19
abbrev ray6964 := rays 19
def bank6964 : Fin 2 → Cell := twoBank p6964 ray6964
theorem signs6964 : ∀ j, Signs p6964 (bank6964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6965 := params 20
abbrev ray6965 := rays 20
def bank6965 : Fin 2 → Cell := twoBank p6965 ray6965
theorem signs6965 : ∀ j, Signs p6965 (bank6965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6966 := params 21
abbrev ray6966 := rays 21
def bank6966 : Fin 2 → Cell := twoBank p6966 ray6966
theorem signs6966 : ∀ j, Signs p6966 (bank6966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6967 := params 22
abbrev ray6967 := rays 22
def bank6967 : Fin 2 → Cell := twoBank p6967 ray6967
theorem signs6967 : ∀ j, Signs p6967 (bank6967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6968 := params 23
abbrev ray6968 := rays 23
def bank6968 : Fin 2 → Cell := twoBank p6968 ray6968
theorem signs6968 : ∀ j, Signs p6968 (bank6968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6969 := params 24
abbrev ray6969 := rays 24
def bank6969 : Fin 2 → Cell := twoBank p6969 ray6969
theorem signs6969 : ∀ j, Signs p6969 (bank6969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6970 := params 25
abbrev ray6970 := rays 25
def bank6970 : Fin 2 → Cell := twoBank p6970 ray6970
theorem signs6970 : ∀ j, Signs p6970 (bank6970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6971 := params 26
abbrev ray6971 := rays 26
def bank6971 : Fin 2 → Cell := twoBank p6971 ray6971
theorem signs6971 : ∀ j, Signs p6971 (bank6971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6972 := params 27
abbrev ray6972 := rays 27
def bank6972 : Fin 2 → Cell := twoBank p6972 ray6972
theorem signs6972 : ∀ j, Signs p6972 (bank6972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6973 := params 28
abbrev ray6973 := rays 28
def bank6973 : Fin 2 → Cell := twoBank p6973 ray6973
theorem signs6973 : ∀ j, Signs p6973 (bank6973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6974 := params 29
abbrev ray6974 := rays 29
def bank6974 : Fin 2 → Cell := twoBank p6974 ray6974
theorem signs6974 : ∀ j, Signs p6974 (bank6974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6975 := params 30
abbrev ray6975 := rays 30
def bank6975 : Fin 2 → Cell := twoBank p6975 ray6975
theorem signs6975 : ∀ j, Signs p6975 (bank6975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6976 := params 31
abbrev ray6976 := rays 31
def bank6976 : Fin 2 → Cell := twoBank p6976 ray6976
theorem signs6976 : ∀ j, Signs p6976 (bank6976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06945_06976
