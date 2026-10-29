/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06049_06080
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98753412968393,98753131782899,98752850574284,98752569342550,98752288087697,98752006809726,98751725508638,98751444184434,98751162837115,98750881466681,98750600073134,98750318656474,98750037216703,98749755753821,98749474267829,98749192758728,98748911226518,98748629671201,98748348092778,98748066491249,98747784866615,98747503218878,98747221548038,98746939854096,98746658137052,98746376396908,98746094633665,98745812847323,98745531037883,98745249205347,98744967349715,98744685470988,98744403569166]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6048+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6049 := params 0
abbrev ray6049 := rays 0
def bank6049 : Fin 2 → Cell := twoBank p6049 ray6049
theorem signs6049 : ∀ j, Signs p6049 (bank6049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6050 := params 1
abbrev ray6050 := rays 1
def bank6050 : Fin 2 → Cell := twoBank p6050 ray6050
theorem signs6050 : ∀ j, Signs p6050 (bank6050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6051 := params 2
abbrev ray6051 := rays 2
def bank6051 : Fin 2 → Cell := twoBank p6051 ray6051
theorem signs6051 : ∀ j, Signs p6051 (bank6051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6052 := params 3
abbrev ray6052 := rays 3
def bank6052 : Fin 2 → Cell := twoBank p6052 ray6052
theorem signs6052 : ∀ j, Signs p6052 (bank6052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6053 := params 4
abbrev ray6053 := rays 4
def bank6053 : Fin 2 → Cell := twoBank p6053 ray6053
theorem signs6053 : ∀ j, Signs p6053 (bank6053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6054 := params 5
abbrev ray6054 := rays 5
def bank6054 : Fin 2 → Cell := twoBank p6054 ray6054
theorem signs6054 : ∀ j, Signs p6054 (bank6054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6055 := params 6
abbrev ray6055 := rays 6
def bank6055 : Fin 2 → Cell := twoBank p6055 ray6055
theorem signs6055 : ∀ j, Signs p6055 (bank6055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6056 := params 7
abbrev ray6056 := rays 7
def bank6056 : Fin 2 → Cell := twoBank p6056 ray6056
theorem signs6056 : ∀ j, Signs p6056 (bank6056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6057 := params 8
abbrev ray6057 := rays 8
def bank6057 : Fin 2 → Cell := twoBank p6057 ray6057
theorem signs6057 : ∀ j, Signs p6057 (bank6057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6058 := params 9
abbrev ray6058 := rays 9
def bank6058 : Fin 2 → Cell := twoBank p6058 ray6058
theorem signs6058 : ∀ j, Signs p6058 (bank6058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6059 := params 10
abbrev ray6059 := rays 10
def bank6059 : Fin 2 → Cell := twoBank p6059 ray6059
theorem signs6059 : ∀ j, Signs p6059 (bank6059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6060 := params 11
abbrev ray6060 := rays 11
def bank6060 : Fin 2 → Cell := twoBank p6060 ray6060
theorem signs6060 : ∀ j, Signs p6060 (bank6060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6061 := params 12
abbrev ray6061 := rays 12
def bank6061 : Fin 2 → Cell := twoBank p6061 ray6061
theorem signs6061 : ∀ j, Signs p6061 (bank6061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6062 := params 13
abbrev ray6062 := rays 13
def bank6062 : Fin 2 → Cell := twoBank p6062 ray6062
theorem signs6062 : ∀ j, Signs p6062 (bank6062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6063 := params 14
abbrev ray6063 := rays 14
def bank6063 : Fin 2 → Cell := twoBank p6063 ray6063
theorem signs6063 : ∀ j, Signs p6063 (bank6063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6064 := params 15
abbrev ray6064 := rays 15
def bank6064 : Fin 2 → Cell := twoBank p6064 ray6064
theorem signs6064 : ∀ j, Signs p6064 (bank6064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6065 := params 16
abbrev ray6065 := rays 16
def bank6065 : Fin 2 → Cell := twoBank p6065 ray6065
theorem signs6065 : ∀ j, Signs p6065 (bank6065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6066 := params 17
abbrev ray6066 := rays 17
def bank6066 : Fin 2 → Cell := twoBank p6066 ray6066
theorem signs6066 : ∀ j, Signs p6066 (bank6066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6067 := params 18
abbrev ray6067 := rays 18
def bank6067 : Fin 2 → Cell := twoBank p6067 ray6067
theorem signs6067 : ∀ j, Signs p6067 (bank6067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6068 := params 19
abbrev ray6068 := rays 19
def bank6068 : Fin 2 → Cell := twoBank p6068 ray6068
theorem signs6068 : ∀ j, Signs p6068 (bank6068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6069 := params 20
abbrev ray6069 := rays 20
def bank6069 : Fin 2 → Cell := twoBank p6069 ray6069
theorem signs6069 : ∀ j, Signs p6069 (bank6069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6070 := params 21
abbrev ray6070 := rays 21
def bank6070 : Fin 2 → Cell := twoBank p6070 ray6070
theorem signs6070 : ∀ j, Signs p6070 (bank6070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6071 := params 22
abbrev ray6071 := rays 22
def bank6071 : Fin 2 → Cell := twoBank p6071 ray6071
theorem signs6071 : ∀ j, Signs p6071 (bank6071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6072 := params 23
abbrev ray6072 := rays 23
def bank6072 : Fin 2 → Cell := twoBank p6072 ray6072
theorem signs6072 : ∀ j, Signs p6072 (bank6072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6073 := params 24
abbrev ray6073 := rays 24
def bank6073 : Fin 2 → Cell := twoBank p6073 ray6073
theorem signs6073 : ∀ j, Signs p6073 (bank6073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6074 := params 25
abbrev ray6074 := rays 25
def bank6074 : Fin 2 → Cell := twoBank p6074 ray6074
theorem signs6074 : ∀ j, Signs p6074 (bank6074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6075 := params 26
abbrev ray6075 := rays 26
def bank6075 : Fin 2 → Cell := twoBank p6075 ray6075
theorem signs6075 : ∀ j, Signs p6075 (bank6075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6076 := params 27
abbrev ray6076 := rays 27
def bank6076 : Fin 2 → Cell := twoBank p6076 ray6076
theorem signs6076 : ∀ j, Signs p6076 (bank6076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6077 := params 28
abbrev ray6077 := rays 28
def bank6077 : Fin 2 → Cell := twoBank p6077 ray6077
theorem signs6077 : ∀ j, Signs p6077 (bank6077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6078 := params 29
abbrev ray6078 := rays 29
def bank6078 : Fin 2 → Cell := twoBank p6078 ray6078
theorem signs6078 : ∀ j, Signs p6078 (bank6078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6079 := params 30
abbrev ray6079 := rays 30
def bank6079 : Fin 2 → Cell := twoBank p6079 ray6079
theorem signs6079 : ∀ j, Signs p6079 (bank6079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6080 := params 31
abbrev ray6080 := rays 31
def bank6080 : Fin 2 → Cell := twoBank p6080 ray6080
theorem signs6080 : ∀ j, Signs p6080 (bank6080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06049_06080
