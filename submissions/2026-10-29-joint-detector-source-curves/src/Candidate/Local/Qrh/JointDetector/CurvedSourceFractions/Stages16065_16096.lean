/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16065_16096
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94902635498939,94902161099195,94901686683461,94901212251737,94900737804024,94900263340321,94899788860628,94899314364945,94898839853272,94898365325609,94897890781957,94897416222315,94896941646683,94896467055062,94895992447451,94895517823851,94895043184261,94894568528682,94894093857113,94893619169555,94893144466007,94892669746470,94892195010944,94891720259428,94891245491923,94890770708429,94890295908946,94889821093473,94889346262011,94888871414560,94888396551120,94887921671691,94887446776273]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16064+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16065 := params 0
abbrev ray16065 := rays 0
def bank16065 : Fin 1 → Cell := oneBank p16065 ray16065
theorem signs16065 : ∀ j, Signs p16065 (bank16065 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16066 := params 1
abbrev ray16066 := rays 1
def bank16066 : Fin 1 → Cell := oneBank p16066 ray16066
theorem signs16066 : ∀ j, Signs p16066 (bank16066 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16067 := params 2
abbrev ray16067 := rays 2
def bank16067 : Fin 1 → Cell := oneBank p16067 ray16067
theorem signs16067 : ∀ j, Signs p16067 (bank16067 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16068 := params 3
abbrev ray16068 := rays 3
def bank16068 : Fin 1 → Cell := oneBank p16068 ray16068
theorem signs16068 : ∀ j, Signs p16068 (bank16068 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16069 := params 4
abbrev ray16069 := rays 4
def bank16069 : Fin 1 → Cell := oneBank p16069 ray16069
theorem signs16069 : ∀ j, Signs p16069 (bank16069 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16070 := params 5
abbrev ray16070 := rays 5
def bank16070 : Fin 1 → Cell := oneBank p16070 ray16070
theorem signs16070 : ∀ j, Signs p16070 (bank16070 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16071 := params 6
abbrev ray16071 := rays 6
def bank16071 : Fin 1 → Cell := oneBank p16071 ray16071
theorem signs16071 : ∀ j, Signs p16071 (bank16071 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16072 := params 7
abbrev ray16072 := rays 7
def bank16072 : Fin 1 → Cell := oneBank p16072 ray16072
theorem signs16072 : ∀ j, Signs p16072 (bank16072 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16073 := params 8
abbrev ray16073 := rays 8
def bank16073 : Fin 1 → Cell := oneBank p16073 ray16073
theorem signs16073 : ∀ j, Signs p16073 (bank16073 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16074 := params 9
abbrev ray16074 := rays 9
def bank16074 : Fin 1 → Cell := oneBank p16074 ray16074
theorem signs16074 : ∀ j, Signs p16074 (bank16074 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16075 := params 10
abbrev ray16075 := rays 10
def bank16075 : Fin 1 → Cell := oneBank p16075 ray16075
theorem signs16075 : ∀ j, Signs p16075 (bank16075 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16076 := params 11
abbrev ray16076 := rays 11
def bank16076 : Fin 1 → Cell := oneBank p16076 ray16076
theorem signs16076 : ∀ j, Signs p16076 (bank16076 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16077 := params 12
abbrev ray16077 := rays 12
def bank16077 : Fin 1 → Cell := oneBank p16077 ray16077
theorem signs16077 : ∀ j, Signs p16077 (bank16077 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16078 := params 13
abbrev ray16078 := rays 13
def bank16078 : Fin 1 → Cell := oneBank p16078 ray16078
theorem signs16078 : ∀ j, Signs p16078 (bank16078 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16079 := params 14
abbrev ray16079 := rays 14
def bank16079 : Fin 1 → Cell := oneBank p16079 ray16079
theorem signs16079 : ∀ j, Signs p16079 (bank16079 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16080 := params 15
abbrev ray16080 := rays 15
def bank16080 : Fin 1 → Cell := oneBank p16080 ray16080
theorem signs16080 : ∀ j, Signs p16080 (bank16080 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16081 := params 16
abbrev ray16081 := rays 16
def bank16081 : Fin 1 → Cell := oneBank p16081 ray16081
theorem signs16081 : ∀ j, Signs p16081 (bank16081 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16082 := params 17
abbrev ray16082 := rays 17
def bank16082 : Fin 1 → Cell := oneBank p16082 ray16082
theorem signs16082 : ∀ j, Signs p16082 (bank16082 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16083 := params 18
abbrev ray16083 := rays 18
def bank16083 : Fin 1 → Cell := oneBank p16083 ray16083
theorem signs16083 : ∀ j, Signs p16083 (bank16083 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16084 := params 19
abbrev ray16084 := rays 19
def bank16084 : Fin 1 → Cell := oneBank p16084 ray16084
theorem signs16084 : ∀ j, Signs p16084 (bank16084 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16085 := params 20
abbrev ray16085 := rays 20
def bank16085 : Fin 1 → Cell := oneBank p16085 ray16085
theorem signs16085 : ∀ j, Signs p16085 (bank16085 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16086 := params 21
abbrev ray16086 := rays 21
def bank16086 : Fin 1 → Cell := oneBank p16086 ray16086
theorem signs16086 : ∀ j, Signs p16086 (bank16086 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16087 := params 22
abbrev ray16087 := rays 22
def bank16087 : Fin 1 → Cell := oneBank p16087 ray16087
theorem signs16087 : ∀ j, Signs p16087 (bank16087 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16088 := params 23
abbrev ray16088 := rays 23
def bank16088 : Fin 1 → Cell := oneBank p16088 ray16088
theorem signs16088 : ∀ j, Signs p16088 (bank16088 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16089 := params 24
abbrev ray16089 := rays 24
def bank16089 : Fin 1 → Cell := oneBank p16089 ray16089
theorem signs16089 : ∀ j, Signs p16089 (bank16089 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16090 := params 25
abbrev ray16090 := rays 25
def bank16090 : Fin 1 → Cell := oneBank p16090 ray16090
theorem signs16090 : ∀ j, Signs p16090 (bank16090 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16091 := params 26
abbrev ray16091 := rays 26
def bank16091 : Fin 1 → Cell := oneBank p16091 ray16091
theorem signs16091 : ∀ j, Signs p16091 (bank16091 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16092 := params 27
abbrev ray16092 := rays 27
def bank16092 : Fin 1 → Cell := oneBank p16092 ray16092
theorem signs16092 : ∀ j, Signs p16092 (bank16092 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16093 := params 28
abbrev ray16093 := rays 28
def bank16093 : Fin 1 → Cell := oneBank p16093 ray16093
theorem signs16093 : ∀ j, Signs p16093 (bank16093 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16094 := params 29
abbrev ray16094 := rays 29
def bank16094 : Fin 1 → Cell := oneBank p16094 ray16094
theorem signs16094 : ∀ j, Signs p16094 (bank16094 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16095 := params 30
abbrev ray16095 := rays 30
def bank16095 : Fin 1 → Cell := oneBank p16095 ray16095
theorem signs16095 : ∀ j, Signs p16095 (bank16095 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16096 := params 31
abbrev ray16096 := rays 31
def bank16096 : Fin 1 → Cell := oneBank p16096 ray16096
theorem signs16096 : ∀ j, Signs p16096 (bank16096 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16065_16096
