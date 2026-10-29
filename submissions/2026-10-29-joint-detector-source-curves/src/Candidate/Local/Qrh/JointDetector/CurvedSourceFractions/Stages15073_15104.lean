/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15073_15104
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95365356363582,95364897853596,95364439327552,95363980785451,95363522227292,95363063653075,95362605062801,95362146456469,95361687834080,95361229195633,95360770541129,95360311870568,95359853183950,95359394481275,95358935762544,95358477027756,95358018276912,95357559510011,95357100727054,95356641928041,95356183112971,95355724281845,95355265434664,95354806571427,95354347692134,95353888796786,95353429885382,95352970957923,95352512014408,95352053054838,95351594079213,95351135087533,95350676079798]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15072+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15073 := params 0
abbrev ray15073 := rays 0
def bank15073 : Fin 1 → Cell := oneBank p15073 ray15073
theorem signs15073 : ∀ j, Signs p15073 (bank15073 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15074 := params 1
abbrev ray15074 := rays 1
def bank15074 : Fin 1 → Cell := oneBank p15074 ray15074
theorem signs15074 : ∀ j, Signs p15074 (bank15074 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15075 := params 2
abbrev ray15075 := rays 2
def bank15075 : Fin 1 → Cell := oneBank p15075 ray15075
theorem signs15075 : ∀ j, Signs p15075 (bank15075 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15076 := params 3
abbrev ray15076 := rays 3
def bank15076 : Fin 1 → Cell := oneBank p15076 ray15076
theorem signs15076 : ∀ j, Signs p15076 (bank15076 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15077 := params 4
abbrev ray15077 := rays 4
def bank15077 : Fin 1 → Cell := oneBank p15077 ray15077
theorem signs15077 : ∀ j, Signs p15077 (bank15077 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15078 := params 5
abbrev ray15078 := rays 5
def bank15078 : Fin 1 → Cell := oneBank p15078 ray15078
theorem signs15078 : ∀ j, Signs p15078 (bank15078 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15079 := params 6
abbrev ray15079 := rays 6
def bank15079 : Fin 1 → Cell := oneBank p15079 ray15079
theorem signs15079 : ∀ j, Signs p15079 (bank15079 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15080 := params 7
abbrev ray15080 := rays 7
def bank15080 : Fin 1 → Cell := oneBank p15080 ray15080
theorem signs15080 : ∀ j, Signs p15080 (bank15080 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15081 := params 8
abbrev ray15081 := rays 8
def bank15081 : Fin 1 → Cell := oneBank p15081 ray15081
theorem signs15081 : ∀ j, Signs p15081 (bank15081 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15082 := params 9
abbrev ray15082 := rays 9
def bank15082 : Fin 1 → Cell := oneBank p15082 ray15082
theorem signs15082 : ∀ j, Signs p15082 (bank15082 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15083 := params 10
abbrev ray15083 := rays 10
def bank15083 : Fin 1 → Cell := oneBank p15083 ray15083
theorem signs15083 : ∀ j, Signs p15083 (bank15083 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15084 := params 11
abbrev ray15084 := rays 11
def bank15084 : Fin 1 → Cell := oneBank p15084 ray15084
theorem signs15084 : ∀ j, Signs p15084 (bank15084 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15085 := params 12
abbrev ray15085 := rays 12
def bank15085 : Fin 1 → Cell := oneBank p15085 ray15085
theorem signs15085 : ∀ j, Signs p15085 (bank15085 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15086 := params 13
abbrev ray15086 := rays 13
def bank15086 : Fin 1 → Cell := oneBank p15086 ray15086
theorem signs15086 : ∀ j, Signs p15086 (bank15086 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15087 := params 14
abbrev ray15087 := rays 14
def bank15087 : Fin 1 → Cell := oneBank p15087 ray15087
theorem signs15087 : ∀ j, Signs p15087 (bank15087 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15088 := params 15
abbrev ray15088 := rays 15
def bank15088 : Fin 1 → Cell := oneBank p15088 ray15088
theorem signs15088 : ∀ j, Signs p15088 (bank15088 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15089 := params 16
abbrev ray15089 := rays 16
def bank15089 : Fin 1 → Cell := oneBank p15089 ray15089
theorem signs15089 : ∀ j, Signs p15089 (bank15089 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15090 := params 17
abbrev ray15090 := rays 17
def bank15090 : Fin 1 → Cell := oneBank p15090 ray15090
theorem signs15090 : ∀ j, Signs p15090 (bank15090 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15091 := params 18
abbrev ray15091 := rays 18
def bank15091 : Fin 1 → Cell := oneBank p15091 ray15091
theorem signs15091 : ∀ j, Signs p15091 (bank15091 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15092 := params 19
abbrev ray15092 := rays 19
def bank15092 : Fin 1 → Cell := oneBank p15092 ray15092
theorem signs15092 : ∀ j, Signs p15092 (bank15092 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15093 := params 20
abbrev ray15093 := rays 20
def bank15093 : Fin 1 → Cell := oneBank p15093 ray15093
theorem signs15093 : ∀ j, Signs p15093 (bank15093 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15094 := params 21
abbrev ray15094 := rays 21
def bank15094 : Fin 1 → Cell := oneBank p15094 ray15094
theorem signs15094 : ∀ j, Signs p15094 (bank15094 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15095 := params 22
abbrev ray15095 := rays 22
def bank15095 : Fin 1 → Cell := oneBank p15095 ray15095
theorem signs15095 : ∀ j, Signs p15095 (bank15095 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15096 := params 23
abbrev ray15096 := rays 23
def bank15096 : Fin 1 → Cell := oneBank p15096 ray15096
theorem signs15096 : ∀ j, Signs p15096 (bank15096 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15097 := params 24
abbrev ray15097 := rays 24
def bank15097 : Fin 1 → Cell := oneBank p15097 ray15097
theorem signs15097 : ∀ j, Signs p15097 (bank15097 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15098 := params 25
abbrev ray15098 := rays 25
def bank15098 : Fin 1 → Cell := oneBank p15098 ray15098
theorem signs15098 : ∀ j, Signs p15098 (bank15098 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15099 := params 26
abbrev ray15099 := rays 26
def bank15099 : Fin 1 → Cell := oneBank p15099 ray15099
theorem signs15099 : ∀ j, Signs p15099 (bank15099 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15100 := params 27
abbrev ray15100 := rays 27
def bank15100 : Fin 1 → Cell := oneBank p15100 ray15100
theorem signs15100 : ∀ j, Signs p15100 (bank15100 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15101 := params 28
abbrev ray15101 := rays 28
def bank15101 : Fin 1 → Cell := oneBank p15101 ray15101
theorem signs15101 : ∀ j, Signs p15101 (bank15101 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15102 := params 29
abbrev ray15102 := rays 29
def bank15102 : Fin 1 → Cell := oneBank p15102 ray15102
theorem signs15102 : ∀ j, Signs p15102 (bank15102 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15103 := params 30
abbrev ray15103 := rays 30
def bank15103 : Fin 1 → Cell := oneBank p15103 ray15103
theorem signs15103 : ∀ j, Signs p15103 (bank15103 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15104 := params 31
abbrev ray15104 := rays 31
def bank15104 : Fin 1 → Cell := oneBank p15104 ray15104
theorem signs15104 : ∀ j, Signs p15104 (bank15104 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15073_15104
