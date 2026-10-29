/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02081_02112
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99676725895958,99676544627156,99676363330751,99676182006745,99676000655139,99675819275934,99675637869132,99675456434734,99675274972742,99675093483157,99674911965981,99674730421215,99674548848860,99674367248918,99674185621390,99674003966278,99673822283583,99673640573307,99673458835451,99673277070016,99673095277004,99672913456417,99672731608255,99672549732521,99672367829215,99672185898339,99672003939895,99671821953884,99671639940307,99671457899166,99671275830462,99671093734197,99670911610372]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2080+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2081 := params 0
abbrev ray2081 := rays 0
def bank2081 : Fin 2 → Cell := twoBank p2081 ray2081
theorem signs2081 : ∀ j, Signs p2081 (bank2081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2082 := params 1
abbrev ray2082 := rays 1
def bank2082 : Fin 2 → Cell := twoBank p2082 ray2082
theorem signs2082 : ∀ j, Signs p2082 (bank2082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2083 := params 2
abbrev ray2083 := rays 2
def bank2083 : Fin 2 → Cell := twoBank p2083 ray2083
theorem signs2083 : ∀ j, Signs p2083 (bank2083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2084 := params 3
abbrev ray2084 := rays 3
def bank2084 : Fin 2 → Cell := twoBank p2084 ray2084
theorem signs2084 : ∀ j, Signs p2084 (bank2084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2085 := params 4
abbrev ray2085 := rays 4
def bank2085 : Fin 2 → Cell := twoBank p2085 ray2085
theorem signs2085 : ∀ j, Signs p2085 (bank2085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2086 := params 5
abbrev ray2086 := rays 5
def bank2086 : Fin 2 → Cell := twoBank p2086 ray2086
theorem signs2086 : ∀ j, Signs p2086 (bank2086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2087 := params 6
abbrev ray2087 := rays 6
def bank2087 : Fin 2 → Cell := twoBank p2087 ray2087
theorem signs2087 : ∀ j, Signs p2087 (bank2087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2088 := params 7
abbrev ray2088 := rays 7
def bank2088 : Fin 2 → Cell := twoBank p2088 ray2088
theorem signs2088 : ∀ j, Signs p2088 (bank2088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2089 := params 8
abbrev ray2089 := rays 8
def bank2089 : Fin 2 → Cell := twoBank p2089 ray2089
theorem signs2089 : ∀ j, Signs p2089 (bank2089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2090 := params 9
abbrev ray2090 := rays 9
def bank2090 : Fin 2 → Cell := twoBank p2090 ray2090
theorem signs2090 : ∀ j, Signs p2090 (bank2090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2091 := params 10
abbrev ray2091 := rays 10
def bank2091 : Fin 2 → Cell := twoBank p2091 ray2091
theorem signs2091 : ∀ j, Signs p2091 (bank2091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2092 := params 11
abbrev ray2092 := rays 11
def bank2092 : Fin 2 → Cell := twoBank p2092 ray2092
theorem signs2092 : ∀ j, Signs p2092 (bank2092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2093 := params 12
abbrev ray2093 := rays 12
def bank2093 : Fin 2 → Cell := twoBank p2093 ray2093
theorem signs2093 : ∀ j, Signs p2093 (bank2093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2094 := params 13
abbrev ray2094 := rays 13
def bank2094 : Fin 2 → Cell := twoBank p2094 ray2094
theorem signs2094 : ∀ j, Signs p2094 (bank2094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2095 := params 14
abbrev ray2095 := rays 14
def bank2095 : Fin 2 → Cell := twoBank p2095 ray2095
theorem signs2095 : ∀ j, Signs p2095 (bank2095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2096 := params 15
abbrev ray2096 := rays 15
def bank2096 : Fin 2 → Cell := twoBank p2096 ray2096
theorem signs2096 : ∀ j, Signs p2096 (bank2096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2097 := params 16
abbrev ray2097 := rays 16
def bank2097 : Fin 2 → Cell := twoBank p2097 ray2097
theorem signs2097 : ∀ j, Signs p2097 (bank2097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2098 := params 17
abbrev ray2098 := rays 17
def bank2098 : Fin 2 → Cell := twoBank p2098 ray2098
theorem signs2098 : ∀ j, Signs p2098 (bank2098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2099 := params 18
abbrev ray2099 := rays 18
def bank2099 : Fin 2 → Cell := twoBank p2099 ray2099
theorem signs2099 : ∀ j, Signs p2099 (bank2099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2100 := params 19
abbrev ray2100 := rays 19
def bank2100 : Fin 2 → Cell := twoBank p2100 ray2100
theorem signs2100 : ∀ j, Signs p2100 (bank2100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2101 := params 20
abbrev ray2101 := rays 20
def bank2101 : Fin 2 → Cell := twoBank p2101 ray2101
theorem signs2101 : ∀ j, Signs p2101 (bank2101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2102 := params 21
abbrev ray2102 := rays 21
def bank2102 : Fin 2 → Cell := twoBank p2102 ray2102
theorem signs2102 : ∀ j, Signs p2102 (bank2102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2103 := params 22
abbrev ray2103 := rays 22
def bank2103 : Fin 2 → Cell := twoBank p2103 ray2103
theorem signs2103 : ∀ j, Signs p2103 (bank2103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2104 := params 23
abbrev ray2104 := rays 23
def bank2104 : Fin 2 → Cell := twoBank p2104 ray2104
theorem signs2104 : ∀ j, Signs p2104 (bank2104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2105 := params 24
abbrev ray2105 := rays 24
def bank2105 : Fin 2 → Cell := twoBank p2105 ray2105
theorem signs2105 : ∀ j, Signs p2105 (bank2105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2106 := params 25
abbrev ray2106 := rays 25
def bank2106 : Fin 2 → Cell := twoBank p2106 ray2106
theorem signs2106 : ∀ j, Signs p2106 (bank2106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2107 := params 26
abbrev ray2107 := rays 26
def bank2107 : Fin 2 → Cell := twoBank p2107 ray2107
theorem signs2107 : ∀ j, Signs p2107 (bank2107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2108 := params 27
abbrev ray2108 := rays 27
def bank2108 : Fin 2 → Cell := twoBank p2108 ray2108
theorem signs2108 : ∀ j, Signs p2108 (bank2108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2109 := params 28
abbrev ray2109 := rays 28
def bank2109 : Fin 2 → Cell := twoBank p2109 ray2109
theorem signs2109 : ∀ j, Signs p2109 (bank2109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2110 := params 29
abbrev ray2110 := rays 29
def bank2110 : Fin 2 → Cell := twoBank p2110 ray2110
theorem signs2110 : ∀ j, Signs p2110 (bank2110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2111 := params 30
abbrev ray2111 := rays 30
def bank2111 : Fin 2 → Cell := twoBank p2111 ray2111
theorem signs2111 : ∀ j, Signs p2111 (bank2111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2112 := params 31
abbrev ray2112 := rays 31
def bank2112 : Fin 2 → Cell := twoBank p2112 ray2112
theorem signs2112 : ∀ j, Signs p2112 (bank2112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02081_02112
