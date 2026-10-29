/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09089_09120
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97795582609836,97795234759835,97794886888964,97794538997224,97794191084615,97793843151138,97793495196794,97793147221583,97792799225506,97792451208563,97792103170756,97791755112084,97791407032549,97791058932150,97790710810889,97790362668766,97790014505782,97789666321937,97789318117232,97788969891668,97788621645245,97788273377964,97787925089826,97787576780831,97787228450979,97786880100272,97786531728710,97786183336293,97785834923022,97785486488898,97785138033921,97784789558092,97784441061412]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9088+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9089 := params 0
abbrev ray9089 := rays 0
def bank9089 : Fin 2 → Cell := twoBank p9089 ray9089
theorem signs9089 : ∀ j, Signs p9089 (bank9089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9090 := params 1
abbrev ray9090 := rays 1
def bank9090 : Fin 2 → Cell := twoBank p9090 ray9090
theorem signs9090 : ∀ j, Signs p9090 (bank9090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9091 := params 2
abbrev ray9091 := rays 2
def bank9091 : Fin 2 → Cell := twoBank p9091 ray9091
theorem signs9091 : ∀ j, Signs p9091 (bank9091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9092 := params 3
abbrev ray9092 := rays 3
def bank9092 : Fin 2 → Cell := twoBank p9092 ray9092
theorem signs9092 : ∀ j, Signs p9092 (bank9092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9093 := params 4
abbrev ray9093 := rays 4
def bank9093 : Fin 2 → Cell := twoBank p9093 ray9093
theorem signs9093 : ∀ j, Signs p9093 (bank9093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9094 := params 5
abbrev ray9094 := rays 5
def bank9094 : Fin 2 → Cell := twoBank p9094 ray9094
theorem signs9094 : ∀ j, Signs p9094 (bank9094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9095 := params 6
abbrev ray9095 := rays 6
def bank9095 : Fin 2 → Cell := twoBank p9095 ray9095
theorem signs9095 : ∀ j, Signs p9095 (bank9095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9096 := params 7
abbrev ray9096 := rays 7
def bank9096 : Fin 2 → Cell := twoBank p9096 ray9096
theorem signs9096 : ∀ j, Signs p9096 (bank9096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9097 := params 8
abbrev ray9097 := rays 8
def bank9097 : Fin 2 → Cell := twoBank p9097 ray9097
theorem signs9097 : ∀ j, Signs p9097 (bank9097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9098 := params 9
abbrev ray9098 := rays 9
def bank9098 : Fin 2 → Cell := twoBank p9098 ray9098
theorem signs9098 : ∀ j, Signs p9098 (bank9098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9099 := params 10
abbrev ray9099 := rays 10
def bank9099 : Fin 2 → Cell := twoBank p9099 ray9099
theorem signs9099 : ∀ j, Signs p9099 (bank9099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9100 := params 11
abbrev ray9100 := rays 11
def bank9100 : Fin 2 → Cell := twoBank p9100 ray9100
theorem signs9100 : ∀ j, Signs p9100 (bank9100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9101 := params 12
abbrev ray9101 := rays 12
def bank9101 : Fin 2 → Cell := twoBank p9101 ray9101
theorem signs9101 : ∀ j, Signs p9101 (bank9101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9102 := params 13
abbrev ray9102 := rays 13
def bank9102 : Fin 2 → Cell := twoBank p9102 ray9102
theorem signs9102 : ∀ j, Signs p9102 (bank9102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9103 := params 14
abbrev ray9103 := rays 14
def bank9103 : Fin 2 → Cell := twoBank p9103 ray9103
theorem signs9103 : ∀ j, Signs p9103 (bank9103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9104 := params 15
abbrev ray9104 := rays 15
def bank9104 : Fin 2 → Cell := twoBank p9104 ray9104
theorem signs9104 : ∀ j, Signs p9104 (bank9104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9105 := params 16
abbrev ray9105 := rays 16
def bank9105 : Fin 2 → Cell := twoBank p9105 ray9105
theorem signs9105 : ∀ j, Signs p9105 (bank9105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9106 := params 17
abbrev ray9106 := rays 17
def bank9106 : Fin 2 → Cell := twoBank p9106 ray9106
theorem signs9106 : ∀ j, Signs p9106 (bank9106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9107 := params 18
abbrev ray9107 := rays 18
def bank9107 : Fin 2 → Cell := twoBank p9107 ray9107
theorem signs9107 : ∀ j, Signs p9107 (bank9107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9108 := params 19
abbrev ray9108 := rays 19
def bank9108 : Fin 2 → Cell := twoBank p9108 ray9108
theorem signs9108 : ∀ j, Signs p9108 (bank9108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9109 := params 20
abbrev ray9109 := rays 20
def bank9109 : Fin 2 → Cell := twoBank p9109 ray9109
theorem signs9109 : ∀ j, Signs p9109 (bank9109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9110 := params 21
abbrev ray9110 := rays 21
def bank9110 : Fin 2 → Cell := twoBank p9110 ray9110
theorem signs9110 : ∀ j, Signs p9110 (bank9110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9111 := params 22
abbrev ray9111 := rays 22
def bank9111 : Fin 2 → Cell := twoBank p9111 ray9111
theorem signs9111 : ∀ j, Signs p9111 (bank9111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9112 := params 23
abbrev ray9112 := rays 23
def bank9112 : Fin 2 → Cell := twoBank p9112 ray9112
theorem signs9112 : ∀ j, Signs p9112 (bank9112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9113 := params 24
abbrev ray9113 := rays 24
def bank9113 : Fin 2 → Cell := twoBank p9113 ray9113
theorem signs9113 : ∀ j, Signs p9113 (bank9113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9114 := params 25
abbrev ray9114 := rays 25
def bank9114 : Fin 2 → Cell := twoBank p9114 ray9114
theorem signs9114 : ∀ j, Signs p9114 (bank9114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9115 := params 26
abbrev ray9115 := rays 26
def bank9115 : Fin 2 → Cell := twoBank p9115 ray9115
theorem signs9115 : ∀ j, Signs p9115 (bank9115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9116 := params 27
abbrev ray9116 := rays 27
def bank9116 : Fin 2 → Cell := twoBank p9116 ray9116
theorem signs9116 : ∀ j, Signs p9116 (bank9116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9117 := params 28
abbrev ray9117 := rays 28
def bank9117 : Fin 2 → Cell := twoBank p9117 ray9117
theorem signs9117 : ∀ j, Signs p9117 (bank9117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9118 := params 29
abbrev ray9118 := rays 29
def bank9118 : Fin 2 → Cell := twoBank p9118 ray9118
theorem signs9118 : ∀ j, Signs p9118 (bank9118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9119 := params 30
abbrev ray9119 := rays 30
def bank9119 : Fin 2 → Cell := twoBank p9119 ray9119
theorem signs9119 : ∀ j, Signs p9119 (bank9119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9120 := params 31
abbrev ray9120 := rays 31
def bank9120 : Fin 2 → Cell := twoBank p9120 ray9120
theorem signs9120 : ∀ j, Signs p9120 (bank9120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09089_09120
