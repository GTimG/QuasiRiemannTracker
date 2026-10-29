/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06081_06112
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98744403569166,98744121644251,98743839696244,98743557725145,98743275730956,98742993713677,98742711673309,98742429609853,98742147523310,98741865413680,98741583280965,98741301125165,98741018946282,98740736744316,98740454519268,98740172271139,98739889999930,98739607705642,98739325388275,98739043047831,98738760684310,98738478297713,98738195888041,98737913455295,98737630999476,98737348520585,98737066018622,98736783493589,98736500945486,98736218374314,98735935780075,98735653162768,98735370522395]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6080+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6081 := params 0
abbrev ray6081 := rays 0
def bank6081 : Fin 2 → Cell := twoBank p6081 ray6081
theorem signs6081 : ∀ j, Signs p6081 (bank6081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6082 := params 1
abbrev ray6082 := rays 1
def bank6082 : Fin 2 → Cell := twoBank p6082 ray6082
theorem signs6082 : ∀ j, Signs p6082 (bank6082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6083 := params 2
abbrev ray6083 := rays 2
def bank6083 : Fin 2 → Cell := twoBank p6083 ray6083
theorem signs6083 : ∀ j, Signs p6083 (bank6083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6084 := params 3
abbrev ray6084 := rays 3
def bank6084 : Fin 2 → Cell := twoBank p6084 ray6084
theorem signs6084 : ∀ j, Signs p6084 (bank6084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6085 := params 4
abbrev ray6085 := rays 4
def bank6085 : Fin 2 → Cell := twoBank p6085 ray6085
theorem signs6085 : ∀ j, Signs p6085 (bank6085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6086 := params 5
abbrev ray6086 := rays 5
def bank6086 : Fin 2 → Cell := twoBank p6086 ray6086
theorem signs6086 : ∀ j, Signs p6086 (bank6086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6087 := params 6
abbrev ray6087 := rays 6
def bank6087 : Fin 2 → Cell := twoBank p6087 ray6087
theorem signs6087 : ∀ j, Signs p6087 (bank6087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6088 := params 7
abbrev ray6088 := rays 7
def bank6088 : Fin 2 → Cell := twoBank p6088 ray6088
theorem signs6088 : ∀ j, Signs p6088 (bank6088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6089 := params 8
abbrev ray6089 := rays 8
def bank6089 : Fin 2 → Cell := twoBank p6089 ray6089
theorem signs6089 : ∀ j, Signs p6089 (bank6089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6090 := params 9
abbrev ray6090 := rays 9
def bank6090 : Fin 2 → Cell := twoBank p6090 ray6090
theorem signs6090 : ∀ j, Signs p6090 (bank6090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6091 := params 10
abbrev ray6091 := rays 10
def bank6091 : Fin 2 → Cell := twoBank p6091 ray6091
theorem signs6091 : ∀ j, Signs p6091 (bank6091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6092 := params 11
abbrev ray6092 := rays 11
def bank6092 : Fin 2 → Cell := twoBank p6092 ray6092
theorem signs6092 : ∀ j, Signs p6092 (bank6092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6093 := params 12
abbrev ray6093 := rays 12
def bank6093 : Fin 2 → Cell := twoBank p6093 ray6093
theorem signs6093 : ∀ j, Signs p6093 (bank6093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6094 := params 13
abbrev ray6094 := rays 13
def bank6094 : Fin 2 → Cell := twoBank p6094 ray6094
theorem signs6094 : ∀ j, Signs p6094 (bank6094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6095 := params 14
abbrev ray6095 := rays 14
def bank6095 : Fin 2 → Cell := twoBank p6095 ray6095
theorem signs6095 : ∀ j, Signs p6095 (bank6095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6096 := params 15
abbrev ray6096 := rays 15
def bank6096 : Fin 2 → Cell := twoBank p6096 ray6096
theorem signs6096 : ∀ j, Signs p6096 (bank6096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6097 := params 16
abbrev ray6097 := rays 16
def bank6097 : Fin 2 → Cell := twoBank p6097 ray6097
theorem signs6097 : ∀ j, Signs p6097 (bank6097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6098 := params 17
abbrev ray6098 := rays 17
def bank6098 : Fin 2 → Cell := twoBank p6098 ray6098
theorem signs6098 : ∀ j, Signs p6098 (bank6098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6099 := params 18
abbrev ray6099 := rays 18
def bank6099 : Fin 2 → Cell := twoBank p6099 ray6099
theorem signs6099 : ∀ j, Signs p6099 (bank6099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6100 := params 19
abbrev ray6100 := rays 19
def bank6100 : Fin 2 → Cell := twoBank p6100 ray6100
theorem signs6100 : ∀ j, Signs p6100 (bank6100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6101 := params 20
abbrev ray6101 := rays 20
def bank6101 : Fin 2 → Cell := twoBank p6101 ray6101
theorem signs6101 : ∀ j, Signs p6101 (bank6101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6102 := params 21
abbrev ray6102 := rays 21
def bank6102 : Fin 2 → Cell := twoBank p6102 ray6102
theorem signs6102 : ∀ j, Signs p6102 (bank6102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6103 := params 22
abbrev ray6103 := rays 22
def bank6103 : Fin 2 → Cell := twoBank p6103 ray6103
theorem signs6103 : ∀ j, Signs p6103 (bank6103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6104 := params 23
abbrev ray6104 := rays 23
def bank6104 : Fin 2 → Cell := twoBank p6104 ray6104
theorem signs6104 : ∀ j, Signs p6104 (bank6104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6105 := params 24
abbrev ray6105 := rays 24
def bank6105 : Fin 2 → Cell := twoBank p6105 ray6105
theorem signs6105 : ∀ j, Signs p6105 (bank6105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6106 := params 25
abbrev ray6106 := rays 25
def bank6106 : Fin 2 → Cell := twoBank p6106 ray6106
theorem signs6106 : ∀ j, Signs p6106 (bank6106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6107 := params 26
abbrev ray6107 := rays 26
def bank6107 : Fin 2 → Cell := twoBank p6107 ray6107
theorem signs6107 : ∀ j, Signs p6107 (bank6107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6108 := params 27
abbrev ray6108 := rays 27
def bank6108 : Fin 2 → Cell := twoBank p6108 ray6108
theorem signs6108 : ∀ j, Signs p6108 (bank6108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6109 := params 28
abbrev ray6109 := rays 28
def bank6109 : Fin 2 → Cell := twoBank p6109 ray6109
theorem signs6109 : ∀ j, Signs p6109 (bank6109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6110 := params 29
abbrev ray6110 := rays 29
def bank6110 : Fin 2 → Cell := twoBank p6110 ray6110
theorem signs6110 : ∀ j, Signs p6110 (bank6110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6111 := params 30
abbrev ray6111 := rays 30
def bank6111 : Fin 2 → Cell := twoBank p6111 ray6111
theorem signs6111 : ∀ j, Signs p6111 (bank6111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6112 := params 31
abbrev ray6112 := rays 31
def bank6112 : Fin 2 → Cell := twoBank p6112 ray6112
theorem signs6112 : ∀ j, Signs p6112 (bank6112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06081_06112
