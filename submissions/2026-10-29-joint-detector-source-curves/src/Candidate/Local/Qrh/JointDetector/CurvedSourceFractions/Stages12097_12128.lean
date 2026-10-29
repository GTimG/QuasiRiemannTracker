/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12097_12128
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96657426486719,96657018342822,96656610179611,96656201997087,96655793795250,96655385574100,96654977333638,96654569073864,96654160794779,96653752496383,96653344178676,96652935841659,96652527485333,96652119109698,96651710714754,96651302300502,96650893866942,96650485414074,96650076941899,96649668450417,96649259939629,96648851409536,96648442860137,96648034291433,96647625703425,96647217096113,96646808469497,96646399823578,96645991158356,96645582473832,96645173770006,96644765046878,96644356304449]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12096+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12097 := params 0
abbrev ray12097 := rays 0
def bank12097 : Fin 2 → Cell := twoBank p12097 ray12097
theorem signs12097 : ∀ j, Signs p12097 (bank12097 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12098 := params 1
abbrev ray12098 := rays 1
def bank12098 : Fin 2 → Cell := twoBank p12098 ray12098
theorem signs12098 : ∀ j, Signs p12098 (bank12098 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12099 := params 2
abbrev ray12099 := rays 2
def bank12099 : Fin 2 → Cell := twoBank p12099 ray12099
theorem signs12099 : ∀ j, Signs p12099 (bank12099 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12100 := params 3
abbrev ray12100 := rays 3
def bank12100 : Fin 2 → Cell := twoBank p12100 ray12100
theorem signs12100 : ∀ j, Signs p12100 (bank12100 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12101 := params 4
abbrev ray12101 := rays 4
def bank12101 : Fin 2 → Cell := twoBank p12101 ray12101
theorem signs12101 : ∀ j, Signs p12101 (bank12101 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12102 := params 5
abbrev ray12102 := rays 5
def bank12102 : Fin 2 → Cell := twoBank p12102 ray12102
theorem signs12102 : ∀ j, Signs p12102 (bank12102 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12103 := params 6
abbrev ray12103 := rays 6
def bank12103 : Fin 2 → Cell := twoBank p12103 ray12103
theorem signs12103 : ∀ j, Signs p12103 (bank12103 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12104 := params 7
abbrev ray12104 := rays 7
def bank12104 : Fin 2 → Cell := twoBank p12104 ray12104
theorem signs12104 : ∀ j, Signs p12104 (bank12104 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12105 := params 8
abbrev ray12105 := rays 8
def bank12105 : Fin 2 → Cell := twoBank p12105 ray12105
theorem signs12105 : ∀ j, Signs p12105 (bank12105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12106 := params 9
abbrev ray12106 := rays 9
def bank12106 : Fin 2 → Cell := twoBank p12106 ray12106
theorem signs12106 : ∀ j, Signs p12106 (bank12106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12107 := params 10
abbrev ray12107 := rays 10
def bank12107 : Fin 2 → Cell := twoBank p12107 ray12107
theorem signs12107 : ∀ j, Signs p12107 (bank12107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12108 := params 11
abbrev ray12108 := rays 11
def bank12108 : Fin 2 → Cell := twoBank p12108 ray12108
theorem signs12108 : ∀ j, Signs p12108 (bank12108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12109 := params 12
abbrev ray12109 := rays 12
def bank12109 : Fin 2 → Cell := twoBank p12109 ray12109
theorem signs12109 : ∀ j, Signs p12109 (bank12109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12110 := params 13
abbrev ray12110 := rays 13
def bank12110 : Fin 2 → Cell := twoBank p12110 ray12110
theorem signs12110 : ∀ j, Signs p12110 (bank12110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12111 := params 14
abbrev ray12111 := rays 14
def bank12111 : Fin 2 → Cell := twoBank p12111 ray12111
theorem signs12111 : ∀ j, Signs p12111 (bank12111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12112 := params 15
abbrev ray12112 := rays 15
def bank12112 : Fin 2 → Cell := twoBank p12112 ray12112
theorem signs12112 : ∀ j, Signs p12112 (bank12112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12113 := params 16
abbrev ray12113 := rays 16
def bank12113 : Fin 2 → Cell := twoBank p12113 ray12113
theorem signs12113 : ∀ j, Signs p12113 (bank12113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12114 := params 17
abbrev ray12114 := rays 17
def bank12114 : Fin 2 → Cell := twoBank p12114 ray12114
theorem signs12114 : ∀ j, Signs p12114 (bank12114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12115 := params 18
abbrev ray12115 := rays 18
def bank12115 : Fin 2 → Cell := twoBank p12115 ray12115
theorem signs12115 : ∀ j, Signs p12115 (bank12115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12116 := params 19
abbrev ray12116 := rays 19
def bank12116 : Fin 2 → Cell := twoBank p12116 ray12116
theorem signs12116 : ∀ j, Signs p12116 (bank12116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12117 := params 20
abbrev ray12117 := rays 20
def bank12117 : Fin 2 → Cell := twoBank p12117 ray12117
theorem signs12117 : ∀ j, Signs p12117 (bank12117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12118 := params 21
abbrev ray12118 := rays 21
def bank12118 : Fin 2 → Cell := twoBank p12118 ray12118
theorem signs12118 : ∀ j, Signs p12118 (bank12118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12119 := params 22
abbrev ray12119 := rays 22
def bank12119 : Fin 2 → Cell := twoBank p12119 ray12119
theorem signs12119 : ∀ j, Signs p12119 (bank12119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12120 := params 23
abbrev ray12120 := rays 23
def bank12120 : Fin 2 → Cell := twoBank p12120 ray12120
theorem signs12120 : ∀ j, Signs p12120 (bank12120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12121 := params 24
abbrev ray12121 := rays 24
def bank12121 : Fin 2 → Cell := twoBank p12121 ray12121
theorem signs12121 : ∀ j, Signs p12121 (bank12121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12122 := params 25
abbrev ray12122 := rays 25
def bank12122 : Fin 2 → Cell := twoBank p12122 ray12122
theorem signs12122 : ∀ j, Signs p12122 (bank12122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12123 := params 26
abbrev ray12123 := rays 26
def bank12123 : Fin 2 → Cell := twoBank p12123 ray12123
theorem signs12123 : ∀ j, Signs p12123 (bank12123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12124 := params 27
abbrev ray12124 := rays 27
def bank12124 : Fin 2 → Cell := twoBank p12124 ray12124
theorem signs12124 : ∀ j, Signs p12124 (bank12124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12125 := params 28
abbrev ray12125 := rays 28
def bank12125 : Fin 2 → Cell := twoBank p12125 ray12125
theorem signs12125 : ∀ j, Signs p12125 (bank12125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12126 := params 29
abbrev ray12126 := rays 29
def bank12126 : Fin 2 → Cell := twoBank p12126 ray12126
theorem signs12126 : ∀ j, Signs p12126 (bank12126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12127 := params 30
abbrev ray12127 := rays 30
def bank12127 : Fin 2 → Cell := twoBank p12127 ray12127
theorem signs12127 : ∀ j, Signs p12127 (bank12127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12128 := params 31
abbrev ray12128 := rays 31
def bank12128 : Fin 2 → Cell := twoBank p12128 ray12128
theorem signs12128 : ∀ j, Signs p12128 (bank12128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12097_12128
