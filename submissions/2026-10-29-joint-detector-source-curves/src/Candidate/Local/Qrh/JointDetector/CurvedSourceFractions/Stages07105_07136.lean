/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07105_07136
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98443769008338,98443463878017,98443158725449,98442853550635,98442548353576,98442243134273,98441937892726,98441632628936,98441327342904,98441022034631,98440716704117,98440411351364,98440105976372,98439800579141,98439495159673,98439189717968,98438884254028,98438578767852,98438273259442,98437967728799,98437662175923,98437356600815,98437051003476,98436745383906,98436439742107,98436134078079,98435828391823,98435522683339,98435216952629,98434911199693,98434605424532,98434299627147,98433993807538]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7104+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7105 := params 0
abbrev ray7105 := rays 0
def bank7105 : Fin 2 → Cell := twoBank p7105 ray7105
theorem signs7105 : ∀ j, Signs p7105 (bank7105 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7106 := params 1
abbrev ray7106 := rays 1
def bank7106 : Fin 2 → Cell := twoBank p7106 ray7106
theorem signs7106 : ∀ j, Signs p7106 (bank7106 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7107 := params 2
abbrev ray7107 := rays 2
def bank7107 : Fin 2 → Cell := twoBank p7107 ray7107
theorem signs7107 : ∀ j, Signs p7107 (bank7107 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7108 := params 3
abbrev ray7108 := rays 3
def bank7108 : Fin 2 → Cell := twoBank p7108 ray7108
theorem signs7108 : ∀ j, Signs p7108 (bank7108 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7109 := params 4
abbrev ray7109 := rays 4
def bank7109 : Fin 2 → Cell := twoBank p7109 ray7109
theorem signs7109 : ∀ j, Signs p7109 (bank7109 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7110 := params 5
abbrev ray7110 := rays 5
def bank7110 : Fin 2 → Cell := twoBank p7110 ray7110
theorem signs7110 : ∀ j, Signs p7110 (bank7110 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7111 := params 6
abbrev ray7111 := rays 6
def bank7111 : Fin 2 → Cell := twoBank p7111 ray7111
theorem signs7111 : ∀ j, Signs p7111 (bank7111 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7112 := params 7
abbrev ray7112 := rays 7
def bank7112 : Fin 2 → Cell := twoBank p7112 ray7112
theorem signs7112 : ∀ j, Signs p7112 (bank7112 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7113 := params 8
abbrev ray7113 := rays 8
def bank7113 : Fin 2 → Cell := twoBank p7113 ray7113
theorem signs7113 : ∀ j, Signs p7113 (bank7113 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7114 := params 9
abbrev ray7114 := rays 9
def bank7114 : Fin 2 → Cell := twoBank p7114 ray7114
theorem signs7114 : ∀ j, Signs p7114 (bank7114 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7115 := params 10
abbrev ray7115 := rays 10
def bank7115 : Fin 2 → Cell := twoBank p7115 ray7115
theorem signs7115 : ∀ j, Signs p7115 (bank7115 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7116 := params 11
abbrev ray7116 := rays 11
def bank7116 : Fin 2 → Cell := twoBank p7116 ray7116
theorem signs7116 : ∀ j, Signs p7116 (bank7116 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7117 := params 12
abbrev ray7117 := rays 12
def bank7117 : Fin 2 → Cell := twoBank p7117 ray7117
theorem signs7117 : ∀ j, Signs p7117 (bank7117 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7118 := params 13
abbrev ray7118 := rays 13
def bank7118 : Fin 2 → Cell := twoBank p7118 ray7118
theorem signs7118 : ∀ j, Signs p7118 (bank7118 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7119 := params 14
abbrev ray7119 := rays 14
def bank7119 : Fin 2 → Cell := twoBank p7119 ray7119
theorem signs7119 : ∀ j, Signs p7119 (bank7119 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7120 := params 15
abbrev ray7120 := rays 15
def bank7120 : Fin 2 → Cell := twoBank p7120 ray7120
theorem signs7120 : ∀ j, Signs p7120 (bank7120 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7121 := params 16
abbrev ray7121 := rays 16
def bank7121 : Fin 2 → Cell := twoBank p7121 ray7121
theorem signs7121 : ∀ j, Signs p7121 (bank7121 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7122 := params 17
abbrev ray7122 := rays 17
def bank7122 : Fin 2 → Cell := twoBank p7122 ray7122
theorem signs7122 : ∀ j, Signs p7122 (bank7122 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7123 := params 18
abbrev ray7123 := rays 18
def bank7123 : Fin 2 → Cell := twoBank p7123 ray7123
theorem signs7123 : ∀ j, Signs p7123 (bank7123 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7124 := params 19
abbrev ray7124 := rays 19
def bank7124 : Fin 2 → Cell := twoBank p7124 ray7124
theorem signs7124 : ∀ j, Signs p7124 (bank7124 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7125 := params 20
abbrev ray7125 := rays 20
def bank7125 : Fin 2 → Cell := twoBank p7125 ray7125
theorem signs7125 : ∀ j, Signs p7125 (bank7125 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7126 := params 21
abbrev ray7126 := rays 21
def bank7126 : Fin 2 → Cell := twoBank p7126 ray7126
theorem signs7126 : ∀ j, Signs p7126 (bank7126 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7127 := params 22
abbrev ray7127 := rays 22
def bank7127 : Fin 2 → Cell := twoBank p7127 ray7127
theorem signs7127 : ∀ j, Signs p7127 (bank7127 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7128 := params 23
abbrev ray7128 := rays 23
def bank7128 : Fin 2 → Cell := twoBank p7128 ray7128
theorem signs7128 : ∀ j, Signs p7128 (bank7128 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7129 := params 24
abbrev ray7129 := rays 24
def bank7129 : Fin 2 → Cell := twoBank p7129 ray7129
theorem signs7129 : ∀ j, Signs p7129 (bank7129 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7130 := params 25
abbrev ray7130 := rays 25
def bank7130 : Fin 2 → Cell := twoBank p7130 ray7130
theorem signs7130 : ∀ j, Signs p7130 (bank7130 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7131 := params 26
abbrev ray7131 := rays 26
def bank7131 : Fin 2 → Cell := twoBank p7131 ray7131
theorem signs7131 : ∀ j, Signs p7131 (bank7131 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7132 := params 27
abbrev ray7132 := rays 27
def bank7132 : Fin 2 → Cell := twoBank p7132 ray7132
theorem signs7132 : ∀ j, Signs p7132 (bank7132 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7133 := params 28
abbrev ray7133 := rays 28
def bank7133 : Fin 2 → Cell := twoBank p7133 ray7133
theorem signs7133 : ∀ j, Signs p7133 (bank7133 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7134 := params 29
abbrev ray7134 := rays 29
def bank7134 : Fin 2 → Cell := twoBank p7134 ray7134
theorem signs7134 : ∀ j, Signs p7134 (bank7134 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7135 := params 30
abbrev ray7135 := rays 30
def bank7135 : Fin 2 → Cell := twoBank p7135 ray7135
theorem signs7135 : ∀ j, Signs p7135 (bank7135 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7136 := params 31
abbrev ray7136 := rays 31
def bank7136 : Fin 2 → Cell := twoBank p7136 ray7136
theorem signs7136 : ∀ j, Signs p7136 (bank7136 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07105_07136
