/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07137_07168
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98433993807538,98433687965707,98433382101654,98433076215380,98432770306885,98432464376171,98432158423238,98431852448087,98431546450719,98431240431134,98430934389333,98430628325318,98430322239088,98430016130645,98429709999989,98429403847122,98429097672044,98428791474755,98428485255257,98428179013550,98427872749635,98427566463513,98427260155184,98426953824650,98426647471911,98426341096968,98426034699821,98425728280472,98425421838921,98425115375169,98424808889217,98424502381065,98424195850715]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7136+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7137 := params 0
abbrev ray7137 := rays 0
def bank7137 : Fin 2 → Cell := twoBank p7137 ray7137
theorem signs7137 : ∀ j, Signs p7137 (bank7137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7138 := params 1
abbrev ray7138 := rays 1
def bank7138 : Fin 2 → Cell := twoBank p7138 ray7138
theorem signs7138 : ∀ j, Signs p7138 (bank7138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7139 := params 2
abbrev ray7139 := rays 2
def bank7139 : Fin 2 → Cell := twoBank p7139 ray7139
theorem signs7139 : ∀ j, Signs p7139 (bank7139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7140 := params 3
abbrev ray7140 := rays 3
def bank7140 : Fin 2 → Cell := twoBank p7140 ray7140
theorem signs7140 : ∀ j, Signs p7140 (bank7140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7141 := params 4
abbrev ray7141 := rays 4
def bank7141 : Fin 2 → Cell := twoBank p7141 ray7141
theorem signs7141 : ∀ j, Signs p7141 (bank7141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7142 := params 5
abbrev ray7142 := rays 5
def bank7142 : Fin 2 → Cell := twoBank p7142 ray7142
theorem signs7142 : ∀ j, Signs p7142 (bank7142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7143 := params 6
abbrev ray7143 := rays 6
def bank7143 : Fin 2 → Cell := twoBank p7143 ray7143
theorem signs7143 : ∀ j, Signs p7143 (bank7143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7144 := params 7
abbrev ray7144 := rays 7
def bank7144 : Fin 2 → Cell := twoBank p7144 ray7144
theorem signs7144 : ∀ j, Signs p7144 (bank7144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7145 := params 8
abbrev ray7145 := rays 8
def bank7145 : Fin 2 → Cell := twoBank p7145 ray7145
theorem signs7145 : ∀ j, Signs p7145 (bank7145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7146 := params 9
abbrev ray7146 := rays 9
def bank7146 : Fin 2 → Cell := twoBank p7146 ray7146
theorem signs7146 : ∀ j, Signs p7146 (bank7146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7147 := params 10
abbrev ray7147 := rays 10
def bank7147 : Fin 2 → Cell := twoBank p7147 ray7147
theorem signs7147 : ∀ j, Signs p7147 (bank7147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7148 := params 11
abbrev ray7148 := rays 11
def bank7148 : Fin 2 → Cell := twoBank p7148 ray7148
theorem signs7148 : ∀ j, Signs p7148 (bank7148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7149 := params 12
abbrev ray7149 := rays 12
def bank7149 : Fin 2 → Cell := twoBank p7149 ray7149
theorem signs7149 : ∀ j, Signs p7149 (bank7149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7150 := params 13
abbrev ray7150 := rays 13
def bank7150 : Fin 2 → Cell := twoBank p7150 ray7150
theorem signs7150 : ∀ j, Signs p7150 (bank7150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7151 := params 14
abbrev ray7151 := rays 14
def bank7151 : Fin 2 → Cell := twoBank p7151 ray7151
theorem signs7151 : ∀ j, Signs p7151 (bank7151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7152 := params 15
abbrev ray7152 := rays 15
def bank7152 : Fin 2 → Cell := twoBank p7152 ray7152
theorem signs7152 : ∀ j, Signs p7152 (bank7152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7153 := params 16
abbrev ray7153 := rays 16
def bank7153 : Fin 2 → Cell := twoBank p7153 ray7153
theorem signs7153 : ∀ j, Signs p7153 (bank7153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7154 := params 17
abbrev ray7154 := rays 17
def bank7154 : Fin 2 → Cell := twoBank p7154 ray7154
theorem signs7154 : ∀ j, Signs p7154 (bank7154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7155 := params 18
abbrev ray7155 := rays 18
def bank7155 : Fin 2 → Cell := twoBank p7155 ray7155
theorem signs7155 : ∀ j, Signs p7155 (bank7155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7156 := params 19
abbrev ray7156 := rays 19
def bank7156 : Fin 2 → Cell := twoBank p7156 ray7156
theorem signs7156 : ∀ j, Signs p7156 (bank7156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7157 := params 20
abbrev ray7157 := rays 20
def bank7157 : Fin 2 → Cell := twoBank p7157 ray7157
theorem signs7157 : ∀ j, Signs p7157 (bank7157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7158 := params 21
abbrev ray7158 := rays 21
def bank7158 : Fin 2 → Cell := twoBank p7158 ray7158
theorem signs7158 : ∀ j, Signs p7158 (bank7158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7159 := params 22
abbrev ray7159 := rays 22
def bank7159 : Fin 2 → Cell := twoBank p7159 ray7159
theorem signs7159 : ∀ j, Signs p7159 (bank7159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7160 := params 23
abbrev ray7160 := rays 23
def bank7160 : Fin 2 → Cell := twoBank p7160 ray7160
theorem signs7160 : ∀ j, Signs p7160 (bank7160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7161 := params 24
abbrev ray7161 := rays 24
def bank7161 : Fin 2 → Cell := twoBank p7161 ray7161
theorem signs7161 : ∀ j, Signs p7161 (bank7161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7162 := params 25
abbrev ray7162 := rays 25
def bank7162 : Fin 2 → Cell := twoBank p7162 ray7162
theorem signs7162 : ∀ j, Signs p7162 (bank7162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7163 := params 26
abbrev ray7163 := rays 26
def bank7163 : Fin 2 → Cell := twoBank p7163 ray7163
theorem signs7163 : ∀ j, Signs p7163 (bank7163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7164 := params 27
abbrev ray7164 := rays 27
def bank7164 : Fin 2 → Cell := twoBank p7164 ray7164
theorem signs7164 : ∀ j, Signs p7164 (bank7164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7165 := params 28
abbrev ray7165 := rays 28
def bank7165 : Fin 2 → Cell := twoBank p7165 ray7165
theorem signs7165 : ∀ j, Signs p7165 (bank7165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7166 := params 29
abbrev ray7166 := rays 29
def bank7166 : Fin 2 → Cell := twoBank p7166 ray7166
theorem signs7166 : ∀ j, Signs p7166 (bank7166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7167 := params 30
abbrev ray7167 := rays 30
def bank7167 : Fin 2 → Cell := twoBank p7167 ray7167
theorem signs7167 : ∀ j, Signs p7167 (bank7167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7168 := params 31
abbrev ray7168 := rays 31
def bank7168 : Fin 2 → Cell := twoBank p7168 ray7168
theorem signs7168 : ∀ j, Signs p7168 (bank7168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07137_07168
