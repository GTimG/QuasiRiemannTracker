/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06145_06176
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98726313856756,98726030455689,98725747031586,98725463584447,98725180114273,98724896621065,98724613104824,98724329565551,98724046003247,98723762417912,98723478809548,98723195178155,98722911523734,98722627846286,98722344145812,98722060422313,98721776675789,98721492906242,98721209113672,98720925298081,98720641459469,98720357597837,98720073713185,98719789805515,98719505874828,98719221921124,98718937944405,98718653944671,98718369921923,98718085876162,98717801807388,98717517715603,98717233600808]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6144+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6145 := params 0
abbrev ray6145 := rays 0
def bank6145 : Fin 2 → Cell := twoBank p6145 ray6145
theorem signs6145 : ∀ j, Signs p6145 (bank6145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6146 := params 1
abbrev ray6146 := rays 1
def bank6146 : Fin 2 → Cell := twoBank p6146 ray6146
theorem signs6146 : ∀ j, Signs p6146 (bank6146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6147 := params 2
abbrev ray6147 := rays 2
def bank6147 : Fin 2 → Cell := twoBank p6147 ray6147
theorem signs6147 : ∀ j, Signs p6147 (bank6147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6148 := params 3
abbrev ray6148 := rays 3
def bank6148 : Fin 2 → Cell := twoBank p6148 ray6148
theorem signs6148 : ∀ j, Signs p6148 (bank6148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6149 := params 4
abbrev ray6149 := rays 4
def bank6149 : Fin 2 → Cell := twoBank p6149 ray6149
theorem signs6149 : ∀ j, Signs p6149 (bank6149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6150 := params 5
abbrev ray6150 := rays 5
def bank6150 : Fin 2 → Cell := twoBank p6150 ray6150
theorem signs6150 : ∀ j, Signs p6150 (bank6150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6151 := params 6
abbrev ray6151 := rays 6
def bank6151 : Fin 2 → Cell := twoBank p6151 ray6151
theorem signs6151 : ∀ j, Signs p6151 (bank6151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6152 := params 7
abbrev ray6152 := rays 7
def bank6152 : Fin 2 → Cell := twoBank p6152 ray6152
theorem signs6152 : ∀ j, Signs p6152 (bank6152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6153 := params 8
abbrev ray6153 := rays 8
def bank6153 : Fin 2 → Cell := twoBank p6153 ray6153
theorem signs6153 : ∀ j, Signs p6153 (bank6153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6154 := params 9
abbrev ray6154 := rays 9
def bank6154 : Fin 2 → Cell := twoBank p6154 ray6154
theorem signs6154 : ∀ j, Signs p6154 (bank6154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6155 := params 10
abbrev ray6155 := rays 10
def bank6155 : Fin 2 → Cell := twoBank p6155 ray6155
theorem signs6155 : ∀ j, Signs p6155 (bank6155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6156 := params 11
abbrev ray6156 := rays 11
def bank6156 : Fin 2 → Cell := twoBank p6156 ray6156
theorem signs6156 : ∀ j, Signs p6156 (bank6156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6157 := params 12
abbrev ray6157 := rays 12
def bank6157 : Fin 2 → Cell := twoBank p6157 ray6157
theorem signs6157 : ∀ j, Signs p6157 (bank6157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6158 := params 13
abbrev ray6158 := rays 13
def bank6158 : Fin 2 → Cell := twoBank p6158 ray6158
theorem signs6158 : ∀ j, Signs p6158 (bank6158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6159 := params 14
abbrev ray6159 := rays 14
def bank6159 : Fin 2 → Cell := twoBank p6159 ray6159
theorem signs6159 : ∀ j, Signs p6159 (bank6159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6160 := params 15
abbrev ray6160 := rays 15
def bank6160 : Fin 2 → Cell := twoBank p6160 ray6160
theorem signs6160 : ∀ j, Signs p6160 (bank6160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6161 := params 16
abbrev ray6161 := rays 16
def bank6161 : Fin 2 → Cell := twoBank p6161 ray6161
theorem signs6161 : ∀ j, Signs p6161 (bank6161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6162 := params 17
abbrev ray6162 := rays 17
def bank6162 : Fin 2 → Cell := twoBank p6162 ray6162
theorem signs6162 : ∀ j, Signs p6162 (bank6162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6163 := params 18
abbrev ray6163 := rays 18
def bank6163 : Fin 2 → Cell := twoBank p6163 ray6163
theorem signs6163 : ∀ j, Signs p6163 (bank6163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6164 := params 19
abbrev ray6164 := rays 19
def bank6164 : Fin 2 → Cell := twoBank p6164 ray6164
theorem signs6164 : ∀ j, Signs p6164 (bank6164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6165 := params 20
abbrev ray6165 := rays 20
def bank6165 : Fin 2 → Cell := twoBank p6165 ray6165
theorem signs6165 : ∀ j, Signs p6165 (bank6165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6166 := params 21
abbrev ray6166 := rays 21
def bank6166 : Fin 2 → Cell := twoBank p6166 ray6166
theorem signs6166 : ∀ j, Signs p6166 (bank6166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6167 := params 22
abbrev ray6167 := rays 22
def bank6167 : Fin 2 → Cell := twoBank p6167 ray6167
theorem signs6167 : ∀ j, Signs p6167 (bank6167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6168 := params 23
abbrev ray6168 := rays 23
def bank6168 : Fin 2 → Cell := twoBank p6168 ray6168
theorem signs6168 : ∀ j, Signs p6168 (bank6168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6169 := params 24
abbrev ray6169 := rays 24
def bank6169 : Fin 2 → Cell := twoBank p6169 ray6169
theorem signs6169 : ∀ j, Signs p6169 (bank6169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6170 := params 25
abbrev ray6170 := rays 25
def bank6170 : Fin 2 → Cell := twoBank p6170 ray6170
theorem signs6170 : ∀ j, Signs p6170 (bank6170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6171 := params 26
abbrev ray6171 := rays 26
def bank6171 : Fin 2 → Cell := twoBank p6171 ray6171
theorem signs6171 : ∀ j, Signs p6171 (bank6171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6172 := params 27
abbrev ray6172 := rays 27
def bank6172 : Fin 2 → Cell := twoBank p6172 ray6172
theorem signs6172 : ∀ j, Signs p6172 (bank6172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6173 := params 28
abbrev ray6173 := rays 28
def bank6173 : Fin 2 → Cell := twoBank p6173 ray6173
theorem signs6173 : ∀ j, Signs p6173 (bank6173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6174 := params 29
abbrev ray6174 := rays 29
def bank6174 : Fin 2 → Cell := twoBank p6174 ray6174
theorem signs6174 : ∀ j, Signs p6174 (bank6174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6175 := params 30
abbrev ray6175 := rays 30
def bank6175 : Fin 2 → Cell := twoBank p6175 ray6175
theorem signs6175 : ∀ j, Signs p6175 (bank6175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6176 := params 31
abbrev ray6176 := rays 31
def bank6176 : Fin 2 → Cell := twoBank p6176 ray6176
theorem signs6176 : ∀ j, Signs p6176 (bank6176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06145_06176
