/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11169_11200
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97027799962209,97027409932864,97027019883785,97026629814972,97026239726426,97025849618148,97025459490137,97025069342395,97024679174922,97024288987718,97023898780784,97023508554120,97023118307727,97022728041605,97022337755755,97021947450177,97021557124872,97021166779840,97020776415082,97020386030598,97019995626389,97019605202455,97019214758797,97018824295415,97018433812309,97018043309480,97017652786929,97017262244656,97016871682661,97016481100945,97016090499509,97015699878353,97015309237477]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11168+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11169 := params 0
abbrev ray11169 := rays 0
def bank11169 : Fin 2 → Cell := twoBank p11169 ray11169
theorem signs11169 : ∀ j, Signs p11169 (bank11169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11170 := params 1
abbrev ray11170 := rays 1
def bank11170 : Fin 2 → Cell := twoBank p11170 ray11170
theorem signs11170 : ∀ j, Signs p11170 (bank11170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11171 := params 2
abbrev ray11171 := rays 2
def bank11171 : Fin 2 → Cell := twoBank p11171 ray11171
theorem signs11171 : ∀ j, Signs p11171 (bank11171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11172 := params 3
abbrev ray11172 := rays 3
def bank11172 : Fin 2 → Cell := twoBank p11172 ray11172
theorem signs11172 : ∀ j, Signs p11172 (bank11172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11173 := params 4
abbrev ray11173 := rays 4
def bank11173 : Fin 2 → Cell := twoBank p11173 ray11173
theorem signs11173 : ∀ j, Signs p11173 (bank11173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11174 := params 5
abbrev ray11174 := rays 5
def bank11174 : Fin 2 → Cell := twoBank p11174 ray11174
theorem signs11174 : ∀ j, Signs p11174 (bank11174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11175 := params 6
abbrev ray11175 := rays 6
def bank11175 : Fin 2 → Cell := twoBank p11175 ray11175
theorem signs11175 : ∀ j, Signs p11175 (bank11175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11176 := params 7
abbrev ray11176 := rays 7
def bank11176 : Fin 2 → Cell := twoBank p11176 ray11176
theorem signs11176 : ∀ j, Signs p11176 (bank11176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11177 := params 8
abbrev ray11177 := rays 8
def bank11177 : Fin 2 → Cell := twoBank p11177 ray11177
theorem signs11177 : ∀ j, Signs p11177 (bank11177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11178 := params 9
abbrev ray11178 := rays 9
def bank11178 : Fin 2 → Cell := twoBank p11178 ray11178
theorem signs11178 : ∀ j, Signs p11178 (bank11178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11179 := params 10
abbrev ray11179 := rays 10
def bank11179 : Fin 2 → Cell := twoBank p11179 ray11179
theorem signs11179 : ∀ j, Signs p11179 (bank11179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11180 := params 11
abbrev ray11180 := rays 11
def bank11180 : Fin 2 → Cell := twoBank p11180 ray11180
theorem signs11180 : ∀ j, Signs p11180 (bank11180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11181 := params 12
abbrev ray11181 := rays 12
def bank11181 : Fin 2 → Cell := twoBank p11181 ray11181
theorem signs11181 : ∀ j, Signs p11181 (bank11181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11182 := params 13
abbrev ray11182 := rays 13
def bank11182 : Fin 2 → Cell := twoBank p11182 ray11182
theorem signs11182 : ∀ j, Signs p11182 (bank11182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11183 := params 14
abbrev ray11183 := rays 14
def bank11183 : Fin 2 → Cell := twoBank p11183 ray11183
theorem signs11183 : ∀ j, Signs p11183 (bank11183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11184 := params 15
abbrev ray11184 := rays 15
def bank11184 : Fin 2 → Cell := twoBank p11184 ray11184
theorem signs11184 : ∀ j, Signs p11184 (bank11184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11185 := params 16
abbrev ray11185 := rays 16
def bank11185 : Fin 2 → Cell := twoBank p11185 ray11185
theorem signs11185 : ∀ j, Signs p11185 (bank11185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11186 := params 17
abbrev ray11186 := rays 17
def bank11186 : Fin 2 → Cell := twoBank p11186 ray11186
theorem signs11186 : ∀ j, Signs p11186 (bank11186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11187 := params 18
abbrev ray11187 := rays 18
def bank11187 : Fin 2 → Cell := twoBank p11187 ray11187
theorem signs11187 : ∀ j, Signs p11187 (bank11187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11188 := params 19
abbrev ray11188 := rays 19
def bank11188 : Fin 2 → Cell := twoBank p11188 ray11188
theorem signs11188 : ∀ j, Signs p11188 (bank11188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11189 := params 20
abbrev ray11189 := rays 20
def bank11189 : Fin 2 → Cell := twoBank p11189 ray11189
theorem signs11189 : ∀ j, Signs p11189 (bank11189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11190 := params 21
abbrev ray11190 := rays 21
def bank11190 : Fin 2 → Cell := twoBank p11190 ray11190
theorem signs11190 : ∀ j, Signs p11190 (bank11190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11191 := params 22
abbrev ray11191 := rays 22
def bank11191 : Fin 2 → Cell := twoBank p11191 ray11191
theorem signs11191 : ∀ j, Signs p11191 (bank11191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11192 := params 23
abbrev ray11192 := rays 23
def bank11192 : Fin 2 → Cell := twoBank p11192 ray11192
theorem signs11192 : ∀ j, Signs p11192 (bank11192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11193 := params 24
abbrev ray11193 := rays 24
def bank11193 : Fin 2 → Cell := twoBank p11193 ray11193
theorem signs11193 : ∀ j, Signs p11193 (bank11193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11194 := params 25
abbrev ray11194 := rays 25
def bank11194 : Fin 2 → Cell := twoBank p11194 ray11194
theorem signs11194 : ∀ j, Signs p11194 (bank11194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11195 := params 26
abbrev ray11195 := rays 26
def bank11195 : Fin 2 → Cell := twoBank p11195 ray11195
theorem signs11195 : ∀ j, Signs p11195 (bank11195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11196 := params 27
abbrev ray11196 := rays 27
def bank11196 : Fin 2 → Cell := twoBank p11196 ray11196
theorem signs11196 : ∀ j, Signs p11196 (bank11196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11197 := params 28
abbrev ray11197 := rays 28
def bank11197 : Fin 2 → Cell := twoBank p11197 ray11197
theorem signs11197 : ∀ j, Signs p11197 (bank11197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11198 := params 29
abbrev ray11198 := rays 29
def bank11198 : Fin 2 → Cell := twoBank p11198 ray11198
theorem signs11198 : ∀ j, Signs p11198 (bank11198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11199 := params 30
abbrev ray11199 := rays 30
def bank11199 : Fin 2 → Cell := twoBank p11199 ray11199
theorem signs11199 : ∀ j, Signs p11199 (bank11199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11200 := params 31
abbrev ray11200 := rays 31
def bank11200 : Fin 2 → Cell := twoBank p11200 ray11200
theorem signs11200 : ∀ j, Signs p11200 (bank11200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11169_11200
