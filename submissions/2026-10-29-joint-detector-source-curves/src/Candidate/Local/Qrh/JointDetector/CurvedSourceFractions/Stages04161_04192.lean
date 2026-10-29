/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04161_04192
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99242015964859,99241780124010,99241544258178,99241308367364,99241072451569,99240836510794,99240600545040,99240364554308,99240128538599,99239892497915,99239656432257,99239420341625,99239184226021,99238948085446,99238711919901,99238475729387,99238239513905,99238003273456,99237767008042,99237530717663,99237294402321,99237058062017,99236821696751,99236585306525,99236348891340,99236112451197,99235875986097,99235639496042,99235402981032,99235166441069,99234929876153,99234693286286,99234456671469]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4160+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4161 := params 0
abbrev ray4161 := rays 0
def bank4161 : Fin 2 → Cell := twoBank p4161 ray4161
theorem signs4161 : ∀ j, Signs p4161 (bank4161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4162 := params 1
abbrev ray4162 := rays 1
def bank4162 : Fin 2 → Cell := twoBank p4162 ray4162
theorem signs4162 : ∀ j, Signs p4162 (bank4162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4163 := params 2
abbrev ray4163 := rays 2
def bank4163 : Fin 2 → Cell := twoBank p4163 ray4163
theorem signs4163 : ∀ j, Signs p4163 (bank4163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4164 := params 3
abbrev ray4164 := rays 3
def bank4164 : Fin 2 → Cell := twoBank p4164 ray4164
theorem signs4164 : ∀ j, Signs p4164 (bank4164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4165 := params 4
abbrev ray4165 := rays 4
def bank4165 : Fin 2 → Cell := twoBank p4165 ray4165
theorem signs4165 : ∀ j, Signs p4165 (bank4165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4166 := params 5
abbrev ray4166 := rays 5
def bank4166 : Fin 2 → Cell := twoBank p4166 ray4166
theorem signs4166 : ∀ j, Signs p4166 (bank4166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4167 := params 6
abbrev ray4167 := rays 6
def bank4167 : Fin 2 → Cell := twoBank p4167 ray4167
theorem signs4167 : ∀ j, Signs p4167 (bank4167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4168 := params 7
abbrev ray4168 := rays 7
def bank4168 : Fin 2 → Cell := twoBank p4168 ray4168
theorem signs4168 : ∀ j, Signs p4168 (bank4168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4169 := params 8
abbrev ray4169 := rays 8
def bank4169 : Fin 2 → Cell := twoBank p4169 ray4169
theorem signs4169 : ∀ j, Signs p4169 (bank4169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4170 := params 9
abbrev ray4170 := rays 9
def bank4170 : Fin 2 → Cell := twoBank p4170 ray4170
theorem signs4170 : ∀ j, Signs p4170 (bank4170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4171 := params 10
abbrev ray4171 := rays 10
def bank4171 : Fin 2 → Cell := twoBank p4171 ray4171
theorem signs4171 : ∀ j, Signs p4171 (bank4171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4172 := params 11
abbrev ray4172 := rays 11
def bank4172 : Fin 2 → Cell := twoBank p4172 ray4172
theorem signs4172 : ∀ j, Signs p4172 (bank4172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4173 := params 12
abbrev ray4173 := rays 12
def bank4173 : Fin 2 → Cell := twoBank p4173 ray4173
theorem signs4173 : ∀ j, Signs p4173 (bank4173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4174 := params 13
abbrev ray4174 := rays 13
def bank4174 : Fin 2 → Cell := twoBank p4174 ray4174
theorem signs4174 : ∀ j, Signs p4174 (bank4174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4175 := params 14
abbrev ray4175 := rays 14
def bank4175 : Fin 2 → Cell := twoBank p4175 ray4175
theorem signs4175 : ∀ j, Signs p4175 (bank4175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4176 := params 15
abbrev ray4176 := rays 15
def bank4176 : Fin 2 → Cell := twoBank p4176 ray4176
theorem signs4176 : ∀ j, Signs p4176 (bank4176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4177 := params 16
abbrev ray4177 := rays 16
def bank4177 : Fin 2 → Cell := twoBank p4177 ray4177
theorem signs4177 : ∀ j, Signs p4177 (bank4177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4178 := params 17
abbrev ray4178 := rays 17
def bank4178 : Fin 2 → Cell := twoBank p4178 ray4178
theorem signs4178 : ∀ j, Signs p4178 (bank4178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4179 := params 18
abbrev ray4179 := rays 18
def bank4179 : Fin 2 → Cell := twoBank p4179 ray4179
theorem signs4179 : ∀ j, Signs p4179 (bank4179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4180 := params 19
abbrev ray4180 := rays 19
def bank4180 : Fin 2 → Cell := twoBank p4180 ray4180
theorem signs4180 : ∀ j, Signs p4180 (bank4180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4181 := params 20
abbrev ray4181 := rays 20
def bank4181 : Fin 2 → Cell := twoBank p4181 ray4181
theorem signs4181 : ∀ j, Signs p4181 (bank4181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4182 := params 21
abbrev ray4182 := rays 21
def bank4182 : Fin 2 → Cell := twoBank p4182 ray4182
theorem signs4182 : ∀ j, Signs p4182 (bank4182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4183 := params 22
abbrev ray4183 := rays 22
def bank4183 : Fin 2 → Cell := twoBank p4183 ray4183
theorem signs4183 : ∀ j, Signs p4183 (bank4183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4184 := params 23
abbrev ray4184 := rays 23
def bank4184 : Fin 2 → Cell := twoBank p4184 ray4184
theorem signs4184 : ∀ j, Signs p4184 (bank4184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4185 := params 24
abbrev ray4185 := rays 24
def bank4185 : Fin 2 → Cell := twoBank p4185 ray4185
theorem signs4185 : ∀ j, Signs p4185 (bank4185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4186 := params 25
abbrev ray4186 := rays 25
def bank4186 : Fin 2 → Cell := twoBank p4186 ray4186
theorem signs4186 : ∀ j, Signs p4186 (bank4186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4187 := params 26
abbrev ray4187 := rays 26
def bank4187 : Fin 2 → Cell := twoBank p4187 ray4187
theorem signs4187 : ∀ j, Signs p4187 (bank4187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4188 := params 27
abbrev ray4188 := rays 27
def bank4188 : Fin 2 → Cell := twoBank p4188 ray4188
theorem signs4188 : ∀ j, Signs p4188 (bank4188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4189 := params 28
abbrev ray4189 := rays 28
def bank4189 : Fin 2 → Cell := twoBank p4189 ray4189
theorem signs4189 : ∀ j, Signs p4189 (bank4189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4190 := params 29
abbrev ray4190 := rays 29
def bank4190 : Fin 2 → Cell := twoBank p4190 ray4190
theorem signs4190 : ∀ j, Signs p4190 (bank4190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4191 := params 30
abbrev ray4191 := rays 30
def bank4191 : Fin 2 → Cell := twoBank p4191 ray4191
theorem signs4191 : ∀ j, Signs p4191 (bank4191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4192 := params 31
abbrev ray4192 := rays 31
def bank4192 : Fin 2 → Cell := twoBank p4192 ray4192
theorem signs4192 : ∀ j, Signs p4192 (bank4192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04161_04192
