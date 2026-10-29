/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15169_15200
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95321266195326,95320806144243,95320346077112,95319885993933,95319425894706,95318965779431,95318505648108,95318045500737,95317585337319,95317125157853,95316664962340,95316204750779,95315744523171,95315284279516,95314824019814,95314363744065,95313903452269,95313443144426,95312982820537,95312522480601,95312062124619,95311601752590,95311141364515,95310680960394,95310220540227,95309760104014,95309299651755,95308839183450,95308378699100,95307918198704,95307457682263,95306997149776,95306536601244]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15168+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15169 := params 0
abbrev ray15169 := rays 0
def bank15169 : Fin 1 → Cell := oneBank p15169 ray15169
theorem signs15169 : ∀ j, Signs p15169 (bank15169 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15170 := params 1
abbrev ray15170 := rays 1
def bank15170 : Fin 1 → Cell := oneBank p15170 ray15170
theorem signs15170 : ∀ j, Signs p15170 (bank15170 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15171 := params 2
abbrev ray15171 := rays 2
def bank15171 : Fin 1 → Cell := oneBank p15171 ray15171
theorem signs15171 : ∀ j, Signs p15171 (bank15171 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15172 := params 3
abbrev ray15172 := rays 3
def bank15172 : Fin 1 → Cell := oneBank p15172 ray15172
theorem signs15172 : ∀ j, Signs p15172 (bank15172 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15173 := params 4
abbrev ray15173 := rays 4
def bank15173 : Fin 1 → Cell := oneBank p15173 ray15173
theorem signs15173 : ∀ j, Signs p15173 (bank15173 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15174 := params 5
abbrev ray15174 := rays 5
def bank15174 : Fin 1 → Cell := oneBank p15174 ray15174
theorem signs15174 : ∀ j, Signs p15174 (bank15174 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15175 := params 6
abbrev ray15175 := rays 6
def bank15175 : Fin 1 → Cell := oneBank p15175 ray15175
theorem signs15175 : ∀ j, Signs p15175 (bank15175 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15176 := params 7
abbrev ray15176 := rays 7
def bank15176 : Fin 1 → Cell := oneBank p15176 ray15176
theorem signs15176 : ∀ j, Signs p15176 (bank15176 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15177 := params 8
abbrev ray15177 := rays 8
def bank15177 : Fin 1 → Cell := oneBank p15177 ray15177
theorem signs15177 : ∀ j, Signs p15177 (bank15177 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15178 := params 9
abbrev ray15178 := rays 9
def bank15178 : Fin 1 → Cell := oneBank p15178 ray15178
theorem signs15178 : ∀ j, Signs p15178 (bank15178 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15179 := params 10
abbrev ray15179 := rays 10
def bank15179 : Fin 1 → Cell := oneBank p15179 ray15179
theorem signs15179 : ∀ j, Signs p15179 (bank15179 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15180 := params 11
abbrev ray15180 := rays 11
def bank15180 : Fin 1 → Cell := oneBank p15180 ray15180
theorem signs15180 : ∀ j, Signs p15180 (bank15180 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15181 := params 12
abbrev ray15181 := rays 12
def bank15181 : Fin 1 → Cell := oneBank p15181 ray15181
theorem signs15181 : ∀ j, Signs p15181 (bank15181 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15182 := params 13
abbrev ray15182 := rays 13
def bank15182 : Fin 1 → Cell := oneBank p15182 ray15182
theorem signs15182 : ∀ j, Signs p15182 (bank15182 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15183 := params 14
abbrev ray15183 := rays 14
def bank15183 : Fin 1 → Cell := oneBank p15183 ray15183
theorem signs15183 : ∀ j, Signs p15183 (bank15183 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15184 := params 15
abbrev ray15184 := rays 15
def bank15184 : Fin 1 → Cell := oneBank p15184 ray15184
theorem signs15184 : ∀ j, Signs p15184 (bank15184 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15185 := params 16
abbrev ray15185 := rays 16
def bank15185 : Fin 1 → Cell := oneBank p15185 ray15185
theorem signs15185 : ∀ j, Signs p15185 (bank15185 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15186 := params 17
abbrev ray15186 := rays 17
def bank15186 : Fin 1 → Cell := oneBank p15186 ray15186
theorem signs15186 : ∀ j, Signs p15186 (bank15186 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15187 := params 18
abbrev ray15187 := rays 18
def bank15187 : Fin 1 → Cell := oneBank p15187 ray15187
theorem signs15187 : ∀ j, Signs p15187 (bank15187 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15188 := params 19
abbrev ray15188 := rays 19
def bank15188 : Fin 1 → Cell := oneBank p15188 ray15188
theorem signs15188 : ∀ j, Signs p15188 (bank15188 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15189 := params 20
abbrev ray15189 := rays 20
def bank15189 : Fin 1 → Cell := oneBank p15189 ray15189
theorem signs15189 : ∀ j, Signs p15189 (bank15189 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15190 := params 21
abbrev ray15190 := rays 21
def bank15190 : Fin 1 → Cell := oneBank p15190 ray15190
theorem signs15190 : ∀ j, Signs p15190 (bank15190 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15191 := params 22
abbrev ray15191 := rays 22
def bank15191 : Fin 1 → Cell := oneBank p15191 ray15191
theorem signs15191 : ∀ j, Signs p15191 (bank15191 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15192 := params 23
abbrev ray15192 := rays 23
def bank15192 : Fin 1 → Cell := oneBank p15192 ray15192
theorem signs15192 : ∀ j, Signs p15192 (bank15192 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15193 := params 24
abbrev ray15193 := rays 24
def bank15193 : Fin 1 → Cell := oneBank p15193 ray15193
theorem signs15193 : ∀ j, Signs p15193 (bank15193 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15194 := params 25
abbrev ray15194 := rays 25
def bank15194 : Fin 1 → Cell := oneBank p15194 ray15194
theorem signs15194 : ∀ j, Signs p15194 (bank15194 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15195 := params 26
abbrev ray15195 := rays 26
def bank15195 : Fin 1 → Cell := oneBank p15195 ray15195
theorem signs15195 : ∀ j, Signs p15195 (bank15195 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15196 := params 27
abbrev ray15196 := rays 27
def bank15196 : Fin 1 → Cell := oneBank p15196 ray15196
theorem signs15196 : ∀ j, Signs p15196 (bank15196 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15197 := params 28
abbrev ray15197 := rays 28
def bank15197 : Fin 1 → Cell := oneBank p15197 ray15197
theorem signs15197 : ∀ j, Signs p15197 (bank15197 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15198 := params 29
abbrev ray15198 := rays 29
def bank15198 : Fin 1 → Cell := oneBank p15198 ray15198
theorem signs15198 : ∀ j, Signs p15198 (bank15198 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15199 := params 30
abbrev ray15199 := rays 30
def bank15199 : Fin 1 → Cell := oneBank p15199 ray15199
theorem signs15199 : ∀ j, Signs p15199 (bank15199 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15200 := params 31
abbrev ray15200 := rays 31
def bank15200 : Fin 1 → Cell := oneBank p15200 ray15200
theorem signs15200 : ∀ j, Signs p15200 (bank15200 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15169_15200
