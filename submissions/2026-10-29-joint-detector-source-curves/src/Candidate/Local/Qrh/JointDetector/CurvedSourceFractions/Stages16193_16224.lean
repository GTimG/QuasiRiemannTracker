/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16193_16224
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94841782375297,94841305929069,94840829466854,94840352988653,94839876494465,94839399984291,94838923458130,94838446915983,94837970357849,94837493783729,94837017193623,94836540587530,94836063965451,94835587327386,94835110673334,94834634003296,94834157317272,94833680615262,94833203897265,94832727163282,94832250413313,94831773647358,94831296865417,94830820067490,94830343253577,94829866423678,94829389577793,94828912715922,94828435838065,94827958944222,94827482034393,94827005108578,94826528166777]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16192+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16193 := params 0
abbrev ray16193 := rays 0
def bank16193 : Fin 1 → Cell := oneBank p16193 ray16193
theorem signs16193 : ∀ j, Signs p16193 (bank16193 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16194 := params 1
abbrev ray16194 := rays 1
def bank16194 : Fin 1 → Cell := oneBank p16194 ray16194
theorem signs16194 : ∀ j, Signs p16194 (bank16194 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16195 := params 2
abbrev ray16195 := rays 2
def bank16195 : Fin 1 → Cell := oneBank p16195 ray16195
theorem signs16195 : ∀ j, Signs p16195 (bank16195 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16196 := params 3
abbrev ray16196 := rays 3
def bank16196 : Fin 1 → Cell := oneBank p16196 ray16196
theorem signs16196 : ∀ j, Signs p16196 (bank16196 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16197 := params 4
abbrev ray16197 := rays 4
def bank16197 : Fin 1 → Cell := oneBank p16197 ray16197
theorem signs16197 : ∀ j, Signs p16197 (bank16197 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16198 := params 5
abbrev ray16198 := rays 5
def bank16198 : Fin 1 → Cell := oneBank p16198 ray16198
theorem signs16198 : ∀ j, Signs p16198 (bank16198 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16199 := params 6
abbrev ray16199 := rays 6
def bank16199 : Fin 1 → Cell := oneBank p16199 ray16199
theorem signs16199 : ∀ j, Signs p16199 (bank16199 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16200 := params 7
abbrev ray16200 := rays 7
def bank16200 : Fin 1 → Cell := oneBank p16200 ray16200
theorem signs16200 : ∀ j, Signs p16200 (bank16200 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16201 := params 8
abbrev ray16201 := rays 8
def bank16201 : Fin 1 → Cell := oneBank p16201 ray16201
theorem signs16201 : ∀ j, Signs p16201 (bank16201 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16202 := params 9
abbrev ray16202 := rays 9
def bank16202 : Fin 1 → Cell := oneBank p16202 ray16202
theorem signs16202 : ∀ j, Signs p16202 (bank16202 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16203 := params 10
abbrev ray16203 := rays 10
def bank16203 : Fin 1 → Cell := oneBank p16203 ray16203
theorem signs16203 : ∀ j, Signs p16203 (bank16203 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16204 := params 11
abbrev ray16204 := rays 11
def bank16204 : Fin 1 → Cell := oneBank p16204 ray16204
theorem signs16204 : ∀ j, Signs p16204 (bank16204 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16205 := params 12
abbrev ray16205 := rays 12
def bank16205 : Fin 1 → Cell := oneBank p16205 ray16205
theorem signs16205 : ∀ j, Signs p16205 (bank16205 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16206 := params 13
abbrev ray16206 := rays 13
def bank16206 : Fin 1 → Cell := oneBank p16206 ray16206
theorem signs16206 : ∀ j, Signs p16206 (bank16206 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16207 := params 14
abbrev ray16207 := rays 14
def bank16207 : Fin 1 → Cell := oneBank p16207 ray16207
theorem signs16207 : ∀ j, Signs p16207 (bank16207 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16208 := params 15
abbrev ray16208 := rays 15
def bank16208 : Fin 1 → Cell := oneBank p16208 ray16208
theorem signs16208 : ∀ j, Signs p16208 (bank16208 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16209 := params 16
abbrev ray16209 := rays 16
def bank16209 : Fin 1 → Cell := oneBank p16209 ray16209
theorem signs16209 : ∀ j, Signs p16209 (bank16209 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16210 := params 17
abbrev ray16210 := rays 17
def bank16210 : Fin 1 → Cell := oneBank p16210 ray16210
theorem signs16210 : ∀ j, Signs p16210 (bank16210 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16211 := params 18
abbrev ray16211 := rays 18
def bank16211 : Fin 1 → Cell := oneBank p16211 ray16211
theorem signs16211 : ∀ j, Signs p16211 (bank16211 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16212 := params 19
abbrev ray16212 := rays 19
def bank16212 : Fin 1 → Cell := oneBank p16212 ray16212
theorem signs16212 : ∀ j, Signs p16212 (bank16212 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16213 := params 20
abbrev ray16213 := rays 20
def bank16213 : Fin 1 → Cell := oneBank p16213 ray16213
theorem signs16213 : ∀ j, Signs p16213 (bank16213 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16214 := params 21
abbrev ray16214 := rays 21
def bank16214 : Fin 1 → Cell := oneBank p16214 ray16214
theorem signs16214 : ∀ j, Signs p16214 (bank16214 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16215 := params 22
abbrev ray16215 := rays 22
def bank16215 : Fin 1 → Cell := oneBank p16215 ray16215
theorem signs16215 : ∀ j, Signs p16215 (bank16215 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16216 := params 23
abbrev ray16216 := rays 23
def bank16216 : Fin 1 → Cell := oneBank p16216 ray16216
theorem signs16216 : ∀ j, Signs p16216 (bank16216 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16217 := params 24
abbrev ray16217 := rays 24
def bank16217 : Fin 1 → Cell := oneBank p16217 ray16217
theorem signs16217 : ∀ j, Signs p16217 (bank16217 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16218 := params 25
abbrev ray16218 := rays 25
def bank16218 : Fin 1 → Cell := oneBank p16218 ray16218
theorem signs16218 : ∀ j, Signs p16218 (bank16218 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16219 := params 26
abbrev ray16219 := rays 26
def bank16219 : Fin 1 → Cell := oneBank p16219 ray16219
theorem signs16219 : ∀ j, Signs p16219 (bank16219 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16220 := params 27
abbrev ray16220 := rays 27
def bank16220 : Fin 1 → Cell := oneBank p16220 ray16220
theorem signs16220 : ∀ j, Signs p16220 (bank16220 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16221 := params 28
abbrev ray16221 := rays 28
def bank16221 : Fin 1 → Cell := oneBank p16221 ray16221
theorem signs16221 : ∀ j, Signs p16221 (bank16221 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16222 := params 29
abbrev ray16222 := rays 29
def bank16222 : Fin 1 → Cell := oneBank p16222 ray16222
theorem signs16222 : ∀ j, Signs p16222 (bank16222 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16223 := params 30
abbrev ray16223 := rays 30
def bank16223 : Fin 1 → Cell := oneBank p16223 ray16223
theorem signs16223 : ∀ j, Signs p16223 (bank16223 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16224 := params 31
abbrev ray16224 := rays 31
def bank16224 : Fin 1 → Cell := oneBank p16224 ray16224
theorem signs16224 : ∀ j, Signs p16224 (bank16224 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16193_16224
