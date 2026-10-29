/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14209_14240
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95755495333646,95755050745164,95754606140505,95754161519669,95753716882657,95753272229469,95752827560105,95752382874565,95751938172849,95751493454957,95751048720890,95750603970647,95750159204229,95749714421636,95749269622869,95748824807927,95748379976811,95747935129520,95747490266055,95747045386416,95746600490603,95746155578617,95745710650457,95745265706124,95744820745618,95744375768939,95743930776087,95743485767063,95743040741866,95742595700497,95742150642956,95741705569243,95741260479358]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14208+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14209 := params 0
abbrev ray14209 := rays 0
def bank14209 : Fin 1 → Cell := oneBank p14209 ray14209
theorem signs14209 : ∀ j, Signs p14209 (bank14209 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14210 := params 1
abbrev ray14210 := rays 1
def bank14210 : Fin 1 → Cell := oneBank p14210 ray14210
theorem signs14210 : ∀ j, Signs p14210 (bank14210 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14211 := params 2
abbrev ray14211 := rays 2
def bank14211 : Fin 1 → Cell := oneBank p14211 ray14211
theorem signs14211 : ∀ j, Signs p14211 (bank14211 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14212 := params 3
abbrev ray14212 := rays 3
def bank14212 : Fin 1 → Cell := oneBank p14212 ray14212
theorem signs14212 : ∀ j, Signs p14212 (bank14212 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14213 := params 4
abbrev ray14213 := rays 4
def bank14213 : Fin 1 → Cell := oneBank p14213 ray14213
theorem signs14213 : ∀ j, Signs p14213 (bank14213 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14214 := params 5
abbrev ray14214 := rays 5
def bank14214 : Fin 1 → Cell := oneBank p14214 ray14214
theorem signs14214 : ∀ j, Signs p14214 (bank14214 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14215 := params 6
abbrev ray14215 := rays 6
def bank14215 : Fin 1 → Cell := oneBank p14215 ray14215
theorem signs14215 : ∀ j, Signs p14215 (bank14215 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14216 := params 7
abbrev ray14216 := rays 7
def bank14216 : Fin 1 → Cell := oneBank p14216 ray14216
theorem signs14216 : ∀ j, Signs p14216 (bank14216 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14217 := params 8
abbrev ray14217 := rays 8
def bank14217 : Fin 1 → Cell := oneBank p14217 ray14217
theorem signs14217 : ∀ j, Signs p14217 (bank14217 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14218 := params 9
abbrev ray14218 := rays 9
def bank14218 : Fin 1 → Cell := oneBank p14218 ray14218
theorem signs14218 : ∀ j, Signs p14218 (bank14218 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14219 := params 10
abbrev ray14219 := rays 10
def bank14219 : Fin 1 → Cell := oneBank p14219 ray14219
theorem signs14219 : ∀ j, Signs p14219 (bank14219 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14220 := params 11
abbrev ray14220 := rays 11
def bank14220 : Fin 1 → Cell := oneBank p14220 ray14220
theorem signs14220 : ∀ j, Signs p14220 (bank14220 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14221 := params 12
abbrev ray14221 := rays 12
def bank14221 : Fin 1 → Cell := oneBank p14221 ray14221
theorem signs14221 : ∀ j, Signs p14221 (bank14221 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14222 := params 13
abbrev ray14222 := rays 13
def bank14222 : Fin 1 → Cell := oneBank p14222 ray14222
theorem signs14222 : ∀ j, Signs p14222 (bank14222 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14223 := params 14
abbrev ray14223 := rays 14
def bank14223 : Fin 1 → Cell := oneBank p14223 ray14223
theorem signs14223 : ∀ j, Signs p14223 (bank14223 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14224 := params 15
abbrev ray14224 := rays 15
def bank14224 : Fin 1 → Cell := oneBank p14224 ray14224
theorem signs14224 : ∀ j, Signs p14224 (bank14224 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14225 := params 16
abbrev ray14225 := rays 16
def bank14225 : Fin 1 → Cell := oneBank p14225 ray14225
theorem signs14225 : ∀ j, Signs p14225 (bank14225 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14226 := params 17
abbrev ray14226 := rays 17
def bank14226 : Fin 1 → Cell := oneBank p14226 ray14226
theorem signs14226 : ∀ j, Signs p14226 (bank14226 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14227 := params 18
abbrev ray14227 := rays 18
def bank14227 : Fin 1 → Cell := oneBank p14227 ray14227
theorem signs14227 : ∀ j, Signs p14227 (bank14227 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14228 := params 19
abbrev ray14228 := rays 19
def bank14228 : Fin 1 → Cell := oneBank p14228 ray14228
theorem signs14228 : ∀ j, Signs p14228 (bank14228 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14229 := params 20
abbrev ray14229 := rays 20
def bank14229 : Fin 1 → Cell := oneBank p14229 ray14229
theorem signs14229 : ∀ j, Signs p14229 (bank14229 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14230 := params 21
abbrev ray14230 := rays 21
def bank14230 : Fin 1 → Cell := oneBank p14230 ray14230
theorem signs14230 : ∀ j, Signs p14230 (bank14230 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14231 := params 22
abbrev ray14231 := rays 22
def bank14231 : Fin 1 → Cell := oneBank p14231 ray14231
theorem signs14231 : ∀ j, Signs p14231 (bank14231 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14232 := params 23
abbrev ray14232 := rays 23
def bank14232 : Fin 1 → Cell := oneBank p14232 ray14232
theorem signs14232 : ∀ j, Signs p14232 (bank14232 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14233 := params 24
abbrev ray14233 := rays 24
def bank14233 : Fin 1 → Cell := oneBank p14233 ray14233
theorem signs14233 : ∀ j, Signs p14233 (bank14233 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14234 := params 25
abbrev ray14234 := rays 25
def bank14234 : Fin 1 → Cell := oneBank p14234 ray14234
theorem signs14234 : ∀ j, Signs p14234 (bank14234 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14235 := params 26
abbrev ray14235 := rays 26
def bank14235 : Fin 1 → Cell := oneBank p14235 ray14235
theorem signs14235 : ∀ j, Signs p14235 (bank14235 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14236 := params 27
abbrev ray14236 := rays 27
def bank14236 : Fin 1 → Cell := oneBank p14236 ray14236
theorem signs14236 : ∀ j, Signs p14236 (bank14236 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14237 := params 28
abbrev ray14237 := rays 28
def bank14237 : Fin 1 → Cell := oneBank p14237 ray14237
theorem signs14237 : ∀ j, Signs p14237 (bank14237 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14238 := params 29
abbrev ray14238 := rays 29
def bank14238 : Fin 1 → Cell := oneBank p14238 ray14238
theorem signs14238 : ∀ j, Signs p14238 (bank14238 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14239 := params 30
abbrev ray14239 := rays 30
def bank14239 : Fin 1 → Cell := oneBank p14239 ray14239
theorem signs14239 : ∀ j, Signs p14239 (bank14239 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14240 := params 31
abbrev ray14240 := rays 31
def bank14240 : Fin 1 → Cell := oneBank p14240 ray14240
theorem signs14240 : ∀ j, Signs p14240 (bank14240 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14209_14240
