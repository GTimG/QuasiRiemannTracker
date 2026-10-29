/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14241_14272
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95741260479358,95740815373302,95740370251074,95739925112675,95739479958105,95739034787364,95738589600452,95738144397370,95737699178117,95737253942694,95736808691101,95736363423338,95735918139405,95735472839303,95735027523031,95734582190590,95734136841980,95733691477201,95733246096253,95732800699137,95732355285852,95731909856399,95731464410778,95731018948989,95730573471032,95730127976908,95729682466616,95729236940157,95728791397531,95728345838738,95727900263778,95727454672652,95727009065359]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14240+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14241 := params 0
abbrev ray14241 := rays 0
def bank14241 : Fin 1 → Cell := oneBank p14241 ray14241
theorem signs14241 : ∀ j, Signs p14241 (bank14241 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14242 := params 1
abbrev ray14242 := rays 1
def bank14242 : Fin 1 → Cell := oneBank p14242 ray14242
theorem signs14242 : ∀ j, Signs p14242 (bank14242 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14243 := params 2
abbrev ray14243 := rays 2
def bank14243 : Fin 1 → Cell := oneBank p14243 ray14243
theorem signs14243 : ∀ j, Signs p14243 (bank14243 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14244 := params 3
abbrev ray14244 := rays 3
def bank14244 : Fin 1 → Cell := oneBank p14244 ray14244
theorem signs14244 : ∀ j, Signs p14244 (bank14244 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14245 := params 4
abbrev ray14245 := rays 4
def bank14245 : Fin 1 → Cell := oneBank p14245 ray14245
theorem signs14245 : ∀ j, Signs p14245 (bank14245 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14246 := params 5
abbrev ray14246 := rays 5
def bank14246 : Fin 1 → Cell := oneBank p14246 ray14246
theorem signs14246 : ∀ j, Signs p14246 (bank14246 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14247 := params 6
abbrev ray14247 := rays 6
def bank14247 : Fin 1 → Cell := oneBank p14247 ray14247
theorem signs14247 : ∀ j, Signs p14247 (bank14247 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14248 := params 7
abbrev ray14248 := rays 7
def bank14248 : Fin 1 → Cell := oneBank p14248 ray14248
theorem signs14248 : ∀ j, Signs p14248 (bank14248 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14249 := params 8
abbrev ray14249 := rays 8
def bank14249 : Fin 1 → Cell := oneBank p14249 ray14249
theorem signs14249 : ∀ j, Signs p14249 (bank14249 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14250 := params 9
abbrev ray14250 := rays 9
def bank14250 : Fin 1 → Cell := oneBank p14250 ray14250
theorem signs14250 : ∀ j, Signs p14250 (bank14250 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14251 := params 10
abbrev ray14251 := rays 10
def bank14251 : Fin 1 → Cell := oneBank p14251 ray14251
theorem signs14251 : ∀ j, Signs p14251 (bank14251 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14252 := params 11
abbrev ray14252 := rays 11
def bank14252 : Fin 1 → Cell := oneBank p14252 ray14252
theorem signs14252 : ∀ j, Signs p14252 (bank14252 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14253 := params 12
abbrev ray14253 := rays 12
def bank14253 : Fin 1 → Cell := oneBank p14253 ray14253
theorem signs14253 : ∀ j, Signs p14253 (bank14253 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14254 := params 13
abbrev ray14254 := rays 13
def bank14254 : Fin 1 → Cell := oneBank p14254 ray14254
theorem signs14254 : ∀ j, Signs p14254 (bank14254 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14255 := params 14
abbrev ray14255 := rays 14
def bank14255 : Fin 1 → Cell := oneBank p14255 ray14255
theorem signs14255 : ∀ j, Signs p14255 (bank14255 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14256 := params 15
abbrev ray14256 := rays 15
def bank14256 : Fin 1 → Cell := oneBank p14256 ray14256
theorem signs14256 : ∀ j, Signs p14256 (bank14256 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14257 := params 16
abbrev ray14257 := rays 16
def bank14257 : Fin 1 → Cell := oneBank p14257 ray14257
theorem signs14257 : ∀ j, Signs p14257 (bank14257 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14258 := params 17
abbrev ray14258 := rays 17
def bank14258 : Fin 1 → Cell := oneBank p14258 ray14258
theorem signs14258 : ∀ j, Signs p14258 (bank14258 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14259 := params 18
abbrev ray14259 := rays 18
def bank14259 : Fin 1 → Cell := oneBank p14259 ray14259
theorem signs14259 : ∀ j, Signs p14259 (bank14259 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14260 := params 19
abbrev ray14260 := rays 19
def bank14260 : Fin 1 → Cell := oneBank p14260 ray14260
theorem signs14260 : ∀ j, Signs p14260 (bank14260 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14261 := params 20
abbrev ray14261 := rays 20
def bank14261 : Fin 1 → Cell := oneBank p14261 ray14261
theorem signs14261 : ∀ j, Signs p14261 (bank14261 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14262 := params 21
abbrev ray14262 := rays 21
def bank14262 : Fin 1 → Cell := oneBank p14262 ray14262
theorem signs14262 : ∀ j, Signs p14262 (bank14262 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14263 := params 22
abbrev ray14263 := rays 22
def bank14263 : Fin 1 → Cell := oneBank p14263 ray14263
theorem signs14263 : ∀ j, Signs p14263 (bank14263 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14264 := params 23
abbrev ray14264 := rays 23
def bank14264 : Fin 1 → Cell := oneBank p14264 ray14264
theorem signs14264 : ∀ j, Signs p14264 (bank14264 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14265 := params 24
abbrev ray14265 := rays 24
def bank14265 : Fin 1 → Cell := oneBank p14265 ray14265
theorem signs14265 : ∀ j, Signs p14265 (bank14265 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14266 := params 25
abbrev ray14266 := rays 25
def bank14266 : Fin 1 → Cell := oneBank p14266 ray14266
theorem signs14266 : ∀ j, Signs p14266 (bank14266 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14267 := params 26
abbrev ray14267 := rays 26
def bank14267 : Fin 1 → Cell := oneBank p14267 ray14267
theorem signs14267 : ∀ j, Signs p14267 (bank14267 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14268 := params 27
abbrev ray14268 := rays 27
def bank14268 : Fin 1 → Cell := oneBank p14268 ray14268
theorem signs14268 : ∀ j, Signs p14268 (bank14268 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14269 := params 28
abbrev ray14269 := rays 28
def bank14269 : Fin 1 → Cell := oneBank p14269 ray14269
theorem signs14269 : ∀ j, Signs p14269 (bank14269 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14270 := params 29
abbrev ray14270 := rays 29
def bank14270 : Fin 1 → Cell := oneBank p14270 ray14270
theorem signs14270 : ∀ j, Signs p14270 (bank14270 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14271 := params 30
abbrev ray14271 := rays 30
def bank14271 : Fin 1 → Cell := oneBank p14271 ray14271
theorem signs14271 : ∀ j, Signs p14271 (bank14271 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14272 := params 31
abbrev ray14272 := rays 31
def bank14272 : Fin 1 → Cell := oneBank p14272 ray14272
theorem signs14272 : ∀ j, Signs p14272 (bank14272 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14241_14272
