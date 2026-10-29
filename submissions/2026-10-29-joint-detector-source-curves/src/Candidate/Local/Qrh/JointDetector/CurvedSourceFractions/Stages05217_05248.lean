/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05217_05248
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98979260508178,98978998874091,98978737216114,98978475534248,98978213828494,98977952098854,98977690345328,98977428567917,98977166766622,98976904941444,98976643092384,98976381219443,98976119322622,98975857401922,98975595457343,98975333488887,98975071496555,98974809480348,98974547440267,98974285376312,98974023288485,98973761176787,98973499041218,98973236881780,98972974698473,98972712491299,98972450260258,98972188005352,98971925726581,98971663423947,98971401097450,98971138747091,98970876372872]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5216+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5217 := params 0
abbrev ray5217 := rays 0
def bank5217 : Fin 2 → Cell := twoBank p5217 ray5217
theorem signs5217 : ∀ j, Signs p5217 (bank5217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5218 := params 1
abbrev ray5218 := rays 1
def bank5218 : Fin 2 → Cell := twoBank p5218 ray5218
theorem signs5218 : ∀ j, Signs p5218 (bank5218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5219 := params 2
abbrev ray5219 := rays 2
def bank5219 : Fin 2 → Cell := twoBank p5219 ray5219
theorem signs5219 : ∀ j, Signs p5219 (bank5219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5220 := params 3
abbrev ray5220 := rays 3
def bank5220 : Fin 2 → Cell := twoBank p5220 ray5220
theorem signs5220 : ∀ j, Signs p5220 (bank5220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5221 := params 4
abbrev ray5221 := rays 4
def bank5221 : Fin 2 → Cell := twoBank p5221 ray5221
theorem signs5221 : ∀ j, Signs p5221 (bank5221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5222 := params 5
abbrev ray5222 := rays 5
def bank5222 : Fin 2 → Cell := twoBank p5222 ray5222
theorem signs5222 : ∀ j, Signs p5222 (bank5222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5223 := params 6
abbrev ray5223 := rays 6
def bank5223 : Fin 2 → Cell := twoBank p5223 ray5223
theorem signs5223 : ∀ j, Signs p5223 (bank5223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5224 := params 7
abbrev ray5224 := rays 7
def bank5224 : Fin 2 → Cell := twoBank p5224 ray5224
theorem signs5224 : ∀ j, Signs p5224 (bank5224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5225 := params 8
abbrev ray5225 := rays 8
def bank5225 : Fin 2 → Cell := twoBank p5225 ray5225
theorem signs5225 : ∀ j, Signs p5225 (bank5225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5226 := params 9
abbrev ray5226 := rays 9
def bank5226 : Fin 2 → Cell := twoBank p5226 ray5226
theorem signs5226 : ∀ j, Signs p5226 (bank5226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5227 := params 10
abbrev ray5227 := rays 10
def bank5227 : Fin 2 → Cell := twoBank p5227 ray5227
theorem signs5227 : ∀ j, Signs p5227 (bank5227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5228 := params 11
abbrev ray5228 := rays 11
def bank5228 : Fin 2 → Cell := twoBank p5228 ray5228
theorem signs5228 : ∀ j, Signs p5228 (bank5228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5229 := params 12
abbrev ray5229 := rays 12
def bank5229 : Fin 2 → Cell := twoBank p5229 ray5229
theorem signs5229 : ∀ j, Signs p5229 (bank5229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5230 := params 13
abbrev ray5230 := rays 13
def bank5230 : Fin 2 → Cell := twoBank p5230 ray5230
theorem signs5230 : ∀ j, Signs p5230 (bank5230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5231 := params 14
abbrev ray5231 := rays 14
def bank5231 : Fin 2 → Cell := twoBank p5231 ray5231
theorem signs5231 : ∀ j, Signs p5231 (bank5231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5232 := params 15
abbrev ray5232 := rays 15
def bank5232 : Fin 2 → Cell := twoBank p5232 ray5232
theorem signs5232 : ∀ j, Signs p5232 (bank5232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5233 := params 16
abbrev ray5233 := rays 16
def bank5233 : Fin 2 → Cell := twoBank p5233 ray5233
theorem signs5233 : ∀ j, Signs p5233 (bank5233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5234 := params 17
abbrev ray5234 := rays 17
def bank5234 : Fin 2 → Cell := twoBank p5234 ray5234
theorem signs5234 : ∀ j, Signs p5234 (bank5234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5235 := params 18
abbrev ray5235 := rays 18
def bank5235 : Fin 2 → Cell := twoBank p5235 ray5235
theorem signs5235 : ∀ j, Signs p5235 (bank5235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5236 := params 19
abbrev ray5236 := rays 19
def bank5236 : Fin 2 → Cell := twoBank p5236 ray5236
theorem signs5236 : ∀ j, Signs p5236 (bank5236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5237 := params 20
abbrev ray5237 := rays 20
def bank5237 : Fin 2 → Cell := twoBank p5237 ray5237
theorem signs5237 : ∀ j, Signs p5237 (bank5237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5238 := params 21
abbrev ray5238 := rays 21
def bank5238 : Fin 2 → Cell := twoBank p5238 ray5238
theorem signs5238 : ∀ j, Signs p5238 (bank5238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5239 := params 22
abbrev ray5239 := rays 22
def bank5239 : Fin 2 → Cell := twoBank p5239 ray5239
theorem signs5239 : ∀ j, Signs p5239 (bank5239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5240 := params 23
abbrev ray5240 := rays 23
def bank5240 : Fin 2 → Cell := twoBank p5240 ray5240
theorem signs5240 : ∀ j, Signs p5240 (bank5240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5241 := params 24
abbrev ray5241 := rays 24
def bank5241 : Fin 2 → Cell := twoBank p5241 ray5241
theorem signs5241 : ∀ j, Signs p5241 (bank5241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5242 := params 25
abbrev ray5242 := rays 25
def bank5242 : Fin 2 → Cell := twoBank p5242 ray5242
theorem signs5242 : ∀ j, Signs p5242 (bank5242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5243 := params 26
abbrev ray5243 := rays 26
def bank5243 : Fin 2 → Cell := twoBank p5243 ray5243
theorem signs5243 : ∀ j, Signs p5243 (bank5243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5244 := params 27
abbrev ray5244 := rays 27
def bank5244 : Fin 2 → Cell := twoBank p5244 ray5244
theorem signs5244 : ∀ j, Signs p5244 (bank5244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5245 := params 28
abbrev ray5245 := rays 28
def bank5245 : Fin 2 → Cell := twoBank p5245 ray5245
theorem signs5245 : ∀ j, Signs p5245 (bank5245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5246 := params 29
abbrev ray5246 := rays 29
def bank5246 : Fin 2 → Cell := twoBank p5246 ray5246
theorem signs5246 : ∀ j, Signs p5246 (bank5246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5247 := params 30
abbrev ray5247 := rays 30
def bank5247 : Fin 2 → Cell := twoBank p5247 ray5247
theorem signs5247 : ∀ j, Signs p5247 (bank5247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5248 := params 31
abbrev ray5248 := rays 31
def bank5248 : Fin 2 → Cell := twoBank p5248 ray5248
theorem signs5248 : ∀ j, Signs p5248 (bank5248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05217_05248
