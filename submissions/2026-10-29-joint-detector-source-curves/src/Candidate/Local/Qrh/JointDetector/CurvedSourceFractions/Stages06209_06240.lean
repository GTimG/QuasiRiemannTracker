/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06209_06240
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98708129783003,98707844909347,98707560012710,98707275093093,98706990150497,98706705184922,98706420196370,98706135184841,98705850150336,98705565092856,98705280012402,98704994908975,98704709782575,98704424633204,98704139460862,98703854265550,98703569047269,98703283806020,98702998541804,98702713254621,98702427944473,98702142611360,98701857255283,98701571876243,98701286474241,98701001049278,98700715601355,98700430130472,98700144636630,98699859119831,98699573580075,98699288017363,98699002431695]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6208+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6209 := params 0
abbrev ray6209 := rays 0
def bank6209 : Fin 2 → Cell := twoBank p6209 ray6209
theorem signs6209 : ∀ j, Signs p6209 (bank6209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6210 := params 1
abbrev ray6210 := rays 1
def bank6210 : Fin 2 → Cell := twoBank p6210 ray6210
theorem signs6210 : ∀ j, Signs p6210 (bank6210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6211 := params 2
abbrev ray6211 := rays 2
def bank6211 : Fin 2 → Cell := twoBank p6211 ray6211
theorem signs6211 : ∀ j, Signs p6211 (bank6211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6212 := params 3
abbrev ray6212 := rays 3
def bank6212 : Fin 2 → Cell := twoBank p6212 ray6212
theorem signs6212 : ∀ j, Signs p6212 (bank6212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6213 := params 4
abbrev ray6213 := rays 4
def bank6213 : Fin 2 → Cell := twoBank p6213 ray6213
theorem signs6213 : ∀ j, Signs p6213 (bank6213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6214 := params 5
abbrev ray6214 := rays 5
def bank6214 : Fin 2 → Cell := twoBank p6214 ray6214
theorem signs6214 : ∀ j, Signs p6214 (bank6214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6215 := params 6
abbrev ray6215 := rays 6
def bank6215 : Fin 2 → Cell := twoBank p6215 ray6215
theorem signs6215 : ∀ j, Signs p6215 (bank6215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6216 := params 7
abbrev ray6216 := rays 7
def bank6216 : Fin 2 → Cell := twoBank p6216 ray6216
theorem signs6216 : ∀ j, Signs p6216 (bank6216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6217 := params 8
abbrev ray6217 := rays 8
def bank6217 : Fin 2 → Cell := twoBank p6217 ray6217
theorem signs6217 : ∀ j, Signs p6217 (bank6217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6218 := params 9
abbrev ray6218 := rays 9
def bank6218 : Fin 2 → Cell := twoBank p6218 ray6218
theorem signs6218 : ∀ j, Signs p6218 (bank6218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6219 := params 10
abbrev ray6219 := rays 10
def bank6219 : Fin 2 → Cell := twoBank p6219 ray6219
theorem signs6219 : ∀ j, Signs p6219 (bank6219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6220 := params 11
abbrev ray6220 := rays 11
def bank6220 : Fin 2 → Cell := twoBank p6220 ray6220
theorem signs6220 : ∀ j, Signs p6220 (bank6220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6221 := params 12
abbrev ray6221 := rays 12
def bank6221 : Fin 2 → Cell := twoBank p6221 ray6221
theorem signs6221 : ∀ j, Signs p6221 (bank6221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6222 := params 13
abbrev ray6222 := rays 13
def bank6222 : Fin 2 → Cell := twoBank p6222 ray6222
theorem signs6222 : ∀ j, Signs p6222 (bank6222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6223 := params 14
abbrev ray6223 := rays 14
def bank6223 : Fin 2 → Cell := twoBank p6223 ray6223
theorem signs6223 : ∀ j, Signs p6223 (bank6223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6224 := params 15
abbrev ray6224 := rays 15
def bank6224 : Fin 2 → Cell := twoBank p6224 ray6224
theorem signs6224 : ∀ j, Signs p6224 (bank6224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6225 := params 16
abbrev ray6225 := rays 16
def bank6225 : Fin 2 → Cell := twoBank p6225 ray6225
theorem signs6225 : ∀ j, Signs p6225 (bank6225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6226 := params 17
abbrev ray6226 := rays 17
def bank6226 : Fin 2 → Cell := twoBank p6226 ray6226
theorem signs6226 : ∀ j, Signs p6226 (bank6226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6227 := params 18
abbrev ray6227 := rays 18
def bank6227 : Fin 2 → Cell := twoBank p6227 ray6227
theorem signs6227 : ∀ j, Signs p6227 (bank6227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6228 := params 19
abbrev ray6228 := rays 19
def bank6228 : Fin 2 → Cell := twoBank p6228 ray6228
theorem signs6228 : ∀ j, Signs p6228 (bank6228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6229 := params 20
abbrev ray6229 := rays 20
def bank6229 : Fin 2 → Cell := twoBank p6229 ray6229
theorem signs6229 : ∀ j, Signs p6229 (bank6229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6230 := params 21
abbrev ray6230 := rays 21
def bank6230 : Fin 2 → Cell := twoBank p6230 ray6230
theorem signs6230 : ∀ j, Signs p6230 (bank6230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6231 := params 22
abbrev ray6231 := rays 22
def bank6231 : Fin 2 → Cell := twoBank p6231 ray6231
theorem signs6231 : ∀ j, Signs p6231 (bank6231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6232 := params 23
abbrev ray6232 := rays 23
def bank6232 : Fin 2 → Cell := twoBank p6232 ray6232
theorem signs6232 : ∀ j, Signs p6232 (bank6232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6233 := params 24
abbrev ray6233 := rays 24
def bank6233 : Fin 2 → Cell := twoBank p6233 ray6233
theorem signs6233 : ∀ j, Signs p6233 (bank6233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6234 := params 25
abbrev ray6234 := rays 25
def bank6234 : Fin 2 → Cell := twoBank p6234 ray6234
theorem signs6234 : ∀ j, Signs p6234 (bank6234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6235 := params 26
abbrev ray6235 := rays 26
def bank6235 : Fin 2 → Cell := twoBank p6235 ray6235
theorem signs6235 : ∀ j, Signs p6235 (bank6235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6236 := params 27
abbrev ray6236 := rays 27
def bank6236 : Fin 2 → Cell := twoBank p6236 ray6236
theorem signs6236 : ∀ j, Signs p6236 (bank6236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6237 := params 28
abbrev ray6237 := rays 28
def bank6237 : Fin 2 → Cell := twoBank p6237 ray6237
theorem signs6237 : ∀ j, Signs p6237 (bank6237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6238 := params 29
abbrev ray6238 := rays 29
def bank6238 : Fin 2 → Cell := twoBank p6238 ray6238
theorem signs6238 : ∀ j, Signs p6238 (bank6238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6239 := params 30
abbrev ray6239 := rays 30
def bank6239 : Fin 2 → Cell := twoBank p6239 ray6239
theorem signs6239 : ∀ j, Signs p6239 (bank6239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6240 := params 31
abbrev ray6240 := rays 31
def bank6240 : Fin 2 → Cell := twoBank p6240 ray6240
theorem signs6240 : ∀ j, Signs p6240 (bank6240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06209_06240
