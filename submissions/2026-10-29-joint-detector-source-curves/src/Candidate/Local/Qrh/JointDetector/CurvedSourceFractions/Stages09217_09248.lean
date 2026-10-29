/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09217_09248
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97750888389262,97750537872907,97750187335760,97749836777822,97749486199094,97749135599576,97748784979269,97748434338174,97748083676291,97747732993621,97747382290164,97747031565921,97746680820892,97746330055079,97745979268481,97745628461100,97745277632936,97744926783989,97744575914261,97744225023751,97743874112461,97743523180391,97743172227541,97742821253913,97742470259506,97742119244322,97741768208361,97741417151624,97741066074111,97740714975823,97740363856760,97740012716923,97739661556313]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9216+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9217 := params 0
abbrev ray9217 := rays 0
def bank9217 : Fin 2 → Cell := twoBank p9217 ray9217
theorem signs9217 : ∀ j, Signs p9217 (bank9217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9218 := params 1
abbrev ray9218 := rays 1
def bank9218 : Fin 2 → Cell := twoBank p9218 ray9218
theorem signs9218 : ∀ j, Signs p9218 (bank9218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9219 := params 2
abbrev ray9219 := rays 2
def bank9219 : Fin 2 → Cell := twoBank p9219 ray9219
theorem signs9219 : ∀ j, Signs p9219 (bank9219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9220 := params 3
abbrev ray9220 := rays 3
def bank9220 : Fin 2 → Cell := twoBank p9220 ray9220
theorem signs9220 : ∀ j, Signs p9220 (bank9220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9221 := params 4
abbrev ray9221 := rays 4
def bank9221 : Fin 2 → Cell := twoBank p9221 ray9221
theorem signs9221 : ∀ j, Signs p9221 (bank9221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9222 := params 5
abbrev ray9222 := rays 5
def bank9222 : Fin 2 → Cell := twoBank p9222 ray9222
theorem signs9222 : ∀ j, Signs p9222 (bank9222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9223 := params 6
abbrev ray9223 := rays 6
def bank9223 : Fin 2 → Cell := twoBank p9223 ray9223
theorem signs9223 : ∀ j, Signs p9223 (bank9223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9224 := params 7
abbrev ray9224 := rays 7
def bank9224 : Fin 2 → Cell := twoBank p9224 ray9224
theorem signs9224 : ∀ j, Signs p9224 (bank9224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9225 := params 8
abbrev ray9225 := rays 8
def bank9225 : Fin 2 → Cell := twoBank p9225 ray9225
theorem signs9225 : ∀ j, Signs p9225 (bank9225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9226 := params 9
abbrev ray9226 := rays 9
def bank9226 : Fin 2 → Cell := twoBank p9226 ray9226
theorem signs9226 : ∀ j, Signs p9226 (bank9226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9227 := params 10
abbrev ray9227 := rays 10
def bank9227 : Fin 2 → Cell := twoBank p9227 ray9227
theorem signs9227 : ∀ j, Signs p9227 (bank9227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9228 := params 11
abbrev ray9228 := rays 11
def bank9228 : Fin 2 → Cell := twoBank p9228 ray9228
theorem signs9228 : ∀ j, Signs p9228 (bank9228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9229 := params 12
abbrev ray9229 := rays 12
def bank9229 : Fin 2 → Cell := twoBank p9229 ray9229
theorem signs9229 : ∀ j, Signs p9229 (bank9229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9230 := params 13
abbrev ray9230 := rays 13
def bank9230 : Fin 2 → Cell := twoBank p9230 ray9230
theorem signs9230 : ∀ j, Signs p9230 (bank9230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9231 := params 14
abbrev ray9231 := rays 14
def bank9231 : Fin 2 → Cell := twoBank p9231 ray9231
theorem signs9231 : ∀ j, Signs p9231 (bank9231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9232 := params 15
abbrev ray9232 := rays 15
def bank9232 : Fin 2 → Cell := twoBank p9232 ray9232
theorem signs9232 : ∀ j, Signs p9232 (bank9232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9233 := params 16
abbrev ray9233 := rays 16
def bank9233 : Fin 2 → Cell := twoBank p9233 ray9233
theorem signs9233 : ∀ j, Signs p9233 (bank9233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9234 := params 17
abbrev ray9234 := rays 17
def bank9234 : Fin 2 → Cell := twoBank p9234 ray9234
theorem signs9234 : ∀ j, Signs p9234 (bank9234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9235 := params 18
abbrev ray9235 := rays 18
def bank9235 : Fin 2 → Cell := twoBank p9235 ray9235
theorem signs9235 : ∀ j, Signs p9235 (bank9235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9236 := params 19
abbrev ray9236 := rays 19
def bank9236 : Fin 2 → Cell := twoBank p9236 ray9236
theorem signs9236 : ∀ j, Signs p9236 (bank9236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9237 := params 20
abbrev ray9237 := rays 20
def bank9237 : Fin 2 → Cell := twoBank p9237 ray9237
theorem signs9237 : ∀ j, Signs p9237 (bank9237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9238 := params 21
abbrev ray9238 := rays 21
def bank9238 : Fin 2 → Cell := twoBank p9238 ray9238
theorem signs9238 : ∀ j, Signs p9238 (bank9238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9239 := params 22
abbrev ray9239 := rays 22
def bank9239 : Fin 2 → Cell := twoBank p9239 ray9239
theorem signs9239 : ∀ j, Signs p9239 (bank9239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9240 := params 23
abbrev ray9240 := rays 23
def bank9240 : Fin 2 → Cell := twoBank p9240 ray9240
theorem signs9240 : ∀ j, Signs p9240 (bank9240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9241 := params 24
abbrev ray9241 := rays 24
def bank9241 : Fin 2 → Cell := twoBank p9241 ray9241
theorem signs9241 : ∀ j, Signs p9241 (bank9241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9242 := params 25
abbrev ray9242 := rays 25
def bank9242 : Fin 2 → Cell := twoBank p9242 ray9242
theorem signs9242 : ∀ j, Signs p9242 (bank9242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9243 := params 26
abbrev ray9243 := rays 26
def bank9243 : Fin 2 → Cell := twoBank p9243 ray9243
theorem signs9243 : ∀ j, Signs p9243 (bank9243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9244 := params 27
abbrev ray9244 := rays 27
def bank9244 : Fin 2 → Cell := twoBank p9244 ray9244
theorem signs9244 : ∀ j, Signs p9244 (bank9244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9245 := params 28
abbrev ray9245 := rays 28
def bank9245 : Fin 2 → Cell := twoBank p9245 ray9245
theorem signs9245 : ∀ j, Signs p9245 (bank9245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9246 := params 29
abbrev ray9246 := rays 29
def bank9246 : Fin 2 → Cell := twoBank p9246 ray9246
theorem signs9246 : ∀ j, Signs p9246 (bank9246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9247 := params 30
abbrev ray9247 := rays 30
def bank9247 : Fin 2 → Cell := twoBank p9247 ray9247
theorem signs9247 : ∀ j, Signs p9247 (bank9247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9248 := params 31
abbrev ray9248 := rays 31
def bank9248 : Fin 2 → Cell := twoBank p9248 ray9248
theorem signs9248 : ∀ j, Signs p9248 (bank9248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09217_09248
