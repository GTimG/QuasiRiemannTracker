/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06305_06336
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98680677241426,98680390165510,98680103066696,98679815944984,98679528800375,98679241632870,98678954442470,98678667229175,98678379992987,98678092733906,98677805451933,98677518147069,98677230819315,98676943468672,98676656095141,98676368698722,98676081279416,98675793837225,98675506372149,98675218884188,98674931373344,98674643839618,98674356283010,98674068703521,98673781101152,98673493475904,98673205827778,98672918156775,98672630462895,98672342746140,98672055006510,98671767244006,98671479458629]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6304+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6305 := params 0
abbrev ray6305 := rays 0
def bank6305 : Fin 2 → Cell := twoBank p6305 ray6305
theorem signs6305 : ∀ j, Signs p6305 (bank6305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6306 := params 1
abbrev ray6306 := rays 1
def bank6306 : Fin 2 → Cell := twoBank p6306 ray6306
theorem signs6306 : ∀ j, Signs p6306 (bank6306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6307 := params 2
abbrev ray6307 := rays 2
def bank6307 : Fin 2 → Cell := twoBank p6307 ray6307
theorem signs6307 : ∀ j, Signs p6307 (bank6307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6308 := params 3
abbrev ray6308 := rays 3
def bank6308 : Fin 2 → Cell := twoBank p6308 ray6308
theorem signs6308 : ∀ j, Signs p6308 (bank6308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6309 := params 4
abbrev ray6309 := rays 4
def bank6309 : Fin 2 → Cell := twoBank p6309 ray6309
theorem signs6309 : ∀ j, Signs p6309 (bank6309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6310 := params 5
abbrev ray6310 := rays 5
def bank6310 : Fin 2 → Cell := twoBank p6310 ray6310
theorem signs6310 : ∀ j, Signs p6310 (bank6310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6311 := params 6
abbrev ray6311 := rays 6
def bank6311 : Fin 2 → Cell := twoBank p6311 ray6311
theorem signs6311 : ∀ j, Signs p6311 (bank6311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6312 := params 7
abbrev ray6312 := rays 7
def bank6312 : Fin 2 → Cell := twoBank p6312 ray6312
theorem signs6312 : ∀ j, Signs p6312 (bank6312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6313 := params 8
abbrev ray6313 := rays 8
def bank6313 : Fin 2 → Cell := twoBank p6313 ray6313
theorem signs6313 : ∀ j, Signs p6313 (bank6313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6314 := params 9
abbrev ray6314 := rays 9
def bank6314 : Fin 2 → Cell := twoBank p6314 ray6314
theorem signs6314 : ∀ j, Signs p6314 (bank6314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6315 := params 10
abbrev ray6315 := rays 10
def bank6315 : Fin 2 → Cell := twoBank p6315 ray6315
theorem signs6315 : ∀ j, Signs p6315 (bank6315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6316 := params 11
abbrev ray6316 := rays 11
def bank6316 : Fin 2 → Cell := twoBank p6316 ray6316
theorem signs6316 : ∀ j, Signs p6316 (bank6316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6317 := params 12
abbrev ray6317 := rays 12
def bank6317 : Fin 2 → Cell := twoBank p6317 ray6317
theorem signs6317 : ∀ j, Signs p6317 (bank6317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6318 := params 13
abbrev ray6318 := rays 13
def bank6318 : Fin 2 → Cell := twoBank p6318 ray6318
theorem signs6318 : ∀ j, Signs p6318 (bank6318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6319 := params 14
abbrev ray6319 := rays 14
def bank6319 : Fin 2 → Cell := twoBank p6319 ray6319
theorem signs6319 : ∀ j, Signs p6319 (bank6319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6320 := params 15
abbrev ray6320 := rays 15
def bank6320 : Fin 2 → Cell := twoBank p6320 ray6320
theorem signs6320 : ∀ j, Signs p6320 (bank6320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6321 := params 16
abbrev ray6321 := rays 16
def bank6321 : Fin 2 → Cell := twoBank p6321 ray6321
theorem signs6321 : ∀ j, Signs p6321 (bank6321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6322 := params 17
abbrev ray6322 := rays 17
def bank6322 : Fin 2 → Cell := twoBank p6322 ray6322
theorem signs6322 : ∀ j, Signs p6322 (bank6322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6323 := params 18
abbrev ray6323 := rays 18
def bank6323 : Fin 2 → Cell := twoBank p6323 ray6323
theorem signs6323 : ∀ j, Signs p6323 (bank6323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6324 := params 19
abbrev ray6324 := rays 19
def bank6324 : Fin 2 → Cell := twoBank p6324 ray6324
theorem signs6324 : ∀ j, Signs p6324 (bank6324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6325 := params 20
abbrev ray6325 := rays 20
def bank6325 : Fin 2 → Cell := twoBank p6325 ray6325
theorem signs6325 : ∀ j, Signs p6325 (bank6325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6326 := params 21
abbrev ray6326 := rays 21
def bank6326 : Fin 2 → Cell := twoBank p6326 ray6326
theorem signs6326 : ∀ j, Signs p6326 (bank6326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6327 := params 22
abbrev ray6327 := rays 22
def bank6327 : Fin 2 → Cell := twoBank p6327 ray6327
theorem signs6327 : ∀ j, Signs p6327 (bank6327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6328 := params 23
abbrev ray6328 := rays 23
def bank6328 : Fin 2 → Cell := twoBank p6328 ray6328
theorem signs6328 : ∀ j, Signs p6328 (bank6328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6329 := params 24
abbrev ray6329 := rays 24
def bank6329 : Fin 2 → Cell := twoBank p6329 ray6329
theorem signs6329 : ∀ j, Signs p6329 (bank6329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6330 := params 25
abbrev ray6330 := rays 25
def bank6330 : Fin 2 → Cell := twoBank p6330 ray6330
theorem signs6330 : ∀ j, Signs p6330 (bank6330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6331 := params 26
abbrev ray6331 := rays 26
def bank6331 : Fin 2 → Cell := twoBank p6331 ray6331
theorem signs6331 : ∀ j, Signs p6331 (bank6331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6332 := params 27
abbrev ray6332 := rays 27
def bank6332 : Fin 2 → Cell := twoBank p6332 ray6332
theorem signs6332 : ∀ j, Signs p6332 (bank6332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6333 := params 28
abbrev ray6333 := rays 28
def bank6333 : Fin 2 → Cell := twoBank p6333 ray6333
theorem signs6333 : ∀ j, Signs p6333 (bank6333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6334 := params 29
abbrev ray6334 := rays 29
def bank6334 : Fin 2 → Cell := twoBank p6334 ray6334
theorem signs6334 : ∀ j, Signs p6334 (bank6334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6335 := params 30
abbrev ray6335 := rays 30
def bank6335 : Fin 2 → Cell := twoBank p6335 ray6335
theorem signs6335 : ∀ j, Signs p6335 (bank6335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6336 := params 31
abbrev ray6336 := rays 31
def bank6336 : Fin 2 → Cell := twoBank p6336 ray6336
theorem signs6336 : ∀ j, Signs p6336 (bank6336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06305_06336
