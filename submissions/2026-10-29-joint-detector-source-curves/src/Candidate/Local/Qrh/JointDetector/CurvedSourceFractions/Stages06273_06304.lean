/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06273_06304
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98689851575125,98689565232417,98689278866783,98688992478224,98688706066741,98688419632335,98688133175006,98687846694755,98687560191583,98687273665491,98686987116480,98686700544551,98686413949704,98686127331941,98685840691262,98685554027668,98685267341160,98684980631739,98684693899406,98684407144161,98684120366006,98683833564941,98683546740967,98683259894085,98682973024296,98682686131600,98682399215999,98682112277493,98681825316084,98681538331772,98681251324558,98680964294442,98680677241426]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6272+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6273 := params 0
abbrev ray6273 := rays 0
def bank6273 : Fin 2 → Cell := twoBank p6273 ray6273
theorem signs6273 : ∀ j, Signs p6273 (bank6273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6274 := params 1
abbrev ray6274 := rays 1
def bank6274 : Fin 2 → Cell := twoBank p6274 ray6274
theorem signs6274 : ∀ j, Signs p6274 (bank6274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6275 := params 2
abbrev ray6275 := rays 2
def bank6275 : Fin 2 → Cell := twoBank p6275 ray6275
theorem signs6275 : ∀ j, Signs p6275 (bank6275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6276 := params 3
abbrev ray6276 := rays 3
def bank6276 : Fin 2 → Cell := twoBank p6276 ray6276
theorem signs6276 : ∀ j, Signs p6276 (bank6276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6277 := params 4
abbrev ray6277 := rays 4
def bank6277 : Fin 2 → Cell := twoBank p6277 ray6277
theorem signs6277 : ∀ j, Signs p6277 (bank6277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6278 := params 5
abbrev ray6278 := rays 5
def bank6278 : Fin 2 → Cell := twoBank p6278 ray6278
theorem signs6278 : ∀ j, Signs p6278 (bank6278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6279 := params 6
abbrev ray6279 := rays 6
def bank6279 : Fin 2 → Cell := twoBank p6279 ray6279
theorem signs6279 : ∀ j, Signs p6279 (bank6279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6280 := params 7
abbrev ray6280 := rays 7
def bank6280 : Fin 2 → Cell := twoBank p6280 ray6280
theorem signs6280 : ∀ j, Signs p6280 (bank6280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6281 := params 8
abbrev ray6281 := rays 8
def bank6281 : Fin 2 → Cell := twoBank p6281 ray6281
theorem signs6281 : ∀ j, Signs p6281 (bank6281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6282 := params 9
abbrev ray6282 := rays 9
def bank6282 : Fin 2 → Cell := twoBank p6282 ray6282
theorem signs6282 : ∀ j, Signs p6282 (bank6282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6283 := params 10
abbrev ray6283 := rays 10
def bank6283 : Fin 2 → Cell := twoBank p6283 ray6283
theorem signs6283 : ∀ j, Signs p6283 (bank6283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6284 := params 11
abbrev ray6284 := rays 11
def bank6284 : Fin 2 → Cell := twoBank p6284 ray6284
theorem signs6284 : ∀ j, Signs p6284 (bank6284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6285 := params 12
abbrev ray6285 := rays 12
def bank6285 : Fin 2 → Cell := twoBank p6285 ray6285
theorem signs6285 : ∀ j, Signs p6285 (bank6285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6286 := params 13
abbrev ray6286 := rays 13
def bank6286 : Fin 2 → Cell := twoBank p6286 ray6286
theorem signs6286 : ∀ j, Signs p6286 (bank6286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6287 := params 14
abbrev ray6287 := rays 14
def bank6287 : Fin 2 → Cell := twoBank p6287 ray6287
theorem signs6287 : ∀ j, Signs p6287 (bank6287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6288 := params 15
abbrev ray6288 := rays 15
def bank6288 : Fin 2 → Cell := twoBank p6288 ray6288
theorem signs6288 : ∀ j, Signs p6288 (bank6288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6289 := params 16
abbrev ray6289 := rays 16
def bank6289 : Fin 2 → Cell := twoBank p6289 ray6289
theorem signs6289 : ∀ j, Signs p6289 (bank6289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6290 := params 17
abbrev ray6290 := rays 17
def bank6290 : Fin 2 → Cell := twoBank p6290 ray6290
theorem signs6290 : ∀ j, Signs p6290 (bank6290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6291 := params 18
abbrev ray6291 := rays 18
def bank6291 : Fin 2 → Cell := twoBank p6291 ray6291
theorem signs6291 : ∀ j, Signs p6291 (bank6291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6292 := params 19
abbrev ray6292 := rays 19
def bank6292 : Fin 2 → Cell := twoBank p6292 ray6292
theorem signs6292 : ∀ j, Signs p6292 (bank6292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6293 := params 20
abbrev ray6293 := rays 20
def bank6293 : Fin 2 → Cell := twoBank p6293 ray6293
theorem signs6293 : ∀ j, Signs p6293 (bank6293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6294 := params 21
abbrev ray6294 := rays 21
def bank6294 : Fin 2 → Cell := twoBank p6294 ray6294
theorem signs6294 : ∀ j, Signs p6294 (bank6294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6295 := params 22
abbrev ray6295 := rays 22
def bank6295 : Fin 2 → Cell := twoBank p6295 ray6295
theorem signs6295 : ∀ j, Signs p6295 (bank6295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6296 := params 23
abbrev ray6296 := rays 23
def bank6296 : Fin 2 → Cell := twoBank p6296 ray6296
theorem signs6296 : ∀ j, Signs p6296 (bank6296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6297 := params 24
abbrev ray6297 := rays 24
def bank6297 : Fin 2 → Cell := twoBank p6297 ray6297
theorem signs6297 : ∀ j, Signs p6297 (bank6297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6298 := params 25
abbrev ray6298 := rays 25
def bank6298 : Fin 2 → Cell := twoBank p6298 ray6298
theorem signs6298 : ∀ j, Signs p6298 (bank6298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6299 := params 26
abbrev ray6299 := rays 26
def bank6299 : Fin 2 → Cell := twoBank p6299 ray6299
theorem signs6299 : ∀ j, Signs p6299 (bank6299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6300 := params 27
abbrev ray6300 := rays 27
def bank6300 : Fin 2 → Cell := twoBank p6300 ray6300
theorem signs6300 : ∀ j, Signs p6300 (bank6300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6301 := params 28
abbrev ray6301 := rays 28
def bank6301 : Fin 2 → Cell := twoBank p6301 ray6301
theorem signs6301 : ∀ j, Signs p6301 (bank6301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6302 := params 29
abbrev ray6302 := rays 29
def bank6302 : Fin 2 → Cell := twoBank p6302 ray6302
theorem signs6302 : ∀ j, Signs p6302 (bank6302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6303 := params 30
abbrev ray6303 := rays 30
def bank6303 : Fin 2 → Cell := twoBank p6303 ray6303
theorem signs6303 : ∀ j, Signs p6303 (bank6303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6304 := params 31
abbrev ray6304 := rays 31
def bank6304 : Fin 2 → Cell := twoBank p6304 ray6304
theorem signs6304 : ∀ j, Signs p6304 (bank6304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06273_06304
