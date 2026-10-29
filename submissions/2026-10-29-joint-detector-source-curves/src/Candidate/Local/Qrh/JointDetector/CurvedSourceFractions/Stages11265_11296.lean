/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11265_11296
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96990267226446,96989875304818,96989483363502,96989091402498,96988699421807,96988307421429,96987915401365,96987523361615,96987131302179,96986739223059,96986347124254,96985955005765,96985562867593,96985170709738,96984778532200,96984386334980,96983994118079,96983601881497,96983209625234,96982817349291,96982425053668,96982032738366,96981640403385,96981248048726,96980855674389,96980463280375,96980070866684,96979678433317,96979285980274,96978893507555,96978501015162,96978108503094,96977715971352]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11264+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11265 := params 0
abbrev ray11265 := rays 0
def bank11265 : Fin 2 → Cell := twoBank p11265 ray11265
theorem signs11265 : ∀ j, Signs p11265 (bank11265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11266 := params 1
abbrev ray11266 := rays 1
def bank11266 : Fin 2 → Cell := twoBank p11266 ray11266
theorem signs11266 : ∀ j, Signs p11266 (bank11266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11267 := params 2
abbrev ray11267 := rays 2
def bank11267 : Fin 2 → Cell := twoBank p11267 ray11267
theorem signs11267 : ∀ j, Signs p11267 (bank11267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11268 := params 3
abbrev ray11268 := rays 3
def bank11268 : Fin 2 → Cell := twoBank p11268 ray11268
theorem signs11268 : ∀ j, Signs p11268 (bank11268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11269 := params 4
abbrev ray11269 := rays 4
def bank11269 : Fin 2 → Cell := twoBank p11269 ray11269
theorem signs11269 : ∀ j, Signs p11269 (bank11269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11270 := params 5
abbrev ray11270 := rays 5
def bank11270 : Fin 2 → Cell := twoBank p11270 ray11270
theorem signs11270 : ∀ j, Signs p11270 (bank11270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11271 := params 6
abbrev ray11271 := rays 6
def bank11271 : Fin 2 → Cell := twoBank p11271 ray11271
theorem signs11271 : ∀ j, Signs p11271 (bank11271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11272 := params 7
abbrev ray11272 := rays 7
def bank11272 : Fin 2 → Cell := twoBank p11272 ray11272
theorem signs11272 : ∀ j, Signs p11272 (bank11272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11273 := params 8
abbrev ray11273 := rays 8
def bank11273 : Fin 2 → Cell := twoBank p11273 ray11273
theorem signs11273 : ∀ j, Signs p11273 (bank11273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11274 := params 9
abbrev ray11274 := rays 9
def bank11274 : Fin 2 → Cell := twoBank p11274 ray11274
theorem signs11274 : ∀ j, Signs p11274 (bank11274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11275 := params 10
abbrev ray11275 := rays 10
def bank11275 : Fin 2 → Cell := twoBank p11275 ray11275
theorem signs11275 : ∀ j, Signs p11275 (bank11275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11276 := params 11
abbrev ray11276 := rays 11
def bank11276 : Fin 2 → Cell := twoBank p11276 ray11276
theorem signs11276 : ∀ j, Signs p11276 (bank11276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11277 := params 12
abbrev ray11277 := rays 12
def bank11277 : Fin 2 → Cell := twoBank p11277 ray11277
theorem signs11277 : ∀ j, Signs p11277 (bank11277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11278 := params 13
abbrev ray11278 := rays 13
def bank11278 : Fin 2 → Cell := twoBank p11278 ray11278
theorem signs11278 : ∀ j, Signs p11278 (bank11278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11279 := params 14
abbrev ray11279 := rays 14
def bank11279 : Fin 2 → Cell := twoBank p11279 ray11279
theorem signs11279 : ∀ j, Signs p11279 (bank11279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11280 := params 15
abbrev ray11280 := rays 15
def bank11280 : Fin 2 → Cell := twoBank p11280 ray11280
theorem signs11280 : ∀ j, Signs p11280 (bank11280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11281 := params 16
abbrev ray11281 := rays 16
def bank11281 : Fin 2 → Cell := twoBank p11281 ray11281
theorem signs11281 : ∀ j, Signs p11281 (bank11281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11282 := params 17
abbrev ray11282 := rays 17
def bank11282 : Fin 2 → Cell := twoBank p11282 ray11282
theorem signs11282 : ∀ j, Signs p11282 (bank11282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11283 := params 18
abbrev ray11283 := rays 18
def bank11283 : Fin 2 → Cell := twoBank p11283 ray11283
theorem signs11283 : ∀ j, Signs p11283 (bank11283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11284 := params 19
abbrev ray11284 := rays 19
def bank11284 : Fin 2 → Cell := twoBank p11284 ray11284
theorem signs11284 : ∀ j, Signs p11284 (bank11284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11285 := params 20
abbrev ray11285 := rays 20
def bank11285 : Fin 2 → Cell := twoBank p11285 ray11285
theorem signs11285 : ∀ j, Signs p11285 (bank11285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11286 := params 21
abbrev ray11286 := rays 21
def bank11286 : Fin 2 → Cell := twoBank p11286 ray11286
theorem signs11286 : ∀ j, Signs p11286 (bank11286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11287 := params 22
abbrev ray11287 := rays 22
def bank11287 : Fin 2 → Cell := twoBank p11287 ray11287
theorem signs11287 : ∀ j, Signs p11287 (bank11287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11288 := params 23
abbrev ray11288 := rays 23
def bank11288 : Fin 2 → Cell := twoBank p11288 ray11288
theorem signs11288 : ∀ j, Signs p11288 (bank11288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11289 := params 24
abbrev ray11289 := rays 24
def bank11289 : Fin 2 → Cell := twoBank p11289 ray11289
theorem signs11289 : ∀ j, Signs p11289 (bank11289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11290 := params 25
abbrev ray11290 := rays 25
def bank11290 : Fin 2 → Cell := twoBank p11290 ray11290
theorem signs11290 : ∀ j, Signs p11290 (bank11290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11291 := params 26
abbrev ray11291 := rays 26
def bank11291 : Fin 2 → Cell := twoBank p11291 ray11291
theorem signs11291 : ∀ j, Signs p11291 (bank11291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11292 := params 27
abbrev ray11292 := rays 27
def bank11292 : Fin 2 → Cell := twoBank p11292 ray11292
theorem signs11292 : ∀ j, Signs p11292 (bank11292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11293 := params 28
abbrev ray11293 := rays 28
def bank11293 : Fin 2 → Cell := twoBank p11293 ray11293
theorem signs11293 : ∀ j, Signs p11293 (bank11293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11294 := params 29
abbrev ray11294 := rays 29
def bank11294 : Fin 2 → Cell := twoBank p11294 ray11294
theorem signs11294 : ∀ j, Signs p11294 (bank11294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11295 := params 30
abbrev ray11295 := rays 30
def bank11295 : Fin 2 → Cell := twoBank p11295 ray11295
theorem signs11295 : ∀ j, Signs p11295 (bank11295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11296 := params 31
abbrev ray11296 := rays 31
def bank11296 : Fin 2 → Cell := twoBank p11296 ray11296
theorem signs11296 : ∀ j, Signs p11296 (bank11296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11265_11296
