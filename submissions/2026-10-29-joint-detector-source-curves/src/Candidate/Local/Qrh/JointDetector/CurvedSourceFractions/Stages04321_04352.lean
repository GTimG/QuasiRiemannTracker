/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04321_04352
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99203964377585,99203724553358,99203484704323,99203244830480,99203004931831,99202765008377,99202525060119,99202285087058,99202045089195,99201805066531,99201565019067,99201324946804,99201084849744,99200844727887,99200604581235,99200364409788,99200124213548,99199883992516,99199643746693,99199403476079,99199163180676,99198922860486,99198682515509,99198442145746,99198201751198,99197961331867,99197720887753,99197480418858,99197239925182,99196999406727,99196758863494,99196518295484,99196277702698]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4320+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4321 := params 0
abbrev ray4321 := rays 0
def bank4321 : Fin 2 → Cell := twoBank p4321 ray4321
theorem signs4321 : ∀ j, Signs p4321 (bank4321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4322 := params 1
abbrev ray4322 := rays 1
def bank4322 : Fin 2 → Cell := twoBank p4322 ray4322
theorem signs4322 : ∀ j, Signs p4322 (bank4322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4323 := params 2
abbrev ray4323 := rays 2
def bank4323 : Fin 2 → Cell := twoBank p4323 ray4323
theorem signs4323 : ∀ j, Signs p4323 (bank4323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4324 := params 3
abbrev ray4324 := rays 3
def bank4324 : Fin 2 → Cell := twoBank p4324 ray4324
theorem signs4324 : ∀ j, Signs p4324 (bank4324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4325 := params 4
abbrev ray4325 := rays 4
def bank4325 : Fin 2 → Cell := twoBank p4325 ray4325
theorem signs4325 : ∀ j, Signs p4325 (bank4325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4326 := params 5
abbrev ray4326 := rays 5
def bank4326 : Fin 2 → Cell := twoBank p4326 ray4326
theorem signs4326 : ∀ j, Signs p4326 (bank4326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4327 := params 6
abbrev ray4327 := rays 6
def bank4327 : Fin 2 → Cell := twoBank p4327 ray4327
theorem signs4327 : ∀ j, Signs p4327 (bank4327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4328 := params 7
abbrev ray4328 := rays 7
def bank4328 : Fin 2 → Cell := twoBank p4328 ray4328
theorem signs4328 : ∀ j, Signs p4328 (bank4328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4329 := params 8
abbrev ray4329 := rays 8
def bank4329 : Fin 2 → Cell := twoBank p4329 ray4329
theorem signs4329 : ∀ j, Signs p4329 (bank4329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4330 := params 9
abbrev ray4330 := rays 9
def bank4330 : Fin 2 → Cell := twoBank p4330 ray4330
theorem signs4330 : ∀ j, Signs p4330 (bank4330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4331 := params 10
abbrev ray4331 := rays 10
def bank4331 : Fin 2 → Cell := twoBank p4331 ray4331
theorem signs4331 : ∀ j, Signs p4331 (bank4331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4332 := params 11
abbrev ray4332 := rays 11
def bank4332 : Fin 2 → Cell := twoBank p4332 ray4332
theorem signs4332 : ∀ j, Signs p4332 (bank4332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4333 := params 12
abbrev ray4333 := rays 12
def bank4333 : Fin 2 → Cell := twoBank p4333 ray4333
theorem signs4333 : ∀ j, Signs p4333 (bank4333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4334 := params 13
abbrev ray4334 := rays 13
def bank4334 : Fin 2 → Cell := twoBank p4334 ray4334
theorem signs4334 : ∀ j, Signs p4334 (bank4334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4335 := params 14
abbrev ray4335 := rays 14
def bank4335 : Fin 2 → Cell := twoBank p4335 ray4335
theorem signs4335 : ∀ j, Signs p4335 (bank4335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4336 := params 15
abbrev ray4336 := rays 15
def bank4336 : Fin 2 → Cell := twoBank p4336 ray4336
theorem signs4336 : ∀ j, Signs p4336 (bank4336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4337 := params 16
abbrev ray4337 := rays 16
def bank4337 : Fin 2 → Cell := twoBank p4337 ray4337
theorem signs4337 : ∀ j, Signs p4337 (bank4337 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4338 := params 17
abbrev ray4338 := rays 17
def bank4338 : Fin 2 → Cell := twoBank p4338 ray4338
theorem signs4338 : ∀ j, Signs p4338 (bank4338 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4339 := params 18
abbrev ray4339 := rays 18
def bank4339 : Fin 2 → Cell := twoBank p4339 ray4339
theorem signs4339 : ∀ j, Signs p4339 (bank4339 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4340 := params 19
abbrev ray4340 := rays 19
def bank4340 : Fin 2 → Cell := twoBank p4340 ray4340
theorem signs4340 : ∀ j, Signs p4340 (bank4340 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4341 := params 20
abbrev ray4341 := rays 20
def bank4341 : Fin 2 → Cell := twoBank p4341 ray4341
theorem signs4341 : ∀ j, Signs p4341 (bank4341 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4342 := params 21
abbrev ray4342 := rays 21
def bank4342 : Fin 2 → Cell := twoBank p4342 ray4342
theorem signs4342 : ∀ j, Signs p4342 (bank4342 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4343 := params 22
abbrev ray4343 := rays 22
def bank4343 : Fin 2 → Cell := twoBank p4343 ray4343
theorem signs4343 : ∀ j, Signs p4343 (bank4343 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4344 := params 23
abbrev ray4344 := rays 23
def bank4344 : Fin 2 → Cell := twoBank p4344 ray4344
theorem signs4344 : ∀ j, Signs p4344 (bank4344 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4345 := params 24
abbrev ray4345 := rays 24
def bank4345 : Fin 2 → Cell := twoBank p4345 ray4345
theorem signs4345 : ∀ j, Signs p4345 (bank4345 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4346 := params 25
abbrev ray4346 := rays 25
def bank4346 : Fin 2 → Cell := twoBank p4346 ray4346
theorem signs4346 : ∀ j, Signs p4346 (bank4346 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4347 := params 26
abbrev ray4347 := rays 26
def bank4347 : Fin 2 → Cell := twoBank p4347 ray4347
theorem signs4347 : ∀ j, Signs p4347 (bank4347 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4348 := params 27
abbrev ray4348 := rays 27
def bank4348 : Fin 2 → Cell := twoBank p4348 ray4348
theorem signs4348 : ∀ j, Signs p4348 (bank4348 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4349 := params 28
abbrev ray4349 := rays 28
def bank4349 : Fin 2 → Cell := twoBank p4349 ray4349
theorem signs4349 : ∀ j, Signs p4349 (bank4349 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4350 := params 29
abbrev ray4350 := rays 29
def bank4350 : Fin 2 → Cell := twoBank p4350 ray4350
theorem signs4350 : ∀ j, Signs p4350 (bank4350 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4351 := params 30
abbrev ray4351 := rays 30
def bank4351 : Fin 2 → Cell := twoBank p4351 ray4351
theorem signs4351 : ∀ j, Signs p4351 (bank4351 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4352 := params 31
abbrev ray4352 := rays 31
def bank4352 : Fin 2 → Cell := twoBank p4352 ray4352
theorem signs4352 : ∀ j, Signs p4352 (bank4352 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04321_04352
