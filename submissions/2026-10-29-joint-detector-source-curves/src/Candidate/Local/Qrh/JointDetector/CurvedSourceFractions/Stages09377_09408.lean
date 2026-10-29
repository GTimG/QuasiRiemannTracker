/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09377_09408
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97694541709339,97694187874019,97693834018004,97693480141294,97693126243890,97692772325793,97692418387003,97692064427520,97691710447346,97691356446481,97691002424925,97690648382679,97690294319744,97689940236120,97689586131808,97689232006809,97688877861123,97688523694751,97688169507693,97687815299950,97687461071522,97687106822410,97686752552615,97686398262137,97686043950977,97685689619135,97685335266613,97684980893410,97684626499527,97684272084965,97683917649725,97683563193807,97683208717211]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9376+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9377 := params 0
abbrev ray9377 := rays 0
def bank9377 : Fin 2 → Cell := twoBank p9377 ray9377
theorem signs9377 : ∀ j, Signs p9377 (bank9377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9378 := params 1
abbrev ray9378 := rays 1
def bank9378 : Fin 2 → Cell := twoBank p9378 ray9378
theorem signs9378 : ∀ j, Signs p9378 (bank9378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9379 := params 2
abbrev ray9379 := rays 2
def bank9379 : Fin 2 → Cell := twoBank p9379 ray9379
theorem signs9379 : ∀ j, Signs p9379 (bank9379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9380 := params 3
abbrev ray9380 := rays 3
def bank9380 : Fin 2 → Cell := twoBank p9380 ray9380
theorem signs9380 : ∀ j, Signs p9380 (bank9380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9381 := params 4
abbrev ray9381 := rays 4
def bank9381 : Fin 2 → Cell := twoBank p9381 ray9381
theorem signs9381 : ∀ j, Signs p9381 (bank9381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9382 := params 5
abbrev ray9382 := rays 5
def bank9382 : Fin 2 → Cell := twoBank p9382 ray9382
theorem signs9382 : ∀ j, Signs p9382 (bank9382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9383 := params 6
abbrev ray9383 := rays 6
def bank9383 : Fin 2 → Cell := twoBank p9383 ray9383
theorem signs9383 : ∀ j, Signs p9383 (bank9383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9384 := params 7
abbrev ray9384 := rays 7
def bank9384 : Fin 2 → Cell := twoBank p9384 ray9384
theorem signs9384 : ∀ j, Signs p9384 (bank9384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9385 := params 8
abbrev ray9385 := rays 8
def bank9385 : Fin 2 → Cell := twoBank p9385 ray9385
theorem signs9385 : ∀ j, Signs p9385 (bank9385 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9386 := params 9
abbrev ray9386 := rays 9
def bank9386 : Fin 2 → Cell := twoBank p9386 ray9386
theorem signs9386 : ∀ j, Signs p9386 (bank9386 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9387 := params 10
abbrev ray9387 := rays 10
def bank9387 : Fin 2 → Cell := twoBank p9387 ray9387
theorem signs9387 : ∀ j, Signs p9387 (bank9387 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9388 := params 11
abbrev ray9388 := rays 11
def bank9388 : Fin 2 → Cell := twoBank p9388 ray9388
theorem signs9388 : ∀ j, Signs p9388 (bank9388 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9389 := params 12
abbrev ray9389 := rays 12
def bank9389 : Fin 2 → Cell := twoBank p9389 ray9389
theorem signs9389 : ∀ j, Signs p9389 (bank9389 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9390 := params 13
abbrev ray9390 := rays 13
def bank9390 : Fin 2 → Cell := twoBank p9390 ray9390
theorem signs9390 : ∀ j, Signs p9390 (bank9390 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9391 := params 14
abbrev ray9391 := rays 14
def bank9391 : Fin 2 → Cell := twoBank p9391 ray9391
theorem signs9391 : ∀ j, Signs p9391 (bank9391 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9392 := params 15
abbrev ray9392 := rays 15
def bank9392 : Fin 2 → Cell := twoBank p9392 ray9392
theorem signs9392 : ∀ j, Signs p9392 (bank9392 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9393 := params 16
abbrev ray9393 := rays 16
def bank9393 : Fin 2 → Cell := twoBank p9393 ray9393
theorem signs9393 : ∀ j, Signs p9393 (bank9393 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9394 := params 17
abbrev ray9394 := rays 17
def bank9394 : Fin 2 → Cell := twoBank p9394 ray9394
theorem signs9394 : ∀ j, Signs p9394 (bank9394 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9395 := params 18
abbrev ray9395 := rays 18
def bank9395 : Fin 2 → Cell := twoBank p9395 ray9395
theorem signs9395 : ∀ j, Signs p9395 (bank9395 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9396 := params 19
abbrev ray9396 := rays 19
def bank9396 : Fin 2 → Cell := twoBank p9396 ray9396
theorem signs9396 : ∀ j, Signs p9396 (bank9396 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9397 := params 20
abbrev ray9397 := rays 20
def bank9397 : Fin 2 → Cell := twoBank p9397 ray9397
theorem signs9397 : ∀ j, Signs p9397 (bank9397 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9398 := params 21
abbrev ray9398 := rays 21
def bank9398 : Fin 2 → Cell := twoBank p9398 ray9398
theorem signs9398 : ∀ j, Signs p9398 (bank9398 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9399 := params 22
abbrev ray9399 := rays 22
def bank9399 : Fin 2 → Cell := twoBank p9399 ray9399
theorem signs9399 : ∀ j, Signs p9399 (bank9399 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9400 := params 23
abbrev ray9400 := rays 23
def bank9400 : Fin 2 → Cell := twoBank p9400 ray9400
theorem signs9400 : ∀ j, Signs p9400 (bank9400 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9401 := params 24
abbrev ray9401 := rays 24
def bank9401 : Fin 2 → Cell := twoBank p9401 ray9401
theorem signs9401 : ∀ j, Signs p9401 (bank9401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9402 := params 25
abbrev ray9402 := rays 25
def bank9402 : Fin 2 → Cell := twoBank p9402 ray9402
theorem signs9402 : ∀ j, Signs p9402 (bank9402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9403 := params 26
abbrev ray9403 := rays 26
def bank9403 : Fin 2 → Cell := twoBank p9403 ray9403
theorem signs9403 : ∀ j, Signs p9403 (bank9403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9404 := params 27
abbrev ray9404 := rays 27
def bank9404 : Fin 2 → Cell := twoBank p9404 ray9404
theorem signs9404 : ∀ j, Signs p9404 (bank9404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9405 := params 28
abbrev ray9405 := rays 28
def bank9405 : Fin 2 → Cell := twoBank p9405 ray9405
theorem signs9405 : ∀ j, Signs p9405 (bank9405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9406 := params 29
abbrev ray9406 := rays 29
def bank9406 : Fin 2 → Cell := twoBank p9406 ray9406
theorem signs9406 : ∀ j, Signs p9406 (bank9406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9407 := params 30
abbrev ray9407 := rays 30
def bank9407 : Fin 2 → Cell := twoBank p9407 ray9407
theorem signs9407 : ∀ j, Signs p9407 (bank9407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9408 := params 31
abbrev ray9408 := rays 31
def bank9408 : Fin 2 → Cell := twoBank p9408 ray9408
theorem signs9408 : ∀ j, Signs p9408 (bank9408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09377_09408
