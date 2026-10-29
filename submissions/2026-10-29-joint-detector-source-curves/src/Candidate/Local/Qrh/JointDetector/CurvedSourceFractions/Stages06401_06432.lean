/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06401_06432
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98653013657341,98652724387034,98652435093910,98652145777969,98651856439213,98651567077642,98651277693257,98650988286059,98650698856049,98650409403228,98650119927597,98649830429156,98649540907906,98649251363849,98648961796985,98648672207314,98648382594838,98648092959558,98647803301474,98647513620587,98647223916898,98646934190408,98646644441118,98646354669028,98646064874140,98645775056454,98645485215971,98645195352692,98644905466618,98644615557749,98644325626087,98644035671632,98643745694385]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6400+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6401 := params 0
abbrev ray6401 := rays 0
def bank6401 : Fin 2 → Cell := twoBank p6401 ray6401
theorem signs6401 : ∀ j, Signs p6401 (bank6401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6402 := params 1
abbrev ray6402 := rays 1
def bank6402 : Fin 2 → Cell := twoBank p6402 ray6402
theorem signs6402 : ∀ j, Signs p6402 (bank6402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6403 := params 2
abbrev ray6403 := rays 2
def bank6403 : Fin 2 → Cell := twoBank p6403 ray6403
theorem signs6403 : ∀ j, Signs p6403 (bank6403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6404 := params 3
abbrev ray6404 := rays 3
def bank6404 : Fin 2 → Cell := twoBank p6404 ray6404
theorem signs6404 : ∀ j, Signs p6404 (bank6404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6405 := params 4
abbrev ray6405 := rays 4
def bank6405 : Fin 2 → Cell := twoBank p6405 ray6405
theorem signs6405 : ∀ j, Signs p6405 (bank6405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6406 := params 5
abbrev ray6406 := rays 5
def bank6406 : Fin 2 → Cell := twoBank p6406 ray6406
theorem signs6406 : ∀ j, Signs p6406 (bank6406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6407 := params 6
abbrev ray6407 := rays 6
def bank6407 : Fin 2 → Cell := twoBank p6407 ray6407
theorem signs6407 : ∀ j, Signs p6407 (bank6407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6408 := params 7
abbrev ray6408 := rays 7
def bank6408 : Fin 2 → Cell := twoBank p6408 ray6408
theorem signs6408 : ∀ j, Signs p6408 (bank6408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6409 := params 8
abbrev ray6409 := rays 8
def bank6409 : Fin 2 → Cell := twoBank p6409 ray6409
theorem signs6409 : ∀ j, Signs p6409 (bank6409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6410 := params 9
abbrev ray6410 := rays 9
def bank6410 : Fin 2 → Cell := twoBank p6410 ray6410
theorem signs6410 : ∀ j, Signs p6410 (bank6410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6411 := params 10
abbrev ray6411 := rays 10
def bank6411 : Fin 2 → Cell := twoBank p6411 ray6411
theorem signs6411 : ∀ j, Signs p6411 (bank6411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6412 := params 11
abbrev ray6412 := rays 11
def bank6412 : Fin 2 → Cell := twoBank p6412 ray6412
theorem signs6412 : ∀ j, Signs p6412 (bank6412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6413 := params 12
abbrev ray6413 := rays 12
def bank6413 : Fin 2 → Cell := twoBank p6413 ray6413
theorem signs6413 : ∀ j, Signs p6413 (bank6413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6414 := params 13
abbrev ray6414 := rays 13
def bank6414 : Fin 2 → Cell := twoBank p6414 ray6414
theorem signs6414 : ∀ j, Signs p6414 (bank6414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6415 := params 14
abbrev ray6415 := rays 14
def bank6415 : Fin 2 → Cell := twoBank p6415 ray6415
theorem signs6415 : ∀ j, Signs p6415 (bank6415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6416 := params 15
abbrev ray6416 := rays 15
def bank6416 : Fin 2 → Cell := twoBank p6416 ray6416
theorem signs6416 : ∀ j, Signs p6416 (bank6416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6417 := params 16
abbrev ray6417 := rays 16
def bank6417 : Fin 2 → Cell := twoBank p6417 ray6417
theorem signs6417 : ∀ j, Signs p6417 (bank6417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6418 := params 17
abbrev ray6418 := rays 17
def bank6418 : Fin 2 → Cell := twoBank p6418 ray6418
theorem signs6418 : ∀ j, Signs p6418 (bank6418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6419 := params 18
abbrev ray6419 := rays 18
def bank6419 : Fin 2 → Cell := twoBank p6419 ray6419
theorem signs6419 : ∀ j, Signs p6419 (bank6419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6420 := params 19
abbrev ray6420 := rays 19
def bank6420 : Fin 2 → Cell := twoBank p6420 ray6420
theorem signs6420 : ∀ j, Signs p6420 (bank6420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6421 := params 20
abbrev ray6421 := rays 20
def bank6421 : Fin 2 → Cell := twoBank p6421 ray6421
theorem signs6421 : ∀ j, Signs p6421 (bank6421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6422 := params 21
abbrev ray6422 := rays 21
def bank6422 : Fin 2 → Cell := twoBank p6422 ray6422
theorem signs6422 : ∀ j, Signs p6422 (bank6422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6423 := params 22
abbrev ray6423 := rays 22
def bank6423 : Fin 2 → Cell := twoBank p6423 ray6423
theorem signs6423 : ∀ j, Signs p6423 (bank6423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6424 := params 23
abbrev ray6424 := rays 23
def bank6424 : Fin 2 → Cell := twoBank p6424 ray6424
theorem signs6424 : ∀ j, Signs p6424 (bank6424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6425 := params 24
abbrev ray6425 := rays 24
def bank6425 : Fin 2 → Cell := twoBank p6425 ray6425
theorem signs6425 : ∀ j, Signs p6425 (bank6425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6426 := params 25
abbrev ray6426 := rays 25
def bank6426 : Fin 2 → Cell := twoBank p6426 ray6426
theorem signs6426 : ∀ j, Signs p6426 (bank6426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6427 := params 26
abbrev ray6427 := rays 26
def bank6427 : Fin 2 → Cell := twoBank p6427 ray6427
theorem signs6427 : ∀ j, Signs p6427 (bank6427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6428 := params 27
abbrev ray6428 := rays 27
def bank6428 : Fin 2 → Cell := twoBank p6428 ray6428
theorem signs6428 : ∀ j, Signs p6428 (bank6428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6429 := params 28
abbrev ray6429 := rays 28
def bank6429 : Fin 2 → Cell := twoBank p6429 ray6429
theorem signs6429 : ∀ j, Signs p6429 (bank6429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6430 := params 29
abbrev ray6430 := rays 29
def bank6430 : Fin 2 → Cell := twoBank p6430 ray6430
theorem signs6430 : ∀ j, Signs p6430 (bank6430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6431 := params 30
abbrev ray6431 := rays 30
def bank6431 : Fin 2 → Cell := twoBank p6431 ray6431
theorem signs6431 : ∀ j, Signs p6431 (bank6431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6432 := params 31
abbrev ray6432 := rays 31
def bank6432 : Fin 2 → Cell := twoBank p6432 ray6432
theorem signs6432 : ∀ j, Signs p6432 (bank6432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06401_06432
