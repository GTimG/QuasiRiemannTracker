/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13345_13376
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96133554784603,96133124244355,96132693687756,96132263114806,96131832525505,96131401919853,96130971297850,96130540659497,96130110004794,96129679333741,96129248646339,96128817942587,96128387222486,96127956486036,96127525733238,96127094964091,96126664178596,96126233376753,96125802558563,96125371724025,96124940873140,96124510005908,96124079122329,96123648222404,96123217306132,96122786373514,96122355424551,96121924459242,96121493477588,96121062479589,96120631465245,96120200434556,96119769387523]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13344+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13345 := params 0
abbrev ray13345 := rays 0
def bank13345 : Fin 1 → Cell := oneBank p13345 ray13345
theorem signs13345 : ∀ j, Signs p13345 (bank13345 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13346 := params 1
abbrev ray13346 := rays 1
def bank13346 : Fin 1 → Cell := oneBank p13346 ray13346
theorem signs13346 : ∀ j, Signs p13346 (bank13346 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13347 := params 2
abbrev ray13347 := rays 2
def bank13347 : Fin 1 → Cell := oneBank p13347 ray13347
theorem signs13347 : ∀ j, Signs p13347 (bank13347 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13348 := params 3
abbrev ray13348 := rays 3
def bank13348 : Fin 1 → Cell := oneBank p13348 ray13348
theorem signs13348 : ∀ j, Signs p13348 (bank13348 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13349 := params 4
abbrev ray13349 := rays 4
def bank13349 : Fin 1 → Cell := oneBank p13349 ray13349
theorem signs13349 : ∀ j, Signs p13349 (bank13349 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13350 := params 5
abbrev ray13350 := rays 5
def bank13350 : Fin 1 → Cell := oneBank p13350 ray13350
theorem signs13350 : ∀ j, Signs p13350 (bank13350 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13351 := params 6
abbrev ray13351 := rays 6
def bank13351 : Fin 1 → Cell := oneBank p13351 ray13351
theorem signs13351 : ∀ j, Signs p13351 (bank13351 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13352 := params 7
abbrev ray13352 := rays 7
def bank13352 : Fin 1 → Cell := oneBank p13352 ray13352
theorem signs13352 : ∀ j, Signs p13352 (bank13352 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13353 := params 8
abbrev ray13353 := rays 8
def bank13353 : Fin 1 → Cell := oneBank p13353 ray13353
theorem signs13353 : ∀ j, Signs p13353 (bank13353 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13354 := params 9
abbrev ray13354 := rays 9
def bank13354 : Fin 1 → Cell := oneBank p13354 ray13354
theorem signs13354 : ∀ j, Signs p13354 (bank13354 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13355 := params 10
abbrev ray13355 := rays 10
def bank13355 : Fin 1 → Cell := oneBank p13355 ray13355
theorem signs13355 : ∀ j, Signs p13355 (bank13355 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13356 := params 11
abbrev ray13356 := rays 11
def bank13356 : Fin 1 → Cell := oneBank p13356 ray13356
theorem signs13356 : ∀ j, Signs p13356 (bank13356 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13357 := params 12
abbrev ray13357 := rays 12
def bank13357 : Fin 1 → Cell := oneBank p13357 ray13357
theorem signs13357 : ∀ j, Signs p13357 (bank13357 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13358 := params 13
abbrev ray13358 := rays 13
def bank13358 : Fin 1 → Cell := oneBank p13358 ray13358
theorem signs13358 : ∀ j, Signs p13358 (bank13358 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13359 := params 14
abbrev ray13359 := rays 14
def bank13359 : Fin 1 → Cell := oneBank p13359 ray13359
theorem signs13359 : ∀ j, Signs p13359 (bank13359 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13360 := params 15
abbrev ray13360 := rays 15
def bank13360 : Fin 1 → Cell := oneBank p13360 ray13360
theorem signs13360 : ∀ j, Signs p13360 (bank13360 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13361 := params 16
abbrev ray13361 := rays 16
def bank13361 : Fin 1 → Cell := oneBank p13361 ray13361
theorem signs13361 : ∀ j, Signs p13361 (bank13361 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13362 := params 17
abbrev ray13362 := rays 17
def bank13362 : Fin 1 → Cell := oneBank p13362 ray13362
theorem signs13362 : ∀ j, Signs p13362 (bank13362 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13363 := params 18
abbrev ray13363 := rays 18
def bank13363 : Fin 1 → Cell := oneBank p13363 ray13363
theorem signs13363 : ∀ j, Signs p13363 (bank13363 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13364 := params 19
abbrev ray13364 := rays 19
def bank13364 : Fin 1 → Cell := oneBank p13364 ray13364
theorem signs13364 : ∀ j, Signs p13364 (bank13364 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13365 := params 20
abbrev ray13365 := rays 20
def bank13365 : Fin 1 → Cell := oneBank p13365 ray13365
theorem signs13365 : ∀ j, Signs p13365 (bank13365 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13366 := params 21
abbrev ray13366 := rays 21
def bank13366 : Fin 1 → Cell := oneBank p13366 ray13366
theorem signs13366 : ∀ j, Signs p13366 (bank13366 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13367 := params 22
abbrev ray13367 := rays 22
def bank13367 : Fin 1 → Cell := oneBank p13367 ray13367
theorem signs13367 : ∀ j, Signs p13367 (bank13367 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13368 := params 23
abbrev ray13368 := rays 23
def bank13368 : Fin 1 → Cell := oneBank p13368 ray13368
theorem signs13368 : ∀ j, Signs p13368 (bank13368 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13369 := params 24
abbrev ray13369 := rays 24
def bank13369 : Fin 1 → Cell := oneBank p13369 ray13369
theorem signs13369 : ∀ j, Signs p13369 (bank13369 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13370 := params 25
abbrev ray13370 := rays 25
def bank13370 : Fin 1 → Cell := oneBank p13370 ray13370
theorem signs13370 : ∀ j, Signs p13370 (bank13370 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13371 := params 26
abbrev ray13371 := rays 26
def bank13371 : Fin 1 → Cell := oneBank p13371 ray13371
theorem signs13371 : ∀ j, Signs p13371 (bank13371 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13372 := params 27
abbrev ray13372 := rays 27
def bank13372 : Fin 1 → Cell := oneBank p13372 ray13372
theorem signs13372 : ∀ j, Signs p13372 (bank13372 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13373 := params 28
abbrev ray13373 := rays 28
def bank13373 : Fin 1 → Cell := oneBank p13373 ray13373
theorem signs13373 : ∀ j, Signs p13373 (bank13373 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13374 := params 29
abbrev ray13374 := rays 29
def bank13374 : Fin 1 → Cell := oneBank p13374 ray13374
theorem signs13374 : ∀ j, Signs p13374 (bank13374 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13375 := params 30
abbrev ray13375 := rays 30
def bank13375 : Fin 1 → Cell := oneBank p13375 ray13375
theorem signs13375 : ∀ j, Signs p13375 (bank13375 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13376 := params 31
abbrev ray13376 := rays 31
def bank13376 : Fin 1 → Cell := oneBank p13376 ray13376
theorem signs13376 : ∀ j, Signs p13376 (bank13376 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13345_13376
