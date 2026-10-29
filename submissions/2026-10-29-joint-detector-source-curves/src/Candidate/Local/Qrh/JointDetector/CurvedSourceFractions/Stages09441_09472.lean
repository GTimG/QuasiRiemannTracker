/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09441_09472
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97671854552033,97671499393416,97671144214142,97670789014211,97670433793624,97670078552382,97669723290485,97669368007933,97669012704728,97668657380870,97668302036359,97667946671196,97667591285382,97667235878917,97666880451802,97666525004037,97666169535623,97665814046561,97665458536851,97665103006494,97664747455490,97664391883840,97664036291545,97663680678605,97663325045021,97662969390793,97662613715922,97662258020409,97661902304254,97661546567458,97661190810021,97660835031944,97660479233227]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9440+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9441 := params 0
abbrev ray9441 := rays 0
def bank9441 : Fin 2 → Cell := twoBank p9441 ray9441
theorem signs9441 : ∀ j, Signs p9441 (bank9441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9442 := params 1
abbrev ray9442 := rays 1
def bank9442 : Fin 2 → Cell := twoBank p9442 ray9442
theorem signs9442 : ∀ j, Signs p9442 (bank9442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9443 := params 2
abbrev ray9443 := rays 2
def bank9443 : Fin 2 → Cell := twoBank p9443 ray9443
theorem signs9443 : ∀ j, Signs p9443 (bank9443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9444 := params 3
abbrev ray9444 := rays 3
def bank9444 : Fin 2 → Cell := twoBank p9444 ray9444
theorem signs9444 : ∀ j, Signs p9444 (bank9444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9445 := params 4
abbrev ray9445 := rays 4
def bank9445 : Fin 2 → Cell := twoBank p9445 ray9445
theorem signs9445 : ∀ j, Signs p9445 (bank9445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9446 := params 5
abbrev ray9446 := rays 5
def bank9446 : Fin 2 → Cell := twoBank p9446 ray9446
theorem signs9446 : ∀ j, Signs p9446 (bank9446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9447 := params 6
abbrev ray9447 := rays 6
def bank9447 : Fin 2 → Cell := twoBank p9447 ray9447
theorem signs9447 : ∀ j, Signs p9447 (bank9447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9448 := params 7
abbrev ray9448 := rays 7
def bank9448 : Fin 2 → Cell := twoBank p9448 ray9448
theorem signs9448 : ∀ j, Signs p9448 (bank9448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9449 := params 8
abbrev ray9449 := rays 8
def bank9449 : Fin 2 → Cell := twoBank p9449 ray9449
theorem signs9449 : ∀ j, Signs p9449 (bank9449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9450 := params 9
abbrev ray9450 := rays 9
def bank9450 : Fin 2 → Cell := twoBank p9450 ray9450
theorem signs9450 : ∀ j, Signs p9450 (bank9450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9451 := params 10
abbrev ray9451 := rays 10
def bank9451 : Fin 2 → Cell := twoBank p9451 ray9451
theorem signs9451 : ∀ j, Signs p9451 (bank9451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9452 := params 11
abbrev ray9452 := rays 11
def bank9452 : Fin 2 → Cell := twoBank p9452 ray9452
theorem signs9452 : ∀ j, Signs p9452 (bank9452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9453 := params 12
abbrev ray9453 := rays 12
def bank9453 : Fin 2 → Cell := twoBank p9453 ray9453
theorem signs9453 : ∀ j, Signs p9453 (bank9453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9454 := params 13
abbrev ray9454 := rays 13
def bank9454 : Fin 2 → Cell := twoBank p9454 ray9454
theorem signs9454 : ∀ j, Signs p9454 (bank9454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9455 := params 14
abbrev ray9455 := rays 14
def bank9455 : Fin 2 → Cell := twoBank p9455 ray9455
theorem signs9455 : ∀ j, Signs p9455 (bank9455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9456 := params 15
abbrev ray9456 := rays 15
def bank9456 : Fin 2 → Cell := twoBank p9456 ray9456
theorem signs9456 : ∀ j, Signs p9456 (bank9456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9457 := params 16
abbrev ray9457 := rays 16
def bank9457 : Fin 2 → Cell := twoBank p9457 ray9457
theorem signs9457 : ∀ j, Signs p9457 (bank9457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9458 := params 17
abbrev ray9458 := rays 17
def bank9458 : Fin 2 → Cell := twoBank p9458 ray9458
theorem signs9458 : ∀ j, Signs p9458 (bank9458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9459 := params 18
abbrev ray9459 := rays 18
def bank9459 : Fin 2 → Cell := twoBank p9459 ray9459
theorem signs9459 : ∀ j, Signs p9459 (bank9459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9460 := params 19
abbrev ray9460 := rays 19
def bank9460 : Fin 2 → Cell := twoBank p9460 ray9460
theorem signs9460 : ∀ j, Signs p9460 (bank9460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9461 := params 20
abbrev ray9461 := rays 20
def bank9461 : Fin 2 → Cell := twoBank p9461 ray9461
theorem signs9461 : ∀ j, Signs p9461 (bank9461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9462 := params 21
abbrev ray9462 := rays 21
def bank9462 : Fin 2 → Cell := twoBank p9462 ray9462
theorem signs9462 : ∀ j, Signs p9462 (bank9462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9463 := params 22
abbrev ray9463 := rays 22
def bank9463 : Fin 2 → Cell := twoBank p9463 ray9463
theorem signs9463 : ∀ j, Signs p9463 (bank9463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9464 := params 23
abbrev ray9464 := rays 23
def bank9464 : Fin 2 → Cell := twoBank p9464 ray9464
theorem signs9464 : ∀ j, Signs p9464 (bank9464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9465 := params 24
abbrev ray9465 := rays 24
def bank9465 : Fin 2 → Cell := twoBank p9465 ray9465
theorem signs9465 : ∀ j, Signs p9465 (bank9465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9466 := params 25
abbrev ray9466 := rays 25
def bank9466 : Fin 2 → Cell := twoBank p9466 ray9466
theorem signs9466 : ∀ j, Signs p9466 (bank9466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9467 := params 26
abbrev ray9467 := rays 26
def bank9467 : Fin 2 → Cell := twoBank p9467 ray9467
theorem signs9467 : ∀ j, Signs p9467 (bank9467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9468 := params 27
abbrev ray9468 := rays 27
def bank9468 : Fin 2 → Cell := twoBank p9468 ray9468
theorem signs9468 : ∀ j, Signs p9468 (bank9468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9469 := params 28
abbrev ray9469 := rays 28
def bank9469 : Fin 2 → Cell := twoBank p9469 ray9469
theorem signs9469 : ∀ j, Signs p9469 (bank9469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9470 := params 29
abbrev ray9470 := rays 29
def bank9470 : Fin 2 → Cell := twoBank p9470 ray9470
theorem signs9470 : ∀ j, Signs p9470 (bank9470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9471 := params 30
abbrev ray9471 := rays 30
def bank9471 : Fin 2 → Cell := twoBank p9471 ray9471
theorem signs9471 : ∀ j, Signs p9471 (bank9471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9472 := params 31
abbrev ray9472 := rays 31
def bank9472 : Fin 2 → Cell := twoBank p9472 ray9472
theorem signs9472 : ∀ j, Signs p9472 (bank9472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09441_09472
