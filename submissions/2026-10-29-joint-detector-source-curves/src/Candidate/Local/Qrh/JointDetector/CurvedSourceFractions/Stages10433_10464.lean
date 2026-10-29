/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10433_10464
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97309476623305,97309101252382,97308725861355,97308350450225,97307975018992,97307599567657,97307224096220,97306848604682,97306473093043,97306097561304,97305722009466,97305346437529,97304970845493,97304595233359,97304219601128,97303843948800,97303468276376,97303092583856,97302716871240,97302341138529,97301965385724,97301589612825,97301213819833,97300838006748,97300462173571,97300086320302,97299710446942,97299334553492,97298958639952,97298582706322,97298206752603,97297830778795,97297454784899]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10432+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10433 := params 0
abbrev ray10433 := rays 0
def bank10433 : Fin 2 → Cell := twoBank p10433 ray10433
theorem signs10433 : ∀ j, Signs p10433 (bank10433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10434 := params 1
abbrev ray10434 := rays 1
def bank10434 : Fin 2 → Cell := twoBank p10434 ray10434
theorem signs10434 : ∀ j, Signs p10434 (bank10434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10435 := params 2
abbrev ray10435 := rays 2
def bank10435 : Fin 2 → Cell := twoBank p10435 ray10435
theorem signs10435 : ∀ j, Signs p10435 (bank10435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10436 := params 3
abbrev ray10436 := rays 3
def bank10436 : Fin 2 → Cell := twoBank p10436 ray10436
theorem signs10436 : ∀ j, Signs p10436 (bank10436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10437 := params 4
abbrev ray10437 := rays 4
def bank10437 : Fin 2 → Cell := twoBank p10437 ray10437
theorem signs10437 : ∀ j, Signs p10437 (bank10437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10438 := params 5
abbrev ray10438 := rays 5
def bank10438 : Fin 2 → Cell := twoBank p10438 ray10438
theorem signs10438 : ∀ j, Signs p10438 (bank10438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10439 := params 6
abbrev ray10439 := rays 6
def bank10439 : Fin 2 → Cell := twoBank p10439 ray10439
theorem signs10439 : ∀ j, Signs p10439 (bank10439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10440 := params 7
abbrev ray10440 := rays 7
def bank10440 : Fin 2 → Cell := twoBank p10440 ray10440
theorem signs10440 : ∀ j, Signs p10440 (bank10440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10441 := params 8
abbrev ray10441 := rays 8
def bank10441 : Fin 2 → Cell := twoBank p10441 ray10441
theorem signs10441 : ∀ j, Signs p10441 (bank10441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10442 := params 9
abbrev ray10442 := rays 9
def bank10442 : Fin 2 → Cell := twoBank p10442 ray10442
theorem signs10442 : ∀ j, Signs p10442 (bank10442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10443 := params 10
abbrev ray10443 := rays 10
def bank10443 : Fin 2 → Cell := twoBank p10443 ray10443
theorem signs10443 : ∀ j, Signs p10443 (bank10443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10444 := params 11
abbrev ray10444 := rays 11
def bank10444 : Fin 2 → Cell := twoBank p10444 ray10444
theorem signs10444 : ∀ j, Signs p10444 (bank10444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10445 := params 12
abbrev ray10445 := rays 12
def bank10445 : Fin 2 → Cell := twoBank p10445 ray10445
theorem signs10445 : ∀ j, Signs p10445 (bank10445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10446 := params 13
abbrev ray10446 := rays 13
def bank10446 : Fin 2 → Cell := twoBank p10446 ray10446
theorem signs10446 : ∀ j, Signs p10446 (bank10446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10447 := params 14
abbrev ray10447 := rays 14
def bank10447 : Fin 2 → Cell := twoBank p10447 ray10447
theorem signs10447 : ∀ j, Signs p10447 (bank10447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10448 := params 15
abbrev ray10448 := rays 15
def bank10448 : Fin 2 → Cell := twoBank p10448 ray10448
theorem signs10448 : ∀ j, Signs p10448 (bank10448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10449 := params 16
abbrev ray10449 := rays 16
def bank10449 : Fin 2 → Cell := twoBank p10449 ray10449
theorem signs10449 : ∀ j, Signs p10449 (bank10449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10450 := params 17
abbrev ray10450 := rays 17
def bank10450 : Fin 2 → Cell := twoBank p10450 ray10450
theorem signs10450 : ∀ j, Signs p10450 (bank10450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10451 := params 18
abbrev ray10451 := rays 18
def bank10451 : Fin 2 → Cell := twoBank p10451 ray10451
theorem signs10451 : ∀ j, Signs p10451 (bank10451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10452 := params 19
abbrev ray10452 := rays 19
def bank10452 : Fin 2 → Cell := twoBank p10452 ray10452
theorem signs10452 : ∀ j, Signs p10452 (bank10452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10453 := params 20
abbrev ray10453 := rays 20
def bank10453 : Fin 2 → Cell := twoBank p10453 ray10453
theorem signs10453 : ∀ j, Signs p10453 (bank10453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10454 := params 21
abbrev ray10454 := rays 21
def bank10454 : Fin 2 → Cell := twoBank p10454 ray10454
theorem signs10454 : ∀ j, Signs p10454 (bank10454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10455 := params 22
abbrev ray10455 := rays 22
def bank10455 : Fin 2 → Cell := twoBank p10455 ray10455
theorem signs10455 : ∀ j, Signs p10455 (bank10455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10456 := params 23
abbrev ray10456 := rays 23
def bank10456 : Fin 2 → Cell := twoBank p10456 ray10456
theorem signs10456 : ∀ j, Signs p10456 (bank10456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10457 := params 24
abbrev ray10457 := rays 24
def bank10457 : Fin 2 → Cell := twoBank p10457 ray10457
theorem signs10457 : ∀ j, Signs p10457 (bank10457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10458 := params 25
abbrev ray10458 := rays 25
def bank10458 : Fin 2 → Cell := twoBank p10458 ray10458
theorem signs10458 : ∀ j, Signs p10458 (bank10458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10459 := params 26
abbrev ray10459 := rays 26
def bank10459 : Fin 2 → Cell := twoBank p10459 ray10459
theorem signs10459 : ∀ j, Signs p10459 (bank10459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10460 := params 27
abbrev ray10460 := rays 27
def bank10460 : Fin 2 → Cell := twoBank p10460 ray10460
theorem signs10460 : ∀ j, Signs p10460 (bank10460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10461 := params 28
abbrev ray10461 := rays 28
def bank10461 : Fin 2 → Cell := twoBank p10461 ray10461
theorem signs10461 : ∀ j, Signs p10461 (bank10461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10462 := params 29
abbrev ray10462 := rays 29
def bank10462 : Fin 2 → Cell := twoBank p10462 ray10462
theorem signs10462 : ∀ j, Signs p10462 (bank10462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10463 := params 30
abbrev ray10463 := rays 30
def bank10463 : Fin 2 → Cell := twoBank p10463 ray10463
theorem signs10463 : ∀ j, Signs p10463 (bank10463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10464 := params 31
abbrev ray10464 := rays 31
def bank10464 : Fin 2 → Cell := twoBank p10464 ray10464
theorem signs10464 : ∀ j, Signs p10464 (bank10464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10433_10464
