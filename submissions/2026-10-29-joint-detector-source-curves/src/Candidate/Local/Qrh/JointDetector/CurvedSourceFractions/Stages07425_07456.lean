/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07425_07456
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98344995999592,98344683789507,98344371557420,98344059303331,98343747027241,98343434729150,98343122409060,98342810066971,98342497702884,98342185316800,98341872908719,98341560478642,98341248026570,98340935552504,98340623056444,98340310538392,98339997998347,98339685436311,98339372852285,98339060246269,98338747618264,98338434968270,98338122296289,98337809602321,98337496886367,98337184148427,98336871388503,98336558606595,98336245802704,98335932976831,98335620128976,98335307259140,98334994367324]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7424+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7425 := params 0
abbrev ray7425 := rays 0
def bank7425 : Fin 2 → Cell := twoBank p7425 ray7425
theorem signs7425 : ∀ j, Signs p7425 (bank7425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7426 := params 1
abbrev ray7426 := rays 1
def bank7426 : Fin 2 → Cell := twoBank p7426 ray7426
theorem signs7426 : ∀ j, Signs p7426 (bank7426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7427 := params 2
abbrev ray7427 := rays 2
def bank7427 : Fin 2 → Cell := twoBank p7427 ray7427
theorem signs7427 : ∀ j, Signs p7427 (bank7427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7428 := params 3
abbrev ray7428 := rays 3
def bank7428 : Fin 2 → Cell := twoBank p7428 ray7428
theorem signs7428 : ∀ j, Signs p7428 (bank7428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7429 := params 4
abbrev ray7429 := rays 4
def bank7429 : Fin 2 → Cell := twoBank p7429 ray7429
theorem signs7429 : ∀ j, Signs p7429 (bank7429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7430 := params 5
abbrev ray7430 := rays 5
def bank7430 : Fin 2 → Cell := twoBank p7430 ray7430
theorem signs7430 : ∀ j, Signs p7430 (bank7430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7431 := params 6
abbrev ray7431 := rays 6
def bank7431 : Fin 2 → Cell := twoBank p7431 ray7431
theorem signs7431 : ∀ j, Signs p7431 (bank7431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7432 := params 7
abbrev ray7432 := rays 7
def bank7432 : Fin 2 → Cell := twoBank p7432 ray7432
theorem signs7432 : ∀ j, Signs p7432 (bank7432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7433 := params 8
abbrev ray7433 := rays 8
def bank7433 : Fin 2 → Cell := twoBank p7433 ray7433
theorem signs7433 : ∀ j, Signs p7433 (bank7433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7434 := params 9
abbrev ray7434 := rays 9
def bank7434 : Fin 2 → Cell := twoBank p7434 ray7434
theorem signs7434 : ∀ j, Signs p7434 (bank7434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7435 := params 10
abbrev ray7435 := rays 10
def bank7435 : Fin 2 → Cell := twoBank p7435 ray7435
theorem signs7435 : ∀ j, Signs p7435 (bank7435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7436 := params 11
abbrev ray7436 := rays 11
def bank7436 : Fin 2 → Cell := twoBank p7436 ray7436
theorem signs7436 : ∀ j, Signs p7436 (bank7436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7437 := params 12
abbrev ray7437 := rays 12
def bank7437 : Fin 2 → Cell := twoBank p7437 ray7437
theorem signs7437 : ∀ j, Signs p7437 (bank7437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7438 := params 13
abbrev ray7438 := rays 13
def bank7438 : Fin 2 → Cell := twoBank p7438 ray7438
theorem signs7438 : ∀ j, Signs p7438 (bank7438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7439 := params 14
abbrev ray7439 := rays 14
def bank7439 : Fin 2 → Cell := twoBank p7439 ray7439
theorem signs7439 : ∀ j, Signs p7439 (bank7439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7440 := params 15
abbrev ray7440 := rays 15
def bank7440 : Fin 2 → Cell := twoBank p7440 ray7440
theorem signs7440 : ∀ j, Signs p7440 (bank7440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7441 := params 16
abbrev ray7441 := rays 16
def bank7441 : Fin 2 → Cell := twoBank p7441 ray7441
theorem signs7441 : ∀ j, Signs p7441 (bank7441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7442 := params 17
abbrev ray7442 := rays 17
def bank7442 : Fin 2 → Cell := twoBank p7442 ray7442
theorem signs7442 : ∀ j, Signs p7442 (bank7442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7443 := params 18
abbrev ray7443 := rays 18
def bank7443 : Fin 2 → Cell := twoBank p7443 ray7443
theorem signs7443 : ∀ j, Signs p7443 (bank7443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7444 := params 19
abbrev ray7444 := rays 19
def bank7444 : Fin 2 → Cell := twoBank p7444 ray7444
theorem signs7444 : ∀ j, Signs p7444 (bank7444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7445 := params 20
abbrev ray7445 := rays 20
def bank7445 : Fin 2 → Cell := twoBank p7445 ray7445
theorem signs7445 : ∀ j, Signs p7445 (bank7445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7446 := params 21
abbrev ray7446 := rays 21
def bank7446 : Fin 2 → Cell := twoBank p7446 ray7446
theorem signs7446 : ∀ j, Signs p7446 (bank7446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7447 := params 22
abbrev ray7447 := rays 22
def bank7447 : Fin 2 → Cell := twoBank p7447 ray7447
theorem signs7447 : ∀ j, Signs p7447 (bank7447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7448 := params 23
abbrev ray7448 := rays 23
def bank7448 : Fin 2 → Cell := twoBank p7448 ray7448
theorem signs7448 : ∀ j, Signs p7448 (bank7448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7449 := params 24
abbrev ray7449 := rays 24
def bank7449 : Fin 2 → Cell := twoBank p7449 ray7449
theorem signs7449 : ∀ j, Signs p7449 (bank7449 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7450 := params 25
abbrev ray7450 := rays 25
def bank7450 : Fin 2 → Cell := twoBank p7450 ray7450
theorem signs7450 : ∀ j, Signs p7450 (bank7450 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7451 := params 26
abbrev ray7451 := rays 26
def bank7451 : Fin 2 → Cell := twoBank p7451 ray7451
theorem signs7451 : ∀ j, Signs p7451 (bank7451 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7452 := params 27
abbrev ray7452 := rays 27
def bank7452 : Fin 2 → Cell := twoBank p7452 ray7452
theorem signs7452 : ∀ j, Signs p7452 (bank7452 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7453 := params 28
abbrev ray7453 := rays 28
def bank7453 : Fin 2 → Cell := twoBank p7453 ray7453
theorem signs7453 : ∀ j, Signs p7453 (bank7453 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7454 := params 29
abbrev ray7454 := rays 29
def bank7454 : Fin 2 → Cell := twoBank p7454 ray7454
theorem signs7454 : ∀ j, Signs p7454 (bank7454 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7455 := params 30
abbrev ray7455 := rays 30
def bank7455 : Fin 2 → Cell := twoBank p7455 ray7455
theorem signs7455 : ∀ j, Signs p7455 (bank7455 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7456 := params 31
abbrev ray7456 := rays 31
def bank7456 : Fin 2 → Cell := twoBank p7456 ray7456
theorem signs7456 : ∀ j, Signs p7456 (bank7456 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07425_07456
