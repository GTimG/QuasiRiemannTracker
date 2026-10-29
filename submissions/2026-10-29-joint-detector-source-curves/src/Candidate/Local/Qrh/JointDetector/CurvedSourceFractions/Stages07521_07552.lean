/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07521_07552
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98314923606518,98314609287591,98314294946732,98313980583943,98313666199225,98313351792578,98313037364003,98312722913500,98312408441071,98312093946716,98311779430436,98311464892231,98311150332103,98310835750052,98310521146078,98310206520183,98309891872367,98309577202631,98309262510976,98308947797403,98308633061912,98308318304504,98308003525180,98307688723940,98307373900785,98307059055716,98306744188734,98306429299839,98306114389033,98305799456316,98305484501688,98305169525151,98304854526705]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7520+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7521 := params 0
abbrev ray7521 := rays 0
def bank7521 : Fin 2 → Cell := twoBank p7521 ray7521
theorem signs7521 : ∀ j, Signs p7521 (bank7521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7522 := params 1
abbrev ray7522 := rays 1
def bank7522 : Fin 2 → Cell := twoBank p7522 ray7522
theorem signs7522 : ∀ j, Signs p7522 (bank7522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7523 := params 2
abbrev ray7523 := rays 2
def bank7523 : Fin 2 → Cell := twoBank p7523 ray7523
theorem signs7523 : ∀ j, Signs p7523 (bank7523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7524 := params 3
abbrev ray7524 := rays 3
def bank7524 : Fin 2 → Cell := twoBank p7524 ray7524
theorem signs7524 : ∀ j, Signs p7524 (bank7524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7525 := params 4
abbrev ray7525 := rays 4
def bank7525 : Fin 2 → Cell := twoBank p7525 ray7525
theorem signs7525 : ∀ j, Signs p7525 (bank7525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7526 := params 5
abbrev ray7526 := rays 5
def bank7526 : Fin 2 → Cell := twoBank p7526 ray7526
theorem signs7526 : ∀ j, Signs p7526 (bank7526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7527 := params 6
abbrev ray7527 := rays 6
def bank7527 : Fin 2 → Cell := twoBank p7527 ray7527
theorem signs7527 : ∀ j, Signs p7527 (bank7527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7528 := params 7
abbrev ray7528 := rays 7
def bank7528 : Fin 2 → Cell := twoBank p7528 ray7528
theorem signs7528 : ∀ j, Signs p7528 (bank7528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7529 := params 8
abbrev ray7529 := rays 8
def bank7529 : Fin 2 → Cell := twoBank p7529 ray7529
theorem signs7529 : ∀ j, Signs p7529 (bank7529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7530 := params 9
abbrev ray7530 := rays 9
def bank7530 : Fin 2 → Cell := twoBank p7530 ray7530
theorem signs7530 : ∀ j, Signs p7530 (bank7530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7531 := params 10
abbrev ray7531 := rays 10
def bank7531 : Fin 2 → Cell := twoBank p7531 ray7531
theorem signs7531 : ∀ j, Signs p7531 (bank7531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7532 := params 11
abbrev ray7532 := rays 11
def bank7532 : Fin 2 → Cell := twoBank p7532 ray7532
theorem signs7532 : ∀ j, Signs p7532 (bank7532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7533 := params 12
abbrev ray7533 := rays 12
def bank7533 : Fin 2 → Cell := twoBank p7533 ray7533
theorem signs7533 : ∀ j, Signs p7533 (bank7533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7534 := params 13
abbrev ray7534 := rays 13
def bank7534 : Fin 2 → Cell := twoBank p7534 ray7534
theorem signs7534 : ∀ j, Signs p7534 (bank7534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7535 := params 14
abbrev ray7535 := rays 14
def bank7535 : Fin 2 → Cell := twoBank p7535 ray7535
theorem signs7535 : ∀ j, Signs p7535 (bank7535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7536 := params 15
abbrev ray7536 := rays 15
def bank7536 : Fin 2 → Cell := twoBank p7536 ray7536
theorem signs7536 : ∀ j, Signs p7536 (bank7536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7537 := params 16
abbrev ray7537 := rays 16
def bank7537 : Fin 2 → Cell := twoBank p7537 ray7537
theorem signs7537 : ∀ j, Signs p7537 (bank7537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7538 := params 17
abbrev ray7538 := rays 17
def bank7538 : Fin 2 → Cell := twoBank p7538 ray7538
theorem signs7538 : ∀ j, Signs p7538 (bank7538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7539 := params 18
abbrev ray7539 := rays 18
def bank7539 : Fin 2 → Cell := twoBank p7539 ray7539
theorem signs7539 : ∀ j, Signs p7539 (bank7539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7540 := params 19
abbrev ray7540 := rays 19
def bank7540 : Fin 2 → Cell := twoBank p7540 ray7540
theorem signs7540 : ∀ j, Signs p7540 (bank7540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7541 := params 20
abbrev ray7541 := rays 20
def bank7541 : Fin 2 → Cell := twoBank p7541 ray7541
theorem signs7541 : ∀ j, Signs p7541 (bank7541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7542 := params 21
abbrev ray7542 := rays 21
def bank7542 : Fin 2 → Cell := twoBank p7542 ray7542
theorem signs7542 : ∀ j, Signs p7542 (bank7542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7543 := params 22
abbrev ray7543 := rays 22
def bank7543 : Fin 2 → Cell := twoBank p7543 ray7543
theorem signs7543 : ∀ j, Signs p7543 (bank7543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7544 := params 23
abbrev ray7544 := rays 23
def bank7544 : Fin 2 → Cell := twoBank p7544 ray7544
theorem signs7544 : ∀ j, Signs p7544 (bank7544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7545 := params 24
abbrev ray7545 := rays 24
def bank7545 : Fin 2 → Cell := twoBank p7545 ray7545
theorem signs7545 : ∀ j, Signs p7545 (bank7545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7546 := params 25
abbrev ray7546 := rays 25
def bank7546 : Fin 2 → Cell := twoBank p7546 ray7546
theorem signs7546 : ∀ j, Signs p7546 (bank7546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7547 := params 26
abbrev ray7547 := rays 26
def bank7547 : Fin 2 → Cell := twoBank p7547 ray7547
theorem signs7547 : ∀ j, Signs p7547 (bank7547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7548 := params 27
abbrev ray7548 := rays 27
def bank7548 : Fin 2 → Cell := twoBank p7548 ray7548
theorem signs7548 : ∀ j, Signs p7548 (bank7548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7549 := params 28
abbrev ray7549 := rays 28
def bank7549 : Fin 2 → Cell := twoBank p7549 ray7549
theorem signs7549 : ∀ j, Signs p7549 (bank7549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7550 := params 29
abbrev ray7550 := rays 29
def bank7550 : Fin 2 → Cell := twoBank p7550 ray7550
theorem signs7550 : ∀ j, Signs p7550 (bank7550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7551 := params 30
abbrev ray7551 := rays 30
def bank7551 : Fin 2 → Cell := twoBank p7551 ray7551
theorem signs7551 : ∀ j, Signs p7551 (bank7551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7552 := params 31
abbrev ray7552 := rays 31
def bank7552 : Fin 2 → Cell := twoBank p7552 ray7552
theorem signs7552 : ∀ j, Signs p7552 (bank7552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07521_07552
