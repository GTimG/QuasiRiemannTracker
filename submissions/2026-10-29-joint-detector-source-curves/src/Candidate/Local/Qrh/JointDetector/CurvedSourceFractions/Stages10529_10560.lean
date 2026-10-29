/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10529_10560
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97273349416390,97272972117893,97272594799342,97272217460738,97271840102081,97271462723372,97271085324612,97270707905801,97270330466939,97269953008027,97269575529066,97269198030056,97268820510997,97268442971890,97268065412736,97267687833535,97267310234288,97266932614995,97266554975657,97266177316274,97265799636847,97265421937376,97265044217862,97264666478305,97264288718706,97263910939065,97263533139383,97263155319660,97262777479897,97262399620094,97262021740252,97261643840372,97261265920454]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10528+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10529 := params 0
abbrev ray10529 := rays 0
def bank10529 : Fin 2 → Cell := twoBank p10529 ray10529
theorem signs10529 : ∀ j, Signs p10529 (bank10529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10530 := params 1
abbrev ray10530 := rays 1
def bank10530 : Fin 2 → Cell := twoBank p10530 ray10530
theorem signs10530 : ∀ j, Signs p10530 (bank10530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10531 := params 2
abbrev ray10531 := rays 2
def bank10531 : Fin 2 → Cell := twoBank p10531 ray10531
theorem signs10531 : ∀ j, Signs p10531 (bank10531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10532 := params 3
abbrev ray10532 := rays 3
def bank10532 : Fin 2 → Cell := twoBank p10532 ray10532
theorem signs10532 : ∀ j, Signs p10532 (bank10532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10533 := params 4
abbrev ray10533 := rays 4
def bank10533 : Fin 2 → Cell := twoBank p10533 ray10533
theorem signs10533 : ∀ j, Signs p10533 (bank10533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10534 := params 5
abbrev ray10534 := rays 5
def bank10534 : Fin 2 → Cell := twoBank p10534 ray10534
theorem signs10534 : ∀ j, Signs p10534 (bank10534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10535 := params 6
abbrev ray10535 := rays 6
def bank10535 : Fin 2 → Cell := twoBank p10535 ray10535
theorem signs10535 : ∀ j, Signs p10535 (bank10535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10536 := params 7
abbrev ray10536 := rays 7
def bank10536 : Fin 2 → Cell := twoBank p10536 ray10536
theorem signs10536 : ∀ j, Signs p10536 (bank10536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10537 := params 8
abbrev ray10537 := rays 8
def bank10537 : Fin 2 → Cell := twoBank p10537 ray10537
theorem signs10537 : ∀ j, Signs p10537 (bank10537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10538 := params 9
abbrev ray10538 := rays 9
def bank10538 : Fin 2 → Cell := twoBank p10538 ray10538
theorem signs10538 : ∀ j, Signs p10538 (bank10538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10539 := params 10
abbrev ray10539 := rays 10
def bank10539 : Fin 2 → Cell := twoBank p10539 ray10539
theorem signs10539 : ∀ j, Signs p10539 (bank10539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10540 := params 11
abbrev ray10540 := rays 11
def bank10540 : Fin 2 → Cell := twoBank p10540 ray10540
theorem signs10540 : ∀ j, Signs p10540 (bank10540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10541 := params 12
abbrev ray10541 := rays 12
def bank10541 : Fin 2 → Cell := twoBank p10541 ray10541
theorem signs10541 : ∀ j, Signs p10541 (bank10541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10542 := params 13
abbrev ray10542 := rays 13
def bank10542 : Fin 2 → Cell := twoBank p10542 ray10542
theorem signs10542 : ∀ j, Signs p10542 (bank10542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10543 := params 14
abbrev ray10543 := rays 14
def bank10543 : Fin 2 → Cell := twoBank p10543 ray10543
theorem signs10543 : ∀ j, Signs p10543 (bank10543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10544 := params 15
abbrev ray10544 := rays 15
def bank10544 : Fin 2 → Cell := twoBank p10544 ray10544
theorem signs10544 : ∀ j, Signs p10544 (bank10544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10545 := params 16
abbrev ray10545 := rays 16
def bank10545 : Fin 2 → Cell := twoBank p10545 ray10545
theorem signs10545 : ∀ j, Signs p10545 (bank10545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10546 := params 17
abbrev ray10546 := rays 17
def bank10546 : Fin 2 → Cell := twoBank p10546 ray10546
theorem signs10546 : ∀ j, Signs p10546 (bank10546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10547 := params 18
abbrev ray10547 := rays 18
def bank10547 : Fin 2 → Cell := twoBank p10547 ray10547
theorem signs10547 : ∀ j, Signs p10547 (bank10547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10548 := params 19
abbrev ray10548 := rays 19
def bank10548 : Fin 2 → Cell := twoBank p10548 ray10548
theorem signs10548 : ∀ j, Signs p10548 (bank10548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10549 := params 20
abbrev ray10549 := rays 20
def bank10549 : Fin 2 → Cell := twoBank p10549 ray10549
theorem signs10549 : ∀ j, Signs p10549 (bank10549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10550 := params 21
abbrev ray10550 := rays 21
def bank10550 : Fin 2 → Cell := twoBank p10550 ray10550
theorem signs10550 : ∀ j, Signs p10550 (bank10550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10551 := params 22
abbrev ray10551 := rays 22
def bank10551 : Fin 2 → Cell := twoBank p10551 ray10551
theorem signs10551 : ∀ j, Signs p10551 (bank10551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10552 := params 23
abbrev ray10552 := rays 23
def bank10552 : Fin 2 → Cell := twoBank p10552 ray10552
theorem signs10552 : ∀ j, Signs p10552 (bank10552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10553 := params 24
abbrev ray10553 := rays 24
def bank10553 : Fin 2 → Cell := twoBank p10553 ray10553
theorem signs10553 : ∀ j, Signs p10553 (bank10553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10554 := params 25
abbrev ray10554 := rays 25
def bank10554 : Fin 2 → Cell := twoBank p10554 ray10554
theorem signs10554 : ∀ j, Signs p10554 (bank10554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10555 := params 26
abbrev ray10555 := rays 26
def bank10555 : Fin 2 → Cell := twoBank p10555 ray10555
theorem signs10555 : ∀ j, Signs p10555 (bank10555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10556 := params 27
abbrev ray10556 := rays 27
def bank10556 : Fin 2 → Cell := twoBank p10556 ray10556
theorem signs10556 : ∀ j, Signs p10556 (bank10556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10557 := params 28
abbrev ray10557 := rays 28
def bank10557 : Fin 2 → Cell := twoBank p10557 ray10557
theorem signs10557 : ∀ j, Signs p10557 (bank10557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10558 := params 29
abbrev ray10558 := rays 29
def bank10558 : Fin 2 → Cell := twoBank p10558 ray10558
theorem signs10558 : ∀ j, Signs p10558 (bank10558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10559 := params 30
abbrev ray10559 := rays 30
def bank10559 : Fin 2 → Cell := twoBank p10559 ray10559
theorem signs10559 : ∀ j, Signs p10559 (bank10559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10560 := params 31
abbrev ray10560 := rays 31
def bank10560 : Fin 2 → Cell := twoBank p10560 ray10560
theorem signs10560 : ∀ j, Signs p10560 (bank10560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10529_10560
