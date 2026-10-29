/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10561_10592
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97261265920454,97260887980498,97260510020505,97260132040476,97259754040411,97259376020310,97258997980174,97258619920004,97258241839800,97257863739562,97257485619291,97257107478988,97256729318653,97256351138287,97255972937890,97255594717463,97255216477006,97254838216520,97254459936005,97254081635462,97253703314891,97253324974293,97252946613668,97252568233017,97252189832340,97251811411638,97251432970911,97251054510160,97250676029386,97250297528589,97249919007769,97249540466927,97249161906063]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10560+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10561 := params 0
abbrev ray10561 := rays 0
def bank10561 : Fin 2 → Cell := twoBank p10561 ray10561
theorem signs10561 : ∀ j, Signs p10561 (bank10561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10562 := params 1
abbrev ray10562 := rays 1
def bank10562 : Fin 2 → Cell := twoBank p10562 ray10562
theorem signs10562 : ∀ j, Signs p10562 (bank10562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10563 := params 2
abbrev ray10563 := rays 2
def bank10563 : Fin 2 → Cell := twoBank p10563 ray10563
theorem signs10563 : ∀ j, Signs p10563 (bank10563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10564 := params 3
abbrev ray10564 := rays 3
def bank10564 : Fin 2 → Cell := twoBank p10564 ray10564
theorem signs10564 : ∀ j, Signs p10564 (bank10564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10565 := params 4
abbrev ray10565 := rays 4
def bank10565 : Fin 2 → Cell := twoBank p10565 ray10565
theorem signs10565 : ∀ j, Signs p10565 (bank10565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10566 := params 5
abbrev ray10566 := rays 5
def bank10566 : Fin 2 → Cell := twoBank p10566 ray10566
theorem signs10566 : ∀ j, Signs p10566 (bank10566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10567 := params 6
abbrev ray10567 := rays 6
def bank10567 : Fin 2 → Cell := twoBank p10567 ray10567
theorem signs10567 : ∀ j, Signs p10567 (bank10567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10568 := params 7
abbrev ray10568 := rays 7
def bank10568 : Fin 2 → Cell := twoBank p10568 ray10568
theorem signs10568 : ∀ j, Signs p10568 (bank10568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10569 := params 8
abbrev ray10569 := rays 8
def bank10569 : Fin 2 → Cell := twoBank p10569 ray10569
theorem signs10569 : ∀ j, Signs p10569 (bank10569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10570 := params 9
abbrev ray10570 := rays 9
def bank10570 : Fin 2 → Cell := twoBank p10570 ray10570
theorem signs10570 : ∀ j, Signs p10570 (bank10570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10571 := params 10
abbrev ray10571 := rays 10
def bank10571 : Fin 2 → Cell := twoBank p10571 ray10571
theorem signs10571 : ∀ j, Signs p10571 (bank10571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10572 := params 11
abbrev ray10572 := rays 11
def bank10572 : Fin 2 → Cell := twoBank p10572 ray10572
theorem signs10572 : ∀ j, Signs p10572 (bank10572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10573 := params 12
abbrev ray10573 := rays 12
def bank10573 : Fin 2 → Cell := twoBank p10573 ray10573
theorem signs10573 : ∀ j, Signs p10573 (bank10573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10574 := params 13
abbrev ray10574 := rays 13
def bank10574 : Fin 2 → Cell := twoBank p10574 ray10574
theorem signs10574 : ∀ j, Signs p10574 (bank10574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10575 := params 14
abbrev ray10575 := rays 14
def bank10575 : Fin 2 → Cell := twoBank p10575 ray10575
theorem signs10575 : ∀ j, Signs p10575 (bank10575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10576 := params 15
abbrev ray10576 := rays 15
def bank10576 : Fin 2 → Cell := twoBank p10576 ray10576
theorem signs10576 : ∀ j, Signs p10576 (bank10576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10577 := params 16
abbrev ray10577 := rays 16
def bank10577 : Fin 2 → Cell := twoBank p10577 ray10577
theorem signs10577 : ∀ j, Signs p10577 (bank10577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10578 := params 17
abbrev ray10578 := rays 17
def bank10578 : Fin 2 → Cell := twoBank p10578 ray10578
theorem signs10578 : ∀ j, Signs p10578 (bank10578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10579 := params 18
abbrev ray10579 := rays 18
def bank10579 : Fin 2 → Cell := twoBank p10579 ray10579
theorem signs10579 : ∀ j, Signs p10579 (bank10579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10580 := params 19
abbrev ray10580 := rays 19
def bank10580 : Fin 2 → Cell := twoBank p10580 ray10580
theorem signs10580 : ∀ j, Signs p10580 (bank10580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10581 := params 20
abbrev ray10581 := rays 20
def bank10581 : Fin 2 → Cell := twoBank p10581 ray10581
theorem signs10581 : ∀ j, Signs p10581 (bank10581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10582 := params 21
abbrev ray10582 := rays 21
def bank10582 : Fin 2 → Cell := twoBank p10582 ray10582
theorem signs10582 : ∀ j, Signs p10582 (bank10582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10583 := params 22
abbrev ray10583 := rays 22
def bank10583 : Fin 2 → Cell := twoBank p10583 ray10583
theorem signs10583 : ∀ j, Signs p10583 (bank10583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10584 := params 23
abbrev ray10584 := rays 23
def bank10584 : Fin 2 → Cell := twoBank p10584 ray10584
theorem signs10584 : ∀ j, Signs p10584 (bank10584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10585 := params 24
abbrev ray10585 := rays 24
def bank10585 : Fin 2 → Cell := twoBank p10585 ray10585
theorem signs10585 : ∀ j, Signs p10585 (bank10585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10586 := params 25
abbrev ray10586 := rays 25
def bank10586 : Fin 2 → Cell := twoBank p10586 ray10586
theorem signs10586 : ∀ j, Signs p10586 (bank10586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10587 := params 26
abbrev ray10587 := rays 26
def bank10587 : Fin 2 → Cell := twoBank p10587 ray10587
theorem signs10587 : ∀ j, Signs p10587 (bank10587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10588 := params 27
abbrev ray10588 := rays 27
def bank10588 : Fin 2 → Cell := twoBank p10588 ray10588
theorem signs10588 : ∀ j, Signs p10588 (bank10588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10589 := params 28
abbrev ray10589 := rays 28
def bank10589 : Fin 2 → Cell := twoBank p10589 ray10589
theorem signs10589 : ∀ j, Signs p10589 (bank10589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10590 := params 29
abbrev ray10590 := rays 29
def bank10590 : Fin 2 → Cell := twoBank p10590 ray10590
theorem signs10590 : ∀ j, Signs p10590 (bank10590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10591 := params 30
abbrev ray10591 := rays 30
def bank10591 : Fin 2 → Cell := twoBank p10591 ray10591
theorem signs10591 : ∀ j, Signs p10591 (bank10591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10592 := params 31
abbrev ray10592 := rays 31
def bank10592 : Fin 2 → Cell := twoBank p10592 ray10592
theorem signs10592 : ∀ j, Signs p10592 (bank10592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10561_10592
