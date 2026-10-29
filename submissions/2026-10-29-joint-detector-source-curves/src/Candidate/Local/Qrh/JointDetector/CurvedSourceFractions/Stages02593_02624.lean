/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02593_02624
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99580336731761,99580141513747,99579946268840,99579750997042,99579555698354,99579360372777,99579165020313,99578969640963,99578774234728,99578578801610,99578383341610,99578187854730,99577992340970,99577796800332,99577601232818,99577405638429,99577210017166,99577014369030,99576818694023,99576622992146,99576427263400,99576231507787,99576035725308,99575839915965,99575644079759,99575448216691,99575252326762,99575056409974,99574860466328,99574664495826,99574468498469,99574272474258,99574076423194]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2592+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2593 := params 0
abbrev ray2593 := rays 0
def bank2593 : Fin 2 → Cell := twoBank p2593 ray2593
theorem signs2593 : ∀ j, Signs p2593 (bank2593 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2594 := params 1
abbrev ray2594 := rays 1
def bank2594 : Fin 2 → Cell := twoBank p2594 ray2594
theorem signs2594 : ∀ j, Signs p2594 (bank2594 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2595 := params 2
abbrev ray2595 := rays 2
def bank2595 : Fin 2 → Cell := twoBank p2595 ray2595
theorem signs2595 : ∀ j, Signs p2595 (bank2595 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2596 := params 3
abbrev ray2596 := rays 3
def bank2596 : Fin 2 → Cell := twoBank p2596 ray2596
theorem signs2596 : ∀ j, Signs p2596 (bank2596 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2597 := params 4
abbrev ray2597 := rays 4
def bank2597 : Fin 2 → Cell := twoBank p2597 ray2597
theorem signs2597 : ∀ j, Signs p2597 (bank2597 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2598 := params 5
abbrev ray2598 := rays 5
def bank2598 : Fin 2 → Cell := twoBank p2598 ray2598
theorem signs2598 : ∀ j, Signs p2598 (bank2598 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2599 := params 6
abbrev ray2599 := rays 6
def bank2599 : Fin 2 → Cell := twoBank p2599 ray2599
theorem signs2599 : ∀ j, Signs p2599 (bank2599 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2600 := params 7
abbrev ray2600 := rays 7
def bank2600 : Fin 2 → Cell := twoBank p2600 ray2600
theorem signs2600 : ∀ j, Signs p2600 (bank2600 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2601 := params 8
abbrev ray2601 := rays 8
def bank2601 : Fin 2 → Cell := twoBank p2601 ray2601
theorem signs2601 : ∀ j, Signs p2601 (bank2601 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2602 := params 9
abbrev ray2602 := rays 9
def bank2602 : Fin 2 → Cell := twoBank p2602 ray2602
theorem signs2602 : ∀ j, Signs p2602 (bank2602 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2603 := params 10
abbrev ray2603 := rays 10
def bank2603 : Fin 2 → Cell := twoBank p2603 ray2603
theorem signs2603 : ∀ j, Signs p2603 (bank2603 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2604 := params 11
abbrev ray2604 := rays 11
def bank2604 : Fin 2 → Cell := twoBank p2604 ray2604
theorem signs2604 : ∀ j, Signs p2604 (bank2604 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2605 := params 12
abbrev ray2605 := rays 12
def bank2605 : Fin 2 → Cell := twoBank p2605 ray2605
theorem signs2605 : ∀ j, Signs p2605 (bank2605 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2606 := params 13
abbrev ray2606 := rays 13
def bank2606 : Fin 2 → Cell := twoBank p2606 ray2606
theorem signs2606 : ∀ j, Signs p2606 (bank2606 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2607 := params 14
abbrev ray2607 := rays 14
def bank2607 : Fin 2 → Cell := twoBank p2607 ray2607
theorem signs2607 : ∀ j, Signs p2607 (bank2607 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2608 := params 15
abbrev ray2608 := rays 15
def bank2608 : Fin 2 → Cell := twoBank p2608 ray2608
theorem signs2608 : ∀ j, Signs p2608 (bank2608 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2609 := params 16
abbrev ray2609 := rays 16
def bank2609 : Fin 2 → Cell := twoBank p2609 ray2609
theorem signs2609 : ∀ j, Signs p2609 (bank2609 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2610 := params 17
abbrev ray2610 := rays 17
def bank2610 : Fin 2 → Cell := twoBank p2610 ray2610
theorem signs2610 : ∀ j, Signs p2610 (bank2610 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2611 := params 18
abbrev ray2611 := rays 18
def bank2611 : Fin 2 → Cell := twoBank p2611 ray2611
theorem signs2611 : ∀ j, Signs p2611 (bank2611 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2612 := params 19
abbrev ray2612 := rays 19
def bank2612 : Fin 2 → Cell := twoBank p2612 ray2612
theorem signs2612 : ∀ j, Signs p2612 (bank2612 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2613 := params 20
abbrev ray2613 := rays 20
def bank2613 : Fin 2 → Cell := twoBank p2613 ray2613
theorem signs2613 : ∀ j, Signs p2613 (bank2613 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2614 := params 21
abbrev ray2614 := rays 21
def bank2614 : Fin 2 → Cell := twoBank p2614 ray2614
theorem signs2614 : ∀ j, Signs p2614 (bank2614 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2615 := params 22
abbrev ray2615 := rays 22
def bank2615 : Fin 2 → Cell := twoBank p2615 ray2615
theorem signs2615 : ∀ j, Signs p2615 (bank2615 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2616 := params 23
abbrev ray2616 := rays 23
def bank2616 : Fin 2 → Cell := twoBank p2616 ray2616
theorem signs2616 : ∀ j, Signs p2616 (bank2616 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2617 := params 24
abbrev ray2617 := rays 24
def bank2617 : Fin 2 → Cell := twoBank p2617 ray2617
theorem signs2617 : ∀ j, Signs p2617 (bank2617 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2618 := params 25
abbrev ray2618 := rays 25
def bank2618 : Fin 2 → Cell := twoBank p2618 ray2618
theorem signs2618 : ∀ j, Signs p2618 (bank2618 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2619 := params 26
abbrev ray2619 := rays 26
def bank2619 : Fin 2 → Cell := twoBank p2619 ray2619
theorem signs2619 : ∀ j, Signs p2619 (bank2619 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2620 := params 27
abbrev ray2620 := rays 27
def bank2620 : Fin 2 → Cell := twoBank p2620 ray2620
theorem signs2620 : ∀ j, Signs p2620 (bank2620 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2621 := params 28
abbrev ray2621 := rays 28
def bank2621 : Fin 2 → Cell := twoBank p2621 ray2621
theorem signs2621 : ∀ j, Signs p2621 (bank2621 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2622 := params 29
abbrev ray2622 := rays 29
def bank2622 : Fin 2 → Cell := twoBank p2622 ray2622
theorem signs2622 : ∀ j, Signs p2622 (bank2622 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2623 := params 30
abbrev ray2623 := rays 30
def bank2623 : Fin 2 → Cell := twoBank p2623 ray2623
theorem signs2623 : ∀ j, Signs p2623 (bank2623 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2624 := params 31
abbrev ray2624 := rays 31
def bank2624 : Fin 2 → Cell := twoBank p2624 ray2624
theorem signs2624 : ∀ j, Signs p2624 (bank2624 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02593_02624
