/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02625_02656
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99574076423194,99573880345279,99573684240514,99573488108901,99573291950441,99573095765135,99572899552984,99572703313990,99572507048154,99572310755478,99572114435963,99571918089610,99571721716420,99571525316395,99571328889537,99571132435846,99570935955324,99570739447972,99570542913792,99570346352785,99570149764952,99569953150294,99569756508813,99569559840510,99569363145387,99569166423445,99568969674685,99568772899109,99568576096717,99568379267512,99568182411494,99567985528665,99567788619026]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2624+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2625 := params 0
abbrev ray2625 := rays 0
def bank2625 : Fin 2 → Cell := twoBank p2625 ray2625
theorem signs2625 : ∀ j, Signs p2625 (bank2625 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2626 := params 1
abbrev ray2626 := rays 1
def bank2626 : Fin 2 → Cell := twoBank p2626 ray2626
theorem signs2626 : ∀ j, Signs p2626 (bank2626 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2627 := params 2
abbrev ray2627 := rays 2
def bank2627 : Fin 2 → Cell := twoBank p2627 ray2627
theorem signs2627 : ∀ j, Signs p2627 (bank2627 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2628 := params 3
abbrev ray2628 := rays 3
def bank2628 : Fin 2 → Cell := twoBank p2628 ray2628
theorem signs2628 : ∀ j, Signs p2628 (bank2628 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2629 := params 4
abbrev ray2629 := rays 4
def bank2629 : Fin 2 → Cell := twoBank p2629 ray2629
theorem signs2629 : ∀ j, Signs p2629 (bank2629 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2630 := params 5
abbrev ray2630 := rays 5
def bank2630 : Fin 2 → Cell := twoBank p2630 ray2630
theorem signs2630 : ∀ j, Signs p2630 (bank2630 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2631 := params 6
abbrev ray2631 := rays 6
def bank2631 : Fin 2 → Cell := twoBank p2631 ray2631
theorem signs2631 : ∀ j, Signs p2631 (bank2631 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2632 := params 7
abbrev ray2632 := rays 7
def bank2632 : Fin 2 → Cell := twoBank p2632 ray2632
theorem signs2632 : ∀ j, Signs p2632 (bank2632 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2633 := params 8
abbrev ray2633 := rays 8
def bank2633 : Fin 2 → Cell := twoBank p2633 ray2633
theorem signs2633 : ∀ j, Signs p2633 (bank2633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2634 := params 9
abbrev ray2634 := rays 9
def bank2634 : Fin 2 → Cell := twoBank p2634 ray2634
theorem signs2634 : ∀ j, Signs p2634 (bank2634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2635 := params 10
abbrev ray2635 := rays 10
def bank2635 : Fin 2 → Cell := twoBank p2635 ray2635
theorem signs2635 : ∀ j, Signs p2635 (bank2635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2636 := params 11
abbrev ray2636 := rays 11
def bank2636 : Fin 2 → Cell := twoBank p2636 ray2636
theorem signs2636 : ∀ j, Signs p2636 (bank2636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2637 := params 12
abbrev ray2637 := rays 12
def bank2637 : Fin 2 → Cell := twoBank p2637 ray2637
theorem signs2637 : ∀ j, Signs p2637 (bank2637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2638 := params 13
abbrev ray2638 := rays 13
def bank2638 : Fin 2 → Cell := twoBank p2638 ray2638
theorem signs2638 : ∀ j, Signs p2638 (bank2638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2639 := params 14
abbrev ray2639 := rays 14
def bank2639 : Fin 2 → Cell := twoBank p2639 ray2639
theorem signs2639 : ∀ j, Signs p2639 (bank2639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2640 := params 15
abbrev ray2640 := rays 15
def bank2640 : Fin 2 → Cell := twoBank p2640 ray2640
theorem signs2640 : ∀ j, Signs p2640 (bank2640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2641 := params 16
abbrev ray2641 := rays 16
def bank2641 : Fin 2 → Cell := twoBank p2641 ray2641
theorem signs2641 : ∀ j, Signs p2641 (bank2641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2642 := params 17
abbrev ray2642 := rays 17
def bank2642 : Fin 2 → Cell := twoBank p2642 ray2642
theorem signs2642 : ∀ j, Signs p2642 (bank2642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2643 := params 18
abbrev ray2643 := rays 18
def bank2643 : Fin 2 → Cell := twoBank p2643 ray2643
theorem signs2643 : ∀ j, Signs p2643 (bank2643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2644 := params 19
abbrev ray2644 := rays 19
def bank2644 : Fin 2 → Cell := twoBank p2644 ray2644
theorem signs2644 : ∀ j, Signs p2644 (bank2644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2645 := params 20
abbrev ray2645 := rays 20
def bank2645 : Fin 2 → Cell := twoBank p2645 ray2645
theorem signs2645 : ∀ j, Signs p2645 (bank2645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2646 := params 21
abbrev ray2646 := rays 21
def bank2646 : Fin 2 → Cell := twoBank p2646 ray2646
theorem signs2646 : ∀ j, Signs p2646 (bank2646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2647 := params 22
abbrev ray2647 := rays 22
def bank2647 : Fin 2 → Cell := twoBank p2647 ray2647
theorem signs2647 : ∀ j, Signs p2647 (bank2647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2648 := params 23
abbrev ray2648 := rays 23
def bank2648 : Fin 2 → Cell := twoBank p2648 ray2648
theorem signs2648 : ∀ j, Signs p2648 (bank2648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2649 := params 24
abbrev ray2649 := rays 24
def bank2649 : Fin 2 → Cell := twoBank p2649 ray2649
theorem signs2649 : ∀ j, Signs p2649 (bank2649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2650 := params 25
abbrev ray2650 := rays 25
def bank2650 : Fin 2 → Cell := twoBank p2650 ray2650
theorem signs2650 : ∀ j, Signs p2650 (bank2650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2651 := params 26
abbrev ray2651 := rays 26
def bank2651 : Fin 2 → Cell := twoBank p2651 ray2651
theorem signs2651 : ∀ j, Signs p2651 (bank2651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2652 := params 27
abbrev ray2652 := rays 27
def bank2652 : Fin 2 → Cell := twoBank p2652 ray2652
theorem signs2652 : ∀ j, Signs p2652 (bank2652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2653 := params 28
abbrev ray2653 := rays 28
def bank2653 : Fin 2 → Cell := twoBank p2653 ray2653
theorem signs2653 : ∀ j, Signs p2653 (bank2653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2654 := params 29
abbrev ray2654 := rays 29
def bank2654 : Fin 2 → Cell := twoBank p2654 ray2654
theorem signs2654 : ∀ j, Signs p2654 (bank2654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2655 := params 30
abbrev ray2655 := rays 30
def bank2655 : Fin 2 → Cell := twoBank p2655 ray2655
theorem signs2655 : ∀ j, Signs p2655 (bank2655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2656 := params 31
abbrev ray2656 := rays 31
def bank2656 : Fin 2 → Cell := twoBank p2656 ray2656
theorem signs2656 : ∀ j, Signs p2656 (bank2656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02625_02656
