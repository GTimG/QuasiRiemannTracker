/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02689_02720
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99561473362964,99561275569347,99561077748966,99560879901821,99560682027914,99560484127247,99560286199820,99560088245635,99559890264694,99559692256997,99559494222546,99559296161343,99559098073388,99558899958683,99558701817229,99558503649028,99558305454081,99558107232389,99557908983954,99557710708777,99557512406859,99557314078201,99557115722805,99556917340672,99556718931804,99556520496202,99556322033867,99556123544800,99555925029003,99555726486477,99555527917223,99555329321243,99555130698538]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2688+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2689 := params 0
abbrev ray2689 := rays 0
def bank2689 : Fin 2 → Cell := twoBank p2689 ray2689
theorem signs2689 : ∀ j, Signs p2689 (bank2689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2690 := params 1
abbrev ray2690 := rays 1
def bank2690 : Fin 2 → Cell := twoBank p2690 ray2690
theorem signs2690 : ∀ j, Signs p2690 (bank2690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2691 := params 2
abbrev ray2691 := rays 2
def bank2691 : Fin 2 → Cell := twoBank p2691 ray2691
theorem signs2691 : ∀ j, Signs p2691 (bank2691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2692 := params 3
abbrev ray2692 := rays 3
def bank2692 : Fin 2 → Cell := twoBank p2692 ray2692
theorem signs2692 : ∀ j, Signs p2692 (bank2692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2693 := params 4
abbrev ray2693 := rays 4
def bank2693 : Fin 2 → Cell := twoBank p2693 ray2693
theorem signs2693 : ∀ j, Signs p2693 (bank2693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2694 := params 5
abbrev ray2694 := rays 5
def bank2694 : Fin 2 → Cell := twoBank p2694 ray2694
theorem signs2694 : ∀ j, Signs p2694 (bank2694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2695 := params 6
abbrev ray2695 := rays 6
def bank2695 : Fin 2 → Cell := twoBank p2695 ray2695
theorem signs2695 : ∀ j, Signs p2695 (bank2695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2696 := params 7
abbrev ray2696 := rays 7
def bank2696 : Fin 2 → Cell := twoBank p2696 ray2696
theorem signs2696 : ∀ j, Signs p2696 (bank2696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2697 := params 8
abbrev ray2697 := rays 8
def bank2697 : Fin 2 → Cell := twoBank p2697 ray2697
theorem signs2697 : ∀ j, Signs p2697 (bank2697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2698 := params 9
abbrev ray2698 := rays 9
def bank2698 : Fin 2 → Cell := twoBank p2698 ray2698
theorem signs2698 : ∀ j, Signs p2698 (bank2698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2699 := params 10
abbrev ray2699 := rays 10
def bank2699 : Fin 2 → Cell := twoBank p2699 ray2699
theorem signs2699 : ∀ j, Signs p2699 (bank2699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2700 := params 11
abbrev ray2700 := rays 11
def bank2700 : Fin 2 → Cell := twoBank p2700 ray2700
theorem signs2700 : ∀ j, Signs p2700 (bank2700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2701 := params 12
abbrev ray2701 := rays 12
def bank2701 : Fin 2 → Cell := twoBank p2701 ray2701
theorem signs2701 : ∀ j, Signs p2701 (bank2701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2702 := params 13
abbrev ray2702 := rays 13
def bank2702 : Fin 2 → Cell := twoBank p2702 ray2702
theorem signs2702 : ∀ j, Signs p2702 (bank2702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2703 := params 14
abbrev ray2703 := rays 14
def bank2703 : Fin 2 → Cell := twoBank p2703 ray2703
theorem signs2703 : ∀ j, Signs p2703 (bank2703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2704 := params 15
abbrev ray2704 := rays 15
def bank2704 : Fin 2 → Cell := twoBank p2704 ray2704
theorem signs2704 : ∀ j, Signs p2704 (bank2704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2705 := params 16
abbrev ray2705 := rays 16
def bank2705 : Fin 2 → Cell := twoBank p2705 ray2705
theorem signs2705 : ∀ j, Signs p2705 (bank2705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2706 := params 17
abbrev ray2706 := rays 17
def bank2706 : Fin 2 → Cell := twoBank p2706 ray2706
theorem signs2706 : ∀ j, Signs p2706 (bank2706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2707 := params 18
abbrev ray2707 := rays 18
def bank2707 : Fin 2 → Cell := twoBank p2707 ray2707
theorem signs2707 : ∀ j, Signs p2707 (bank2707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2708 := params 19
abbrev ray2708 := rays 19
def bank2708 : Fin 2 → Cell := twoBank p2708 ray2708
theorem signs2708 : ∀ j, Signs p2708 (bank2708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2709 := params 20
abbrev ray2709 := rays 20
def bank2709 : Fin 2 → Cell := twoBank p2709 ray2709
theorem signs2709 : ∀ j, Signs p2709 (bank2709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2710 := params 21
abbrev ray2710 := rays 21
def bank2710 : Fin 2 → Cell := twoBank p2710 ray2710
theorem signs2710 : ∀ j, Signs p2710 (bank2710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2711 := params 22
abbrev ray2711 := rays 22
def bank2711 : Fin 2 → Cell := twoBank p2711 ray2711
theorem signs2711 : ∀ j, Signs p2711 (bank2711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2712 := params 23
abbrev ray2712 := rays 23
def bank2712 : Fin 2 → Cell := twoBank p2712 ray2712
theorem signs2712 : ∀ j, Signs p2712 (bank2712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2713 := params 24
abbrev ray2713 := rays 24
def bank2713 : Fin 2 → Cell := twoBank p2713 ray2713
theorem signs2713 : ∀ j, Signs p2713 (bank2713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2714 := params 25
abbrev ray2714 := rays 25
def bank2714 : Fin 2 → Cell := twoBank p2714 ray2714
theorem signs2714 : ∀ j, Signs p2714 (bank2714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2715 := params 26
abbrev ray2715 := rays 26
def bank2715 : Fin 2 → Cell := twoBank p2715 ray2715
theorem signs2715 : ∀ j, Signs p2715 (bank2715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2716 := params 27
abbrev ray2716 := rays 27
def bank2716 : Fin 2 → Cell := twoBank p2716 ray2716
theorem signs2716 : ∀ j, Signs p2716 (bank2716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2717 := params 28
abbrev ray2717 := rays 28
def bank2717 : Fin 2 → Cell := twoBank p2717 ray2717
theorem signs2717 : ∀ j, Signs p2717 (bank2717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2718 := params 29
abbrev ray2718 := rays 29
def bank2718 : Fin 2 → Cell := twoBank p2718 ray2718
theorem signs2718 : ∀ j, Signs p2718 (bank2718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2719 := params 30
abbrev ray2719 := rays 30
def bank2719 : Fin 2 → Cell := twoBank p2719 ray2719
theorem signs2719 : ∀ j, Signs p2719 (bank2719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2720 := params 31
abbrev ray2720 := rays 31
def bank2720 : Fin 2 → Cell := twoBank p2720 ray2720
theorem signs2720 : ∀ j, Signs p2720 (bank2720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02689_02720
