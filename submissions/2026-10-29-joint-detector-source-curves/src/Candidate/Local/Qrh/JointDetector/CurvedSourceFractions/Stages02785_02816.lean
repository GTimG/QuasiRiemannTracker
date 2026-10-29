/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02785_02816
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99542363317829,99542162960827,99541962577187,99541762166910,99541561729997,99541361266450,99541160776270,99540960259459,99540759716017,99540559145946,99540358549248,99540157925923,99539957275973,99539756599399,99539555896203,99539355166386,99539154409949,99538953626893,99538752817220,99538551980931,99538351118028,99538150228511,99537949312382,99537748369643,99537547400294,99537346404337,99537145381773,99536944332604,99536743256831,99536542154455,99536341025477,99536139869899,99535938687722]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2784+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2785 := params 0
abbrev ray2785 := rays 0
def bank2785 : Fin 2 → Cell := twoBank p2785 ray2785
theorem signs2785 : ∀ j, Signs p2785 (bank2785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2786 := params 1
abbrev ray2786 := rays 1
def bank2786 : Fin 2 → Cell := twoBank p2786 ray2786
theorem signs2786 : ∀ j, Signs p2786 (bank2786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2787 := params 2
abbrev ray2787 := rays 2
def bank2787 : Fin 2 → Cell := twoBank p2787 ray2787
theorem signs2787 : ∀ j, Signs p2787 (bank2787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2788 := params 3
abbrev ray2788 := rays 3
def bank2788 : Fin 2 → Cell := twoBank p2788 ray2788
theorem signs2788 : ∀ j, Signs p2788 (bank2788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2789 := params 4
abbrev ray2789 := rays 4
def bank2789 : Fin 2 → Cell := twoBank p2789 ray2789
theorem signs2789 : ∀ j, Signs p2789 (bank2789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2790 := params 5
abbrev ray2790 := rays 5
def bank2790 : Fin 2 → Cell := twoBank p2790 ray2790
theorem signs2790 : ∀ j, Signs p2790 (bank2790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2791 := params 6
abbrev ray2791 := rays 6
def bank2791 : Fin 2 → Cell := twoBank p2791 ray2791
theorem signs2791 : ∀ j, Signs p2791 (bank2791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2792 := params 7
abbrev ray2792 := rays 7
def bank2792 : Fin 2 → Cell := twoBank p2792 ray2792
theorem signs2792 : ∀ j, Signs p2792 (bank2792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2793 := params 8
abbrev ray2793 := rays 8
def bank2793 : Fin 2 → Cell := twoBank p2793 ray2793
theorem signs2793 : ∀ j, Signs p2793 (bank2793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2794 := params 9
abbrev ray2794 := rays 9
def bank2794 : Fin 2 → Cell := twoBank p2794 ray2794
theorem signs2794 : ∀ j, Signs p2794 (bank2794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2795 := params 10
abbrev ray2795 := rays 10
def bank2795 : Fin 2 → Cell := twoBank p2795 ray2795
theorem signs2795 : ∀ j, Signs p2795 (bank2795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2796 := params 11
abbrev ray2796 := rays 11
def bank2796 : Fin 2 → Cell := twoBank p2796 ray2796
theorem signs2796 : ∀ j, Signs p2796 (bank2796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2797 := params 12
abbrev ray2797 := rays 12
def bank2797 : Fin 2 → Cell := twoBank p2797 ray2797
theorem signs2797 : ∀ j, Signs p2797 (bank2797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2798 := params 13
abbrev ray2798 := rays 13
def bank2798 : Fin 2 → Cell := twoBank p2798 ray2798
theorem signs2798 : ∀ j, Signs p2798 (bank2798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2799 := params 14
abbrev ray2799 := rays 14
def bank2799 : Fin 2 → Cell := twoBank p2799 ray2799
theorem signs2799 : ∀ j, Signs p2799 (bank2799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2800 := params 15
abbrev ray2800 := rays 15
def bank2800 : Fin 2 → Cell := twoBank p2800 ray2800
theorem signs2800 : ∀ j, Signs p2800 (bank2800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2801 := params 16
abbrev ray2801 := rays 16
def bank2801 : Fin 2 → Cell := twoBank p2801 ray2801
theorem signs2801 : ∀ j, Signs p2801 (bank2801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2802 := params 17
abbrev ray2802 := rays 17
def bank2802 : Fin 2 → Cell := twoBank p2802 ray2802
theorem signs2802 : ∀ j, Signs p2802 (bank2802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2803 := params 18
abbrev ray2803 := rays 18
def bank2803 : Fin 2 → Cell := twoBank p2803 ray2803
theorem signs2803 : ∀ j, Signs p2803 (bank2803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2804 := params 19
abbrev ray2804 := rays 19
def bank2804 : Fin 2 → Cell := twoBank p2804 ray2804
theorem signs2804 : ∀ j, Signs p2804 (bank2804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2805 := params 20
abbrev ray2805 := rays 20
def bank2805 : Fin 2 → Cell := twoBank p2805 ray2805
theorem signs2805 : ∀ j, Signs p2805 (bank2805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2806 := params 21
abbrev ray2806 := rays 21
def bank2806 : Fin 2 → Cell := twoBank p2806 ray2806
theorem signs2806 : ∀ j, Signs p2806 (bank2806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2807 := params 22
abbrev ray2807 := rays 22
def bank2807 : Fin 2 → Cell := twoBank p2807 ray2807
theorem signs2807 : ∀ j, Signs p2807 (bank2807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2808 := params 23
abbrev ray2808 := rays 23
def bank2808 : Fin 2 → Cell := twoBank p2808 ray2808
theorem signs2808 : ∀ j, Signs p2808 (bank2808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2809 := params 24
abbrev ray2809 := rays 24
def bank2809 : Fin 2 → Cell := twoBank p2809 ray2809
theorem signs2809 : ∀ j, Signs p2809 (bank2809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2810 := params 25
abbrev ray2810 := rays 25
def bank2810 : Fin 2 → Cell := twoBank p2810 ray2810
theorem signs2810 : ∀ j, Signs p2810 (bank2810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2811 := params 26
abbrev ray2811 := rays 26
def bank2811 : Fin 2 → Cell := twoBank p2811 ray2811
theorem signs2811 : ∀ j, Signs p2811 (bank2811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2812 := params 27
abbrev ray2812 := rays 27
def bank2812 : Fin 2 → Cell := twoBank p2812 ray2812
theorem signs2812 : ∀ j, Signs p2812 (bank2812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2813 := params 28
abbrev ray2813 := rays 28
def bank2813 : Fin 2 → Cell := twoBank p2813 ray2813
theorem signs2813 : ∀ j, Signs p2813 (bank2813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2814 := params 29
abbrev ray2814 := rays 29
def bank2814 : Fin 2 → Cell := twoBank p2814 ray2814
theorem signs2814 : ∀ j, Signs p2814 (bank2814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2815 := params 30
abbrev ray2815 := rays 30
def bank2815 : Fin 2 → Cell := twoBank p2815 ray2815
theorem signs2815 : ∀ j, Signs p2815 (bank2815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2816 := params 31
abbrev ray2816 := rays 31
def bank2816 : Fin 2 → Cell := twoBank p2816 ray2816
theorem signs2816 : ∀ j, Signs p2816 (bank2816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02785_02816
