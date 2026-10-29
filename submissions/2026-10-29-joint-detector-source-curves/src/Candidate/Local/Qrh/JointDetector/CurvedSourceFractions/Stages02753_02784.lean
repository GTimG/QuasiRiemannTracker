/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02753_02784
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99548760669100,99548561165212,99548361634643,99548162077396,99547962493471,99547762882870,99547563245594,99547363581644,99547163891022,99546964173729,99546764429767,99546564659136,99546364861838,99546165037874,99545965187246,99545765309955,99545565406002,99545365475389,99545165518117,99544965534187,99544765523600,99544565486358,99544365422462,99544165331914,99543965214714,99543765070864,99543564900366,99543364703221,99543164479429,99542964228993,99542763951913,99542563648191,99542363317829]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2752+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2753 := params 0
abbrev ray2753 := rays 0
def bank2753 : Fin 2 → Cell := twoBank p2753 ray2753
theorem signs2753 : ∀ j, Signs p2753 (bank2753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2754 := params 1
abbrev ray2754 := rays 1
def bank2754 : Fin 2 → Cell := twoBank p2754 ray2754
theorem signs2754 : ∀ j, Signs p2754 (bank2754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2755 := params 2
abbrev ray2755 := rays 2
def bank2755 : Fin 2 → Cell := twoBank p2755 ray2755
theorem signs2755 : ∀ j, Signs p2755 (bank2755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2756 := params 3
abbrev ray2756 := rays 3
def bank2756 : Fin 2 → Cell := twoBank p2756 ray2756
theorem signs2756 : ∀ j, Signs p2756 (bank2756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2757 := params 4
abbrev ray2757 := rays 4
def bank2757 : Fin 2 → Cell := twoBank p2757 ray2757
theorem signs2757 : ∀ j, Signs p2757 (bank2757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2758 := params 5
abbrev ray2758 := rays 5
def bank2758 : Fin 2 → Cell := twoBank p2758 ray2758
theorem signs2758 : ∀ j, Signs p2758 (bank2758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2759 := params 6
abbrev ray2759 := rays 6
def bank2759 : Fin 2 → Cell := twoBank p2759 ray2759
theorem signs2759 : ∀ j, Signs p2759 (bank2759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2760 := params 7
abbrev ray2760 := rays 7
def bank2760 : Fin 2 → Cell := twoBank p2760 ray2760
theorem signs2760 : ∀ j, Signs p2760 (bank2760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2761 := params 8
abbrev ray2761 := rays 8
def bank2761 : Fin 2 → Cell := twoBank p2761 ray2761
theorem signs2761 : ∀ j, Signs p2761 (bank2761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2762 := params 9
abbrev ray2762 := rays 9
def bank2762 : Fin 2 → Cell := twoBank p2762 ray2762
theorem signs2762 : ∀ j, Signs p2762 (bank2762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2763 := params 10
abbrev ray2763 := rays 10
def bank2763 : Fin 2 → Cell := twoBank p2763 ray2763
theorem signs2763 : ∀ j, Signs p2763 (bank2763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2764 := params 11
abbrev ray2764 := rays 11
def bank2764 : Fin 2 → Cell := twoBank p2764 ray2764
theorem signs2764 : ∀ j, Signs p2764 (bank2764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2765 := params 12
abbrev ray2765 := rays 12
def bank2765 : Fin 2 → Cell := twoBank p2765 ray2765
theorem signs2765 : ∀ j, Signs p2765 (bank2765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2766 := params 13
abbrev ray2766 := rays 13
def bank2766 : Fin 2 → Cell := twoBank p2766 ray2766
theorem signs2766 : ∀ j, Signs p2766 (bank2766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2767 := params 14
abbrev ray2767 := rays 14
def bank2767 : Fin 2 → Cell := twoBank p2767 ray2767
theorem signs2767 : ∀ j, Signs p2767 (bank2767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2768 := params 15
abbrev ray2768 := rays 15
def bank2768 : Fin 2 → Cell := twoBank p2768 ray2768
theorem signs2768 : ∀ j, Signs p2768 (bank2768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2769 := params 16
abbrev ray2769 := rays 16
def bank2769 : Fin 2 → Cell := twoBank p2769 ray2769
theorem signs2769 : ∀ j, Signs p2769 (bank2769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2770 := params 17
abbrev ray2770 := rays 17
def bank2770 : Fin 2 → Cell := twoBank p2770 ray2770
theorem signs2770 : ∀ j, Signs p2770 (bank2770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2771 := params 18
abbrev ray2771 := rays 18
def bank2771 : Fin 2 → Cell := twoBank p2771 ray2771
theorem signs2771 : ∀ j, Signs p2771 (bank2771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2772 := params 19
abbrev ray2772 := rays 19
def bank2772 : Fin 2 → Cell := twoBank p2772 ray2772
theorem signs2772 : ∀ j, Signs p2772 (bank2772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2773 := params 20
abbrev ray2773 := rays 20
def bank2773 : Fin 2 → Cell := twoBank p2773 ray2773
theorem signs2773 : ∀ j, Signs p2773 (bank2773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2774 := params 21
abbrev ray2774 := rays 21
def bank2774 : Fin 2 → Cell := twoBank p2774 ray2774
theorem signs2774 : ∀ j, Signs p2774 (bank2774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2775 := params 22
abbrev ray2775 := rays 22
def bank2775 : Fin 2 → Cell := twoBank p2775 ray2775
theorem signs2775 : ∀ j, Signs p2775 (bank2775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2776 := params 23
abbrev ray2776 := rays 23
def bank2776 : Fin 2 → Cell := twoBank p2776 ray2776
theorem signs2776 : ∀ j, Signs p2776 (bank2776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2777 := params 24
abbrev ray2777 := rays 24
def bank2777 : Fin 2 → Cell := twoBank p2777 ray2777
theorem signs2777 : ∀ j, Signs p2777 (bank2777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2778 := params 25
abbrev ray2778 := rays 25
def bank2778 : Fin 2 → Cell := twoBank p2778 ray2778
theorem signs2778 : ∀ j, Signs p2778 (bank2778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2779 := params 26
abbrev ray2779 := rays 26
def bank2779 : Fin 2 → Cell := twoBank p2779 ray2779
theorem signs2779 : ∀ j, Signs p2779 (bank2779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2780 := params 27
abbrev ray2780 := rays 27
def bank2780 : Fin 2 → Cell := twoBank p2780 ray2780
theorem signs2780 : ∀ j, Signs p2780 (bank2780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2781 := params 28
abbrev ray2781 := rays 28
def bank2781 : Fin 2 → Cell := twoBank p2781 ray2781
theorem signs2781 : ∀ j, Signs p2781 (bank2781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2782 := params 29
abbrev ray2782 := rays 29
def bank2782 : Fin 2 → Cell := twoBank p2782 ray2782
theorem signs2782 : ∀ j, Signs p2782 (bank2782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2783 := params 30
abbrev ray2783 := rays 30
def bank2783 : Fin 2 → Cell := twoBank p2783 ray2783
theorem signs2783 : ∀ j, Signs p2783 (bank2783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2784 := params 31
abbrev ray2784 := rays 31
def bank2784 : Fin 2 → Cell := twoBank p2784 ray2784
theorem signs2784 : ∀ j, Signs p2784 (bank2784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02753_02784
