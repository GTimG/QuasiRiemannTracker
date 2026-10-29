/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08801_08832
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97894892388516,97894550574986,97894208740406,97893866884776,97893525008097,97893183110369,97892841191593,97892499251770,97892157290900,97891815308984,97891473306023,97891131282017,97890789236967,97890447170874,97890105083738,97889762975560,97889420846340,97889078696079,97888736524778,97888394332437,97888052119057,97887709884639,97887367629183,97887025352690,97886683055161,97886340736596,97885998396995,97885656036360,97885313654691,97884971251989,97884628828254,97884286383487,97883943917689]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8800+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8801 := params 0
abbrev ray8801 := rays 0
def bank8801 : Fin 2 → Cell := twoBank p8801 ray8801
theorem signs8801 : ∀ j, Signs p8801 (bank8801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8802 := params 1
abbrev ray8802 := rays 1
def bank8802 : Fin 2 → Cell := twoBank p8802 ray8802
theorem signs8802 : ∀ j, Signs p8802 (bank8802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8803 := params 2
abbrev ray8803 := rays 2
def bank8803 : Fin 2 → Cell := twoBank p8803 ray8803
theorem signs8803 : ∀ j, Signs p8803 (bank8803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8804 := params 3
abbrev ray8804 := rays 3
def bank8804 : Fin 2 → Cell := twoBank p8804 ray8804
theorem signs8804 : ∀ j, Signs p8804 (bank8804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8805 := params 4
abbrev ray8805 := rays 4
def bank8805 : Fin 2 → Cell := twoBank p8805 ray8805
theorem signs8805 : ∀ j, Signs p8805 (bank8805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8806 := params 5
abbrev ray8806 := rays 5
def bank8806 : Fin 2 → Cell := twoBank p8806 ray8806
theorem signs8806 : ∀ j, Signs p8806 (bank8806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8807 := params 6
abbrev ray8807 := rays 6
def bank8807 : Fin 2 → Cell := twoBank p8807 ray8807
theorem signs8807 : ∀ j, Signs p8807 (bank8807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8808 := params 7
abbrev ray8808 := rays 7
def bank8808 : Fin 2 → Cell := twoBank p8808 ray8808
theorem signs8808 : ∀ j, Signs p8808 (bank8808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8809 := params 8
abbrev ray8809 := rays 8
def bank8809 : Fin 2 → Cell := twoBank p8809 ray8809
theorem signs8809 : ∀ j, Signs p8809 (bank8809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8810 := params 9
abbrev ray8810 := rays 9
def bank8810 : Fin 2 → Cell := twoBank p8810 ray8810
theorem signs8810 : ∀ j, Signs p8810 (bank8810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8811 := params 10
abbrev ray8811 := rays 10
def bank8811 : Fin 2 → Cell := twoBank p8811 ray8811
theorem signs8811 : ∀ j, Signs p8811 (bank8811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8812 := params 11
abbrev ray8812 := rays 11
def bank8812 : Fin 2 → Cell := twoBank p8812 ray8812
theorem signs8812 : ∀ j, Signs p8812 (bank8812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8813 := params 12
abbrev ray8813 := rays 12
def bank8813 : Fin 2 → Cell := twoBank p8813 ray8813
theorem signs8813 : ∀ j, Signs p8813 (bank8813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8814 := params 13
abbrev ray8814 := rays 13
def bank8814 : Fin 2 → Cell := twoBank p8814 ray8814
theorem signs8814 : ∀ j, Signs p8814 (bank8814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8815 := params 14
abbrev ray8815 := rays 14
def bank8815 : Fin 2 → Cell := twoBank p8815 ray8815
theorem signs8815 : ∀ j, Signs p8815 (bank8815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8816 := params 15
abbrev ray8816 := rays 15
def bank8816 : Fin 2 → Cell := twoBank p8816 ray8816
theorem signs8816 : ∀ j, Signs p8816 (bank8816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8817 := params 16
abbrev ray8817 := rays 16
def bank8817 : Fin 2 → Cell := twoBank p8817 ray8817
theorem signs8817 : ∀ j, Signs p8817 (bank8817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8818 := params 17
abbrev ray8818 := rays 17
def bank8818 : Fin 2 → Cell := twoBank p8818 ray8818
theorem signs8818 : ∀ j, Signs p8818 (bank8818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8819 := params 18
abbrev ray8819 := rays 18
def bank8819 : Fin 2 → Cell := twoBank p8819 ray8819
theorem signs8819 : ∀ j, Signs p8819 (bank8819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8820 := params 19
abbrev ray8820 := rays 19
def bank8820 : Fin 2 → Cell := twoBank p8820 ray8820
theorem signs8820 : ∀ j, Signs p8820 (bank8820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8821 := params 20
abbrev ray8821 := rays 20
def bank8821 : Fin 2 → Cell := twoBank p8821 ray8821
theorem signs8821 : ∀ j, Signs p8821 (bank8821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8822 := params 21
abbrev ray8822 := rays 21
def bank8822 : Fin 2 → Cell := twoBank p8822 ray8822
theorem signs8822 : ∀ j, Signs p8822 (bank8822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8823 := params 22
abbrev ray8823 := rays 22
def bank8823 : Fin 2 → Cell := twoBank p8823 ray8823
theorem signs8823 : ∀ j, Signs p8823 (bank8823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8824 := params 23
abbrev ray8824 := rays 23
def bank8824 : Fin 2 → Cell := twoBank p8824 ray8824
theorem signs8824 : ∀ j, Signs p8824 (bank8824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8825 := params 24
abbrev ray8825 := rays 24
def bank8825 : Fin 2 → Cell := twoBank p8825 ray8825
theorem signs8825 : ∀ j, Signs p8825 (bank8825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8826 := params 25
abbrev ray8826 := rays 25
def bank8826 : Fin 2 → Cell := twoBank p8826 ray8826
theorem signs8826 : ∀ j, Signs p8826 (bank8826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8827 := params 26
abbrev ray8827 := rays 26
def bank8827 : Fin 2 → Cell := twoBank p8827 ray8827
theorem signs8827 : ∀ j, Signs p8827 (bank8827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8828 := params 27
abbrev ray8828 := rays 27
def bank8828 : Fin 2 → Cell := twoBank p8828 ray8828
theorem signs8828 : ∀ j, Signs p8828 (bank8828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8829 := params 28
abbrev ray8829 := rays 28
def bank8829 : Fin 2 → Cell := twoBank p8829 ray8829
theorem signs8829 : ∀ j, Signs p8829 (bank8829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8830 := params 29
abbrev ray8830 := rays 29
def bank8830 : Fin 2 → Cell := twoBank p8830 ray8830
theorem signs8830 : ∀ j, Signs p8830 (bank8830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8831 := params 30
abbrev ray8831 := rays 30
def bank8831 : Fin 2 → Cell := twoBank p8831 ray8831
theorem signs8831 : ∀ j, Signs p8831 (bank8831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8832 := params 31
abbrev ray8832 := rays 31
def bank8832 : Fin 2 → Cell := twoBank p8832 ray8832
theorem signs8832 : ∀ j, Signs p8832 (bank8832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08801_08832
