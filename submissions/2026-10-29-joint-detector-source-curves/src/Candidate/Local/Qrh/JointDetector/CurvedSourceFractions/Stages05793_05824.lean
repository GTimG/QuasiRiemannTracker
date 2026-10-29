/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05793_05824
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98824633374284,98824358136879,98824082876125,98823807592023,98823532284573,98823256953777,98822981599635,98822706222149,98822430821319,98822155397146,98821879949631,98821604478775,98821328984579,98821053467044,98820777926170,98820502361959,98820226774412,98819951163529,98819675529311,98819399871759,98819124190875,98818848486659,98818572759112,98818297008234,98818021234027,98817745436492,98817469615629,98817193771440,98816917903925,98816642013085,98816366098921,98816090161435,98815814200627]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5792+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5793 := params 0
abbrev ray5793 := rays 0
def bank5793 : Fin 2 → Cell := twoBank p5793 ray5793
theorem signs5793 : ∀ j, Signs p5793 (bank5793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5794 := params 1
abbrev ray5794 := rays 1
def bank5794 : Fin 2 → Cell := twoBank p5794 ray5794
theorem signs5794 : ∀ j, Signs p5794 (bank5794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5795 := params 2
abbrev ray5795 := rays 2
def bank5795 : Fin 2 → Cell := twoBank p5795 ray5795
theorem signs5795 : ∀ j, Signs p5795 (bank5795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5796 := params 3
abbrev ray5796 := rays 3
def bank5796 : Fin 2 → Cell := twoBank p5796 ray5796
theorem signs5796 : ∀ j, Signs p5796 (bank5796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5797 := params 4
abbrev ray5797 := rays 4
def bank5797 : Fin 2 → Cell := twoBank p5797 ray5797
theorem signs5797 : ∀ j, Signs p5797 (bank5797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5798 := params 5
abbrev ray5798 := rays 5
def bank5798 : Fin 2 → Cell := twoBank p5798 ray5798
theorem signs5798 : ∀ j, Signs p5798 (bank5798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5799 := params 6
abbrev ray5799 := rays 6
def bank5799 : Fin 2 → Cell := twoBank p5799 ray5799
theorem signs5799 : ∀ j, Signs p5799 (bank5799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5800 := params 7
abbrev ray5800 := rays 7
def bank5800 : Fin 2 → Cell := twoBank p5800 ray5800
theorem signs5800 : ∀ j, Signs p5800 (bank5800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5801 := params 8
abbrev ray5801 := rays 8
def bank5801 : Fin 2 → Cell := twoBank p5801 ray5801
theorem signs5801 : ∀ j, Signs p5801 (bank5801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5802 := params 9
abbrev ray5802 := rays 9
def bank5802 : Fin 2 → Cell := twoBank p5802 ray5802
theorem signs5802 : ∀ j, Signs p5802 (bank5802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5803 := params 10
abbrev ray5803 := rays 10
def bank5803 : Fin 2 → Cell := twoBank p5803 ray5803
theorem signs5803 : ∀ j, Signs p5803 (bank5803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5804 := params 11
abbrev ray5804 := rays 11
def bank5804 : Fin 2 → Cell := twoBank p5804 ray5804
theorem signs5804 : ∀ j, Signs p5804 (bank5804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5805 := params 12
abbrev ray5805 := rays 12
def bank5805 : Fin 2 → Cell := twoBank p5805 ray5805
theorem signs5805 : ∀ j, Signs p5805 (bank5805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5806 := params 13
abbrev ray5806 := rays 13
def bank5806 : Fin 2 → Cell := twoBank p5806 ray5806
theorem signs5806 : ∀ j, Signs p5806 (bank5806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5807 := params 14
abbrev ray5807 := rays 14
def bank5807 : Fin 2 → Cell := twoBank p5807 ray5807
theorem signs5807 : ∀ j, Signs p5807 (bank5807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5808 := params 15
abbrev ray5808 := rays 15
def bank5808 : Fin 2 → Cell := twoBank p5808 ray5808
theorem signs5808 : ∀ j, Signs p5808 (bank5808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5809 := params 16
abbrev ray5809 := rays 16
def bank5809 : Fin 2 → Cell := twoBank p5809 ray5809
theorem signs5809 : ∀ j, Signs p5809 (bank5809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5810 := params 17
abbrev ray5810 := rays 17
def bank5810 : Fin 2 → Cell := twoBank p5810 ray5810
theorem signs5810 : ∀ j, Signs p5810 (bank5810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5811 := params 18
abbrev ray5811 := rays 18
def bank5811 : Fin 2 → Cell := twoBank p5811 ray5811
theorem signs5811 : ∀ j, Signs p5811 (bank5811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5812 := params 19
abbrev ray5812 := rays 19
def bank5812 : Fin 2 → Cell := twoBank p5812 ray5812
theorem signs5812 : ∀ j, Signs p5812 (bank5812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5813 := params 20
abbrev ray5813 := rays 20
def bank5813 : Fin 2 → Cell := twoBank p5813 ray5813
theorem signs5813 : ∀ j, Signs p5813 (bank5813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5814 := params 21
abbrev ray5814 := rays 21
def bank5814 : Fin 2 → Cell := twoBank p5814 ray5814
theorem signs5814 : ∀ j, Signs p5814 (bank5814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5815 := params 22
abbrev ray5815 := rays 22
def bank5815 : Fin 2 → Cell := twoBank p5815 ray5815
theorem signs5815 : ∀ j, Signs p5815 (bank5815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5816 := params 23
abbrev ray5816 := rays 23
def bank5816 : Fin 2 → Cell := twoBank p5816 ray5816
theorem signs5816 : ∀ j, Signs p5816 (bank5816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5817 := params 24
abbrev ray5817 := rays 24
def bank5817 : Fin 2 → Cell := twoBank p5817 ray5817
theorem signs5817 : ∀ j, Signs p5817 (bank5817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5818 := params 25
abbrev ray5818 := rays 25
def bank5818 : Fin 2 → Cell := twoBank p5818 ray5818
theorem signs5818 : ∀ j, Signs p5818 (bank5818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5819 := params 26
abbrev ray5819 := rays 26
def bank5819 : Fin 2 → Cell := twoBank p5819 ray5819
theorem signs5819 : ∀ j, Signs p5819 (bank5819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5820 := params 27
abbrev ray5820 := rays 27
def bank5820 : Fin 2 → Cell := twoBank p5820 ray5820
theorem signs5820 : ∀ j, Signs p5820 (bank5820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5821 := params 28
abbrev ray5821 := rays 28
def bank5821 : Fin 2 → Cell := twoBank p5821 ray5821
theorem signs5821 : ∀ j, Signs p5821 (bank5821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5822 := params 29
abbrev ray5822 := rays 29
def bank5822 : Fin 2 → Cell := twoBank p5822 ray5822
theorem signs5822 : ∀ j, Signs p5822 (bank5822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5823 := params 30
abbrev ray5823 := rays 30
def bank5823 : Fin 2 → Cell := twoBank p5823 ray5823
theorem signs5823 : ∀ j, Signs p5823 (bank5823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5824 := params 31
abbrev ray5824 := rays 31
def bank5824 : Fin 2 → Cell := twoBank p5824 ray5824
theorem signs5824 : ∀ j, Signs p5824 (bank5824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05793_05824
