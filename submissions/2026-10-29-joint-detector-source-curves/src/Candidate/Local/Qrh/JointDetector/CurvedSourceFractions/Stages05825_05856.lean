/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05825_05856
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98815814200627,98815538216497,98815262209047,98814986178278,98814710124190,98814434046785,98814157946063,98813881822026,98813605674674,98813329504008,98813053310029,98812777092738,98812500852136,98812224588223,98811948301001,98811671990470,98811395656632,98811119299487,98810842919036,98810566515280,98810290088220,98810013637857,98809737164192,98809460667226,98809184146960,98808907603394,98808631036530,98808354446368,98808077832909,98807801196154,98807524536104,98807247852760,98806971146123]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5824+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5825 := params 0
abbrev ray5825 := rays 0
def bank5825 : Fin 2 → Cell := twoBank p5825 ray5825
theorem signs5825 : ∀ j, Signs p5825 (bank5825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5826 := params 1
abbrev ray5826 := rays 1
def bank5826 : Fin 2 → Cell := twoBank p5826 ray5826
theorem signs5826 : ∀ j, Signs p5826 (bank5826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5827 := params 2
abbrev ray5827 := rays 2
def bank5827 : Fin 2 → Cell := twoBank p5827 ray5827
theorem signs5827 : ∀ j, Signs p5827 (bank5827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5828 := params 3
abbrev ray5828 := rays 3
def bank5828 : Fin 2 → Cell := twoBank p5828 ray5828
theorem signs5828 : ∀ j, Signs p5828 (bank5828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5829 := params 4
abbrev ray5829 := rays 4
def bank5829 : Fin 2 → Cell := twoBank p5829 ray5829
theorem signs5829 : ∀ j, Signs p5829 (bank5829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5830 := params 5
abbrev ray5830 := rays 5
def bank5830 : Fin 2 → Cell := twoBank p5830 ray5830
theorem signs5830 : ∀ j, Signs p5830 (bank5830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5831 := params 6
abbrev ray5831 := rays 6
def bank5831 : Fin 2 → Cell := twoBank p5831 ray5831
theorem signs5831 : ∀ j, Signs p5831 (bank5831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5832 := params 7
abbrev ray5832 := rays 7
def bank5832 : Fin 2 → Cell := twoBank p5832 ray5832
theorem signs5832 : ∀ j, Signs p5832 (bank5832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5833 := params 8
abbrev ray5833 := rays 8
def bank5833 : Fin 2 → Cell := twoBank p5833 ray5833
theorem signs5833 : ∀ j, Signs p5833 (bank5833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5834 := params 9
abbrev ray5834 := rays 9
def bank5834 : Fin 2 → Cell := twoBank p5834 ray5834
theorem signs5834 : ∀ j, Signs p5834 (bank5834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5835 := params 10
abbrev ray5835 := rays 10
def bank5835 : Fin 2 → Cell := twoBank p5835 ray5835
theorem signs5835 : ∀ j, Signs p5835 (bank5835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5836 := params 11
abbrev ray5836 := rays 11
def bank5836 : Fin 2 → Cell := twoBank p5836 ray5836
theorem signs5836 : ∀ j, Signs p5836 (bank5836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5837 := params 12
abbrev ray5837 := rays 12
def bank5837 : Fin 2 → Cell := twoBank p5837 ray5837
theorem signs5837 : ∀ j, Signs p5837 (bank5837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5838 := params 13
abbrev ray5838 := rays 13
def bank5838 : Fin 2 → Cell := twoBank p5838 ray5838
theorem signs5838 : ∀ j, Signs p5838 (bank5838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5839 := params 14
abbrev ray5839 := rays 14
def bank5839 : Fin 2 → Cell := twoBank p5839 ray5839
theorem signs5839 : ∀ j, Signs p5839 (bank5839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5840 := params 15
abbrev ray5840 := rays 15
def bank5840 : Fin 2 → Cell := twoBank p5840 ray5840
theorem signs5840 : ∀ j, Signs p5840 (bank5840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5841 := params 16
abbrev ray5841 := rays 16
def bank5841 : Fin 2 → Cell := twoBank p5841 ray5841
theorem signs5841 : ∀ j, Signs p5841 (bank5841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5842 := params 17
abbrev ray5842 := rays 17
def bank5842 : Fin 2 → Cell := twoBank p5842 ray5842
theorem signs5842 : ∀ j, Signs p5842 (bank5842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5843 := params 18
abbrev ray5843 := rays 18
def bank5843 : Fin 2 → Cell := twoBank p5843 ray5843
theorem signs5843 : ∀ j, Signs p5843 (bank5843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5844 := params 19
abbrev ray5844 := rays 19
def bank5844 : Fin 2 → Cell := twoBank p5844 ray5844
theorem signs5844 : ∀ j, Signs p5844 (bank5844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5845 := params 20
abbrev ray5845 := rays 20
def bank5845 : Fin 2 → Cell := twoBank p5845 ray5845
theorem signs5845 : ∀ j, Signs p5845 (bank5845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5846 := params 21
abbrev ray5846 := rays 21
def bank5846 : Fin 2 → Cell := twoBank p5846 ray5846
theorem signs5846 : ∀ j, Signs p5846 (bank5846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5847 := params 22
abbrev ray5847 := rays 22
def bank5847 : Fin 2 → Cell := twoBank p5847 ray5847
theorem signs5847 : ∀ j, Signs p5847 (bank5847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5848 := params 23
abbrev ray5848 := rays 23
def bank5848 : Fin 2 → Cell := twoBank p5848 ray5848
theorem signs5848 : ∀ j, Signs p5848 (bank5848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5849 := params 24
abbrev ray5849 := rays 24
def bank5849 : Fin 2 → Cell := twoBank p5849 ray5849
theorem signs5849 : ∀ j, Signs p5849 (bank5849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5850 := params 25
abbrev ray5850 := rays 25
def bank5850 : Fin 2 → Cell := twoBank p5850 ray5850
theorem signs5850 : ∀ j, Signs p5850 (bank5850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5851 := params 26
abbrev ray5851 := rays 26
def bank5851 : Fin 2 → Cell := twoBank p5851 ray5851
theorem signs5851 : ∀ j, Signs p5851 (bank5851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5852 := params 27
abbrev ray5852 := rays 27
def bank5852 : Fin 2 → Cell := twoBank p5852 ray5852
theorem signs5852 : ∀ j, Signs p5852 (bank5852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5853 := params 28
abbrev ray5853 := rays 28
def bank5853 : Fin 2 → Cell := twoBank p5853 ray5853
theorem signs5853 : ∀ j, Signs p5853 (bank5853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5854 := params 29
abbrev ray5854 := rays 29
def bank5854 : Fin 2 → Cell := twoBank p5854 ray5854
theorem signs5854 : ∀ j, Signs p5854 (bank5854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5855 := params 30
abbrev ray5855 := rays 30
def bank5855 : Fin 2 → Cell := twoBank p5855 ray5855
theorem signs5855 : ∀ j, Signs p5855 (bank5855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5856 := params 31
abbrev ray5856 := rays 31
def bank5856 : Fin 2 → Cell := twoBank p5856 ray5856
theorem signs5856 : ∀ j, Signs p5856 (bank5856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05825_05856
