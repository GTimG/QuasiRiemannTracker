/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11809_11840
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96774166432801,96773763869255,96773361286270,96772958683847,96772556061986,96772153420687,96771750759951,96771348079778,96770945380169,96770542661124,96770139922644,96769737164729,96769334387379,96768931590595,96768528774378,96768125938727,96767723083644,96767320209128,96766917315181,96766514401802,96766111468992,96765708516752,96765305545082,96764902553982,96764499543453,96764096513495,96763693464109,96763290395295,96762887307053,96762484199384,96762081072289,96761677925768,96761274759821]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11808+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11809 := params 0
abbrev ray11809 := rays 0
def bank11809 : Fin 2 → Cell := twoBank p11809 ray11809
theorem signs11809 : ∀ j, Signs p11809 (bank11809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11810 := params 1
abbrev ray11810 := rays 1
def bank11810 : Fin 2 → Cell := twoBank p11810 ray11810
theorem signs11810 : ∀ j, Signs p11810 (bank11810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11811 := params 2
abbrev ray11811 := rays 2
def bank11811 : Fin 2 → Cell := twoBank p11811 ray11811
theorem signs11811 : ∀ j, Signs p11811 (bank11811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11812 := params 3
abbrev ray11812 := rays 3
def bank11812 : Fin 2 → Cell := twoBank p11812 ray11812
theorem signs11812 : ∀ j, Signs p11812 (bank11812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11813 := params 4
abbrev ray11813 := rays 4
def bank11813 : Fin 2 → Cell := twoBank p11813 ray11813
theorem signs11813 : ∀ j, Signs p11813 (bank11813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11814 := params 5
abbrev ray11814 := rays 5
def bank11814 : Fin 2 → Cell := twoBank p11814 ray11814
theorem signs11814 : ∀ j, Signs p11814 (bank11814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11815 := params 6
abbrev ray11815 := rays 6
def bank11815 : Fin 2 → Cell := twoBank p11815 ray11815
theorem signs11815 : ∀ j, Signs p11815 (bank11815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11816 := params 7
abbrev ray11816 := rays 7
def bank11816 : Fin 2 → Cell := twoBank p11816 ray11816
theorem signs11816 : ∀ j, Signs p11816 (bank11816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11817 := params 8
abbrev ray11817 := rays 8
def bank11817 : Fin 2 → Cell := twoBank p11817 ray11817
theorem signs11817 : ∀ j, Signs p11817 (bank11817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11818 := params 9
abbrev ray11818 := rays 9
def bank11818 : Fin 2 → Cell := twoBank p11818 ray11818
theorem signs11818 : ∀ j, Signs p11818 (bank11818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11819 := params 10
abbrev ray11819 := rays 10
def bank11819 : Fin 2 → Cell := twoBank p11819 ray11819
theorem signs11819 : ∀ j, Signs p11819 (bank11819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11820 := params 11
abbrev ray11820 := rays 11
def bank11820 : Fin 2 → Cell := twoBank p11820 ray11820
theorem signs11820 : ∀ j, Signs p11820 (bank11820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11821 := params 12
abbrev ray11821 := rays 12
def bank11821 : Fin 2 → Cell := twoBank p11821 ray11821
theorem signs11821 : ∀ j, Signs p11821 (bank11821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11822 := params 13
abbrev ray11822 := rays 13
def bank11822 : Fin 2 → Cell := twoBank p11822 ray11822
theorem signs11822 : ∀ j, Signs p11822 (bank11822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11823 := params 14
abbrev ray11823 := rays 14
def bank11823 : Fin 2 → Cell := twoBank p11823 ray11823
theorem signs11823 : ∀ j, Signs p11823 (bank11823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11824 := params 15
abbrev ray11824 := rays 15
def bank11824 : Fin 2 → Cell := twoBank p11824 ray11824
theorem signs11824 : ∀ j, Signs p11824 (bank11824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11825 := params 16
abbrev ray11825 := rays 16
def bank11825 : Fin 2 → Cell := twoBank p11825 ray11825
theorem signs11825 : ∀ j, Signs p11825 (bank11825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11826 := params 17
abbrev ray11826 := rays 17
def bank11826 : Fin 2 → Cell := twoBank p11826 ray11826
theorem signs11826 : ∀ j, Signs p11826 (bank11826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11827 := params 18
abbrev ray11827 := rays 18
def bank11827 : Fin 2 → Cell := twoBank p11827 ray11827
theorem signs11827 : ∀ j, Signs p11827 (bank11827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11828 := params 19
abbrev ray11828 := rays 19
def bank11828 : Fin 2 → Cell := twoBank p11828 ray11828
theorem signs11828 : ∀ j, Signs p11828 (bank11828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11829 := params 20
abbrev ray11829 := rays 20
def bank11829 : Fin 2 → Cell := twoBank p11829 ray11829
theorem signs11829 : ∀ j, Signs p11829 (bank11829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11830 := params 21
abbrev ray11830 := rays 21
def bank11830 : Fin 2 → Cell := twoBank p11830 ray11830
theorem signs11830 : ∀ j, Signs p11830 (bank11830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11831 := params 22
abbrev ray11831 := rays 22
def bank11831 : Fin 2 → Cell := twoBank p11831 ray11831
theorem signs11831 : ∀ j, Signs p11831 (bank11831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11832 := params 23
abbrev ray11832 := rays 23
def bank11832 : Fin 2 → Cell := twoBank p11832 ray11832
theorem signs11832 : ∀ j, Signs p11832 (bank11832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11833 := params 24
abbrev ray11833 := rays 24
def bank11833 : Fin 2 → Cell := twoBank p11833 ray11833
theorem signs11833 : ∀ j, Signs p11833 (bank11833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11834 := params 25
abbrev ray11834 := rays 25
def bank11834 : Fin 2 → Cell := twoBank p11834 ray11834
theorem signs11834 : ∀ j, Signs p11834 (bank11834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11835 := params 26
abbrev ray11835 := rays 26
def bank11835 : Fin 2 → Cell := twoBank p11835 ray11835
theorem signs11835 : ∀ j, Signs p11835 (bank11835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11836 := params 27
abbrev ray11836 := rays 27
def bank11836 : Fin 2 → Cell := twoBank p11836 ray11836
theorem signs11836 : ∀ j, Signs p11836 (bank11836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11837 := params 28
abbrev ray11837 := rays 28
def bank11837 : Fin 2 → Cell := twoBank p11837 ray11837
theorem signs11837 : ∀ j, Signs p11837 (bank11837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11838 := params 29
abbrev ray11838 := rays 29
def bank11838 : Fin 2 → Cell := twoBank p11838 ray11838
theorem signs11838 : ∀ j, Signs p11838 (bank11838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11839 := params 30
abbrev ray11839 := rays 30
def bank11839 : Fin 2 → Cell := twoBank p11839 ray11839
theorem signs11839 : ∀ j, Signs p11839 (bank11839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11840 := params 31
abbrev ray11840 := rays 31
def bank11840 : Fin 2 → Cell := twoBank p11840 ray11840
theorem signs11840 : ∀ j, Signs p11840 (bank11840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11809_11840
