/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09793_09824
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97545566816654,97545204422730,97544842008353,97544479573523,97544117118241,97543754642507,97543392146322,97543029629687,97542667092602,97542304535068,97541941957085,97541579358654,97541216739775,97540854100449,97540491440676,97540128760458,97539766059794,97539403338685,97539040597132,97538677835136,97538315052696,97537952249814,97537589426490,97537226582725,97536863718519,97536500833872,97536137928786,97535775003261,97535412057297,97535049090895,97534686104056,97534323096780,97533960069067]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9792+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9793 := params 0
abbrev ray9793 := rays 0
def bank9793 : Fin 2 → Cell := twoBank p9793 ray9793
theorem signs9793 : ∀ j, Signs p9793 (bank9793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9794 := params 1
abbrev ray9794 := rays 1
def bank9794 : Fin 2 → Cell := twoBank p9794 ray9794
theorem signs9794 : ∀ j, Signs p9794 (bank9794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9795 := params 2
abbrev ray9795 := rays 2
def bank9795 : Fin 2 → Cell := twoBank p9795 ray9795
theorem signs9795 : ∀ j, Signs p9795 (bank9795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9796 := params 3
abbrev ray9796 := rays 3
def bank9796 : Fin 2 → Cell := twoBank p9796 ray9796
theorem signs9796 : ∀ j, Signs p9796 (bank9796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9797 := params 4
abbrev ray9797 := rays 4
def bank9797 : Fin 2 → Cell := twoBank p9797 ray9797
theorem signs9797 : ∀ j, Signs p9797 (bank9797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9798 := params 5
abbrev ray9798 := rays 5
def bank9798 : Fin 2 → Cell := twoBank p9798 ray9798
theorem signs9798 : ∀ j, Signs p9798 (bank9798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9799 := params 6
abbrev ray9799 := rays 6
def bank9799 : Fin 2 → Cell := twoBank p9799 ray9799
theorem signs9799 : ∀ j, Signs p9799 (bank9799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9800 := params 7
abbrev ray9800 := rays 7
def bank9800 : Fin 2 → Cell := twoBank p9800 ray9800
theorem signs9800 : ∀ j, Signs p9800 (bank9800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9801 := params 8
abbrev ray9801 := rays 8
def bank9801 : Fin 2 → Cell := twoBank p9801 ray9801
theorem signs9801 : ∀ j, Signs p9801 (bank9801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9802 := params 9
abbrev ray9802 := rays 9
def bank9802 : Fin 2 → Cell := twoBank p9802 ray9802
theorem signs9802 : ∀ j, Signs p9802 (bank9802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9803 := params 10
abbrev ray9803 := rays 10
def bank9803 : Fin 2 → Cell := twoBank p9803 ray9803
theorem signs9803 : ∀ j, Signs p9803 (bank9803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9804 := params 11
abbrev ray9804 := rays 11
def bank9804 : Fin 2 → Cell := twoBank p9804 ray9804
theorem signs9804 : ∀ j, Signs p9804 (bank9804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9805 := params 12
abbrev ray9805 := rays 12
def bank9805 : Fin 2 → Cell := twoBank p9805 ray9805
theorem signs9805 : ∀ j, Signs p9805 (bank9805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9806 := params 13
abbrev ray9806 := rays 13
def bank9806 : Fin 2 → Cell := twoBank p9806 ray9806
theorem signs9806 : ∀ j, Signs p9806 (bank9806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9807 := params 14
abbrev ray9807 := rays 14
def bank9807 : Fin 2 → Cell := twoBank p9807 ray9807
theorem signs9807 : ∀ j, Signs p9807 (bank9807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9808 := params 15
abbrev ray9808 := rays 15
def bank9808 : Fin 2 → Cell := twoBank p9808 ray9808
theorem signs9808 : ∀ j, Signs p9808 (bank9808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9809 := params 16
abbrev ray9809 := rays 16
def bank9809 : Fin 2 → Cell := twoBank p9809 ray9809
theorem signs9809 : ∀ j, Signs p9809 (bank9809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9810 := params 17
abbrev ray9810 := rays 17
def bank9810 : Fin 2 → Cell := twoBank p9810 ray9810
theorem signs9810 : ∀ j, Signs p9810 (bank9810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9811 := params 18
abbrev ray9811 := rays 18
def bank9811 : Fin 2 → Cell := twoBank p9811 ray9811
theorem signs9811 : ∀ j, Signs p9811 (bank9811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9812 := params 19
abbrev ray9812 := rays 19
def bank9812 : Fin 2 → Cell := twoBank p9812 ray9812
theorem signs9812 : ∀ j, Signs p9812 (bank9812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9813 := params 20
abbrev ray9813 := rays 20
def bank9813 : Fin 2 → Cell := twoBank p9813 ray9813
theorem signs9813 : ∀ j, Signs p9813 (bank9813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9814 := params 21
abbrev ray9814 := rays 21
def bank9814 : Fin 2 → Cell := twoBank p9814 ray9814
theorem signs9814 : ∀ j, Signs p9814 (bank9814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9815 := params 22
abbrev ray9815 := rays 22
def bank9815 : Fin 2 → Cell := twoBank p9815 ray9815
theorem signs9815 : ∀ j, Signs p9815 (bank9815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9816 := params 23
abbrev ray9816 := rays 23
def bank9816 : Fin 2 → Cell := twoBank p9816 ray9816
theorem signs9816 : ∀ j, Signs p9816 (bank9816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9817 := params 24
abbrev ray9817 := rays 24
def bank9817 : Fin 2 → Cell := twoBank p9817 ray9817
theorem signs9817 : ∀ j, Signs p9817 (bank9817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9818 := params 25
abbrev ray9818 := rays 25
def bank9818 : Fin 2 → Cell := twoBank p9818 ray9818
theorem signs9818 : ∀ j, Signs p9818 (bank9818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9819 := params 26
abbrev ray9819 := rays 26
def bank9819 : Fin 2 → Cell := twoBank p9819 ray9819
theorem signs9819 : ∀ j, Signs p9819 (bank9819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9820 := params 27
abbrev ray9820 := rays 27
def bank9820 : Fin 2 → Cell := twoBank p9820 ray9820
theorem signs9820 : ∀ j, Signs p9820 (bank9820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9821 := params 28
abbrev ray9821 := rays 28
def bank9821 : Fin 2 → Cell := twoBank p9821 ray9821
theorem signs9821 : ∀ j, Signs p9821 (bank9821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9822 := params 29
abbrev ray9822 := rays 29
def bank9822 : Fin 2 → Cell := twoBank p9822 ray9822
theorem signs9822 : ∀ j, Signs p9822 (bank9822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9823 := params 30
abbrev ray9823 := rays 30
def bank9823 : Fin 2 → Cell := twoBank p9823 ray9823
theorem signs9823 : ∀ j, Signs p9823 (bank9823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9824 := params 31
abbrev ray9824 := rays 31
def bank9824 : Fin 2 → Cell := twoBank p9824 ray9824
theorem signs9824 : ∀ j, Signs p9824 (bank9824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09793_09824
