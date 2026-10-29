/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07809_07840
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98223496282154,98223175677349,98222855050822,98222534402575,98222213732608,98221893040922,98221572327517,98221251592395,98220930835556,98220610057000,98220289256729,98219968434743,98219647591043,98219326725629,98219005838502,98218684929663,98218363999113,98218043046853,98217722072883,98217401077204,98217080059816,98216759020720,98216437959917,98216116877408,98215795773193,98215474647274,98215153499650,98214832330323,98214511139293,98214189926561,98213868692128,98213547435994,98213226158161]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7808+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7809 := params 0
abbrev ray7809 := rays 0
def bank7809 : Fin 2 → Cell := twoBank p7809 ray7809
theorem signs7809 : ∀ j, Signs p7809 (bank7809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7810 := params 1
abbrev ray7810 := rays 1
def bank7810 : Fin 2 → Cell := twoBank p7810 ray7810
theorem signs7810 : ∀ j, Signs p7810 (bank7810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7811 := params 2
abbrev ray7811 := rays 2
def bank7811 : Fin 2 → Cell := twoBank p7811 ray7811
theorem signs7811 : ∀ j, Signs p7811 (bank7811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7812 := params 3
abbrev ray7812 := rays 3
def bank7812 : Fin 2 → Cell := twoBank p7812 ray7812
theorem signs7812 : ∀ j, Signs p7812 (bank7812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7813 := params 4
abbrev ray7813 := rays 4
def bank7813 : Fin 2 → Cell := twoBank p7813 ray7813
theorem signs7813 : ∀ j, Signs p7813 (bank7813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7814 := params 5
abbrev ray7814 := rays 5
def bank7814 : Fin 2 → Cell := twoBank p7814 ray7814
theorem signs7814 : ∀ j, Signs p7814 (bank7814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7815 := params 6
abbrev ray7815 := rays 6
def bank7815 : Fin 2 → Cell := twoBank p7815 ray7815
theorem signs7815 : ∀ j, Signs p7815 (bank7815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7816 := params 7
abbrev ray7816 := rays 7
def bank7816 : Fin 2 → Cell := twoBank p7816 ray7816
theorem signs7816 : ∀ j, Signs p7816 (bank7816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7817 := params 8
abbrev ray7817 := rays 8
def bank7817 : Fin 2 → Cell := twoBank p7817 ray7817
theorem signs7817 : ∀ j, Signs p7817 (bank7817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7818 := params 9
abbrev ray7818 := rays 9
def bank7818 : Fin 2 → Cell := twoBank p7818 ray7818
theorem signs7818 : ∀ j, Signs p7818 (bank7818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7819 := params 10
abbrev ray7819 := rays 10
def bank7819 : Fin 2 → Cell := twoBank p7819 ray7819
theorem signs7819 : ∀ j, Signs p7819 (bank7819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7820 := params 11
abbrev ray7820 := rays 11
def bank7820 : Fin 2 → Cell := twoBank p7820 ray7820
theorem signs7820 : ∀ j, Signs p7820 (bank7820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7821 := params 12
abbrev ray7821 := rays 12
def bank7821 : Fin 2 → Cell := twoBank p7821 ray7821
theorem signs7821 : ∀ j, Signs p7821 (bank7821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7822 := params 13
abbrev ray7822 := rays 13
def bank7822 : Fin 2 → Cell := twoBank p7822 ray7822
theorem signs7822 : ∀ j, Signs p7822 (bank7822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7823 := params 14
abbrev ray7823 := rays 14
def bank7823 : Fin 2 → Cell := twoBank p7823 ray7823
theorem signs7823 : ∀ j, Signs p7823 (bank7823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7824 := params 15
abbrev ray7824 := rays 15
def bank7824 : Fin 2 → Cell := twoBank p7824 ray7824
theorem signs7824 : ∀ j, Signs p7824 (bank7824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7825 := params 16
abbrev ray7825 := rays 16
def bank7825 : Fin 2 → Cell := twoBank p7825 ray7825
theorem signs7825 : ∀ j, Signs p7825 (bank7825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7826 := params 17
abbrev ray7826 := rays 17
def bank7826 : Fin 2 → Cell := twoBank p7826 ray7826
theorem signs7826 : ∀ j, Signs p7826 (bank7826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7827 := params 18
abbrev ray7827 := rays 18
def bank7827 : Fin 2 → Cell := twoBank p7827 ray7827
theorem signs7827 : ∀ j, Signs p7827 (bank7827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7828 := params 19
abbrev ray7828 := rays 19
def bank7828 : Fin 2 → Cell := twoBank p7828 ray7828
theorem signs7828 : ∀ j, Signs p7828 (bank7828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7829 := params 20
abbrev ray7829 := rays 20
def bank7829 : Fin 2 → Cell := twoBank p7829 ray7829
theorem signs7829 : ∀ j, Signs p7829 (bank7829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7830 := params 21
abbrev ray7830 := rays 21
def bank7830 : Fin 2 → Cell := twoBank p7830 ray7830
theorem signs7830 : ∀ j, Signs p7830 (bank7830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7831 := params 22
abbrev ray7831 := rays 22
def bank7831 : Fin 2 → Cell := twoBank p7831 ray7831
theorem signs7831 : ∀ j, Signs p7831 (bank7831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7832 := params 23
abbrev ray7832 := rays 23
def bank7832 : Fin 2 → Cell := twoBank p7832 ray7832
theorem signs7832 : ∀ j, Signs p7832 (bank7832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7833 := params 24
abbrev ray7833 := rays 24
def bank7833 : Fin 2 → Cell := twoBank p7833 ray7833
theorem signs7833 : ∀ j, Signs p7833 (bank7833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7834 := params 25
abbrev ray7834 := rays 25
def bank7834 : Fin 2 → Cell := twoBank p7834 ray7834
theorem signs7834 : ∀ j, Signs p7834 (bank7834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7835 := params 26
abbrev ray7835 := rays 26
def bank7835 : Fin 2 → Cell := twoBank p7835 ray7835
theorem signs7835 : ∀ j, Signs p7835 (bank7835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7836 := params 27
abbrev ray7836 := rays 27
def bank7836 : Fin 2 → Cell := twoBank p7836 ray7836
theorem signs7836 : ∀ j, Signs p7836 (bank7836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7837 := params 28
abbrev ray7837 := rays 28
def bank7837 : Fin 2 → Cell := twoBank p7837 ray7837
theorem signs7837 : ∀ j, Signs p7837 (bank7837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7838 := params 29
abbrev ray7838 := rays 29
def bank7838 : Fin 2 → Cell := twoBank p7838 ray7838
theorem signs7838 : ∀ j, Signs p7838 (bank7838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7839 := params 30
abbrev ray7839 := rays 30
def bank7839 : Fin 2 → Cell := twoBank p7839 ray7839
theorem signs7839 : ∀ j, Signs p7839 (bank7839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7840 := params 31
abbrev ray7840 := rays 31
def bank7840 : Fin 2 → Cell := twoBank p7840 ray7840
theorem signs7840 : ∀ j, Signs p7840 (bank7840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07809_07840
