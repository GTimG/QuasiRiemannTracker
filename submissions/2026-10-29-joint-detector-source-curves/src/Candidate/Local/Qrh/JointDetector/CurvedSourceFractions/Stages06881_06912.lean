/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06881_06912
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98511556097255,98511255969963,98510955820248,98510655648110,98510355453551,98510055236571,98509754997171,98509454735352,98509154451114,98508854144459,98508553815387,98508253463899,98507953089996,98507652693679,98507352274948,98507051833804,98506751370248,98506450884281,98506150375904,98505849845117,98505549291921,98505248716317,98504948118306,98504647497888,98504346855065,98504046189837,98503745502205,98503444792170,98503144059732,98502843304893,98502542527653,98502241728013,98501940905974]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6880+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6881 := params 0
abbrev ray6881 := rays 0
def bank6881 : Fin 2 → Cell := twoBank p6881 ray6881
theorem signs6881 : ∀ j, Signs p6881 (bank6881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6882 := params 1
abbrev ray6882 := rays 1
def bank6882 : Fin 2 → Cell := twoBank p6882 ray6882
theorem signs6882 : ∀ j, Signs p6882 (bank6882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6883 := params 2
abbrev ray6883 := rays 2
def bank6883 : Fin 2 → Cell := twoBank p6883 ray6883
theorem signs6883 : ∀ j, Signs p6883 (bank6883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6884 := params 3
abbrev ray6884 := rays 3
def bank6884 : Fin 2 → Cell := twoBank p6884 ray6884
theorem signs6884 : ∀ j, Signs p6884 (bank6884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6885 := params 4
abbrev ray6885 := rays 4
def bank6885 : Fin 2 → Cell := twoBank p6885 ray6885
theorem signs6885 : ∀ j, Signs p6885 (bank6885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6886 := params 5
abbrev ray6886 := rays 5
def bank6886 : Fin 2 → Cell := twoBank p6886 ray6886
theorem signs6886 : ∀ j, Signs p6886 (bank6886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6887 := params 6
abbrev ray6887 := rays 6
def bank6887 : Fin 2 → Cell := twoBank p6887 ray6887
theorem signs6887 : ∀ j, Signs p6887 (bank6887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6888 := params 7
abbrev ray6888 := rays 7
def bank6888 : Fin 2 → Cell := twoBank p6888 ray6888
theorem signs6888 : ∀ j, Signs p6888 (bank6888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6889 := params 8
abbrev ray6889 := rays 8
def bank6889 : Fin 2 → Cell := twoBank p6889 ray6889
theorem signs6889 : ∀ j, Signs p6889 (bank6889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6890 := params 9
abbrev ray6890 := rays 9
def bank6890 : Fin 2 → Cell := twoBank p6890 ray6890
theorem signs6890 : ∀ j, Signs p6890 (bank6890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6891 := params 10
abbrev ray6891 := rays 10
def bank6891 : Fin 2 → Cell := twoBank p6891 ray6891
theorem signs6891 : ∀ j, Signs p6891 (bank6891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6892 := params 11
abbrev ray6892 := rays 11
def bank6892 : Fin 2 → Cell := twoBank p6892 ray6892
theorem signs6892 : ∀ j, Signs p6892 (bank6892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6893 := params 12
abbrev ray6893 := rays 12
def bank6893 : Fin 2 → Cell := twoBank p6893 ray6893
theorem signs6893 : ∀ j, Signs p6893 (bank6893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6894 := params 13
abbrev ray6894 := rays 13
def bank6894 : Fin 2 → Cell := twoBank p6894 ray6894
theorem signs6894 : ∀ j, Signs p6894 (bank6894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6895 := params 14
abbrev ray6895 := rays 14
def bank6895 : Fin 2 → Cell := twoBank p6895 ray6895
theorem signs6895 : ∀ j, Signs p6895 (bank6895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6896 := params 15
abbrev ray6896 := rays 15
def bank6896 : Fin 2 → Cell := twoBank p6896 ray6896
theorem signs6896 : ∀ j, Signs p6896 (bank6896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6897 := params 16
abbrev ray6897 := rays 16
def bank6897 : Fin 2 → Cell := twoBank p6897 ray6897
theorem signs6897 : ∀ j, Signs p6897 (bank6897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6898 := params 17
abbrev ray6898 := rays 17
def bank6898 : Fin 2 → Cell := twoBank p6898 ray6898
theorem signs6898 : ∀ j, Signs p6898 (bank6898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6899 := params 18
abbrev ray6899 := rays 18
def bank6899 : Fin 2 → Cell := twoBank p6899 ray6899
theorem signs6899 : ∀ j, Signs p6899 (bank6899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6900 := params 19
abbrev ray6900 := rays 19
def bank6900 : Fin 2 → Cell := twoBank p6900 ray6900
theorem signs6900 : ∀ j, Signs p6900 (bank6900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6901 := params 20
abbrev ray6901 := rays 20
def bank6901 : Fin 2 → Cell := twoBank p6901 ray6901
theorem signs6901 : ∀ j, Signs p6901 (bank6901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6902 := params 21
abbrev ray6902 := rays 21
def bank6902 : Fin 2 → Cell := twoBank p6902 ray6902
theorem signs6902 : ∀ j, Signs p6902 (bank6902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6903 := params 22
abbrev ray6903 := rays 22
def bank6903 : Fin 2 → Cell := twoBank p6903 ray6903
theorem signs6903 : ∀ j, Signs p6903 (bank6903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6904 := params 23
abbrev ray6904 := rays 23
def bank6904 : Fin 2 → Cell := twoBank p6904 ray6904
theorem signs6904 : ∀ j, Signs p6904 (bank6904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6905 := params 24
abbrev ray6905 := rays 24
def bank6905 : Fin 2 → Cell := twoBank p6905 ray6905
theorem signs6905 : ∀ j, Signs p6905 (bank6905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6906 := params 25
abbrev ray6906 := rays 25
def bank6906 : Fin 2 → Cell := twoBank p6906 ray6906
theorem signs6906 : ∀ j, Signs p6906 (bank6906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6907 := params 26
abbrev ray6907 := rays 26
def bank6907 : Fin 2 → Cell := twoBank p6907 ray6907
theorem signs6907 : ∀ j, Signs p6907 (bank6907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6908 := params 27
abbrev ray6908 := rays 27
def bank6908 : Fin 2 → Cell := twoBank p6908 ray6908
theorem signs6908 : ∀ j, Signs p6908 (bank6908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6909 := params 28
abbrev ray6909 := rays 28
def bank6909 : Fin 2 → Cell := twoBank p6909 ray6909
theorem signs6909 : ∀ j, Signs p6909 (bank6909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6910 := params 29
abbrev ray6910 := rays 29
def bank6910 : Fin 2 → Cell := twoBank p6910 ray6910
theorem signs6910 : ∀ j, Signs p6910 (bank6910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6911 := params 30
abbrev ray6911 := rays 30
def bank6911 : Fin 2 → Cell := twoBank p6911 ray6911
theorem signs6911 : ∀ j, Signs p6911 (bank6911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6912 := params 31
abbrev ray6912 := rays 31
def bank6912 : Fin 2 → Cell := twoBank p6912 ray6912
theorem signs6912 : ∀ j, Signs p6912 (bank6912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06881_06912
