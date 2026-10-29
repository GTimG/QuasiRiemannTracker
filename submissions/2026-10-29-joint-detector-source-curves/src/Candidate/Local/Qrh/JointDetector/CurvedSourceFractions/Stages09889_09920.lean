/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09889_09920
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97510683813761,97510319458898,97509955083636,97509590687975,97509226271916,97508861835460,97508497378607,97508132901357,97507768403712,97507403885671,97507039347236,97506674788407,97506310209184,97505945609568,97505580989560,97505216349160,97504851688369,97504487007187,97504122305615,97503757583653,97503392841302,97503028078563,97502663295436,97502298491921,97501933668019,97501568823731,97501203959057,97500839073998,97500474168555,97500109242728,97499744296517,97499379329923,97499014342947]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9888+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9889 := params 0
abbrev ray9889 := rays 0
def bank9889 : Fin 2 → Cell := twoBank p9889 ray9889
theorem signs9889 : ∀ j, Signs p9889 (bank9889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9890 := params 1
abbrev ray9890 := rays 1
def bank9890 : Fin 2 → Cell := twoBank p9890 ray9890
theorem signs9890 : ∀ j, Signs p9890 (bank9890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9891 := params 2
abbrev ray9891 := rays 2
def bank9891 : Fin 2 → Cell := twoBank p9891 ray9891
theorem signs9891 : ∀ j, Signs p9891 (bank9891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9892 := params 3
abbrev ray9892 := rays 3
def bank9892 : Fin 2 → Cell := twoBank p9892 ray9892
theorem signs9892 : ∀ j, Signs p9892 (bank9892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9893 := params 4
abbrev ray9893 := rays 4
def bank9893 : Fin 2 → Cell := twoBank p9893 ray9893
theorem signs9893 : ∀ j, Signs p9893 (bank9893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9894 := params 5
abbrev ray9894 := rays 5
def bank9894 : Fin 2 → Cell := twoBank p9894 ray9894
theorem signs9894 : ∀ j, Signs p9894 (bank9894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9895 := params 6
abbrev ray9895 := rays 6
def bank9895 : Fin 2 → Cell := twoBank p9895 ray9895
theorem signs9895 : ∀ j, Signs p9895 (bank9895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9896 := params 7
abbrev ray9896 := rays 7
def bank9896 : Fin 2 → Cell := twoBank p9896 ray9896
theorem signs9896 : ∀ j, Signs p9896 (bank9896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9897 := params 8
abbrev ray9897 := rays 8
def bank9897 : Fin 2 → Cell := twoBank p9897 ray9897
theorem signs9897 : ∀ j, Signs p9897 (bank9897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9898 := params 9
abbrev ray9898 := rays 9
def bank9898 : Fin 2 → Cell := twoBank p9898 ray9898
theorem signs9898 : ∀ j, Signs p9898 (bank9898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9899 := params 10
abbrev ray9899 := rays 10
def bank9899 : Fin 2 → Cell := twoBank p9899 ray9899
theorem signs9899 : ∀ j, Signs p9899 (bank9899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9900 := params 11
abbrev ray9900 := rays 11
def bank9900 : Fin 2 → Cell := twoBank p9900 ray9900
theorem signs9900 : ∀ j, Signs p9900 (bank9900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9901 := params 12
abbrev ray9901 := rays 12
def bank9901 : Fin 2 → Cell := twoBank p9901 ray9901
theorem signs9901 : ∀ j, Signs p9901 (bank9901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9902 := params 13
abbrev ray9902 := rays 13
def bank9902 : Fin 2 → Cell := twoBank p9902 ray9902
theorem signs9902 : ∀ j, Signs p9902 (bank9902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9903 := params 14
abbrev ray9903 := rays 14
def bank9903 : Fin 2 → Cell := twoBank p9903 ray9903
theorem signs9903 : ∀ j, Signs p9903 (bank9903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9904 := params 15
abbrev ray9904 := rays 15
def bank9904 : Fin 2 → Cell := twoBank p9904 ray9904
theorem signs9904 : ∀ j, Signs p9904 (bank9904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9905 := params 16
abbrev ray9905 := rays 16
def bank9905 : Fin 2 → Cell := twoBank p9905 ray9905
theorem signs9905 : ∀ j, Signs p9905 (bank9905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9906 := params 17
abbrev ray9906 := rays 17
def bank9906 : Fin 2 → Cell := twoBank p9906 ray9906
theorem signs9906 : ∀ j, Signs p9906 (bank9906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9907 := params 18
abbrev ray9907 := rays 18
def bank9907 : Fin 2 → Cell := twoBank p9907 ray9907
theorem signs9907 : ∀ j, Signs p9907 (bank9907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9908 := params 19
abbrev ray9908 := rays 19
def bank9908 : Fin 2 → Cell := twoBank p9908 ray9908
theorem signs9908 : ∀ j, Signs p9908 (bank9908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9909 := params 20
abbrev ray9909 := rays 20
def bank9909 : Fin 2 → Cell := twoBank p9909 ray9909
theorem signs9909 : ∀ j, Signs p9909 (bank9909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9910 := params 21
abbrev ray9910 := rays 21
def bank9910 : Fin 2 → Cell := twoBank p9910 ray9910
theorem signs9910 : ∀ j, Signs p9910 (bank9910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9911 := params 22
abbrev ray9911 := rays 22
def bank9911 : Fin 2 → Cell := twoBank p9911 ray9911
theorem signs9911 : ∀ j, Signs p9911 (bank9911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9912 := params 23
abbrev ray9912 := rays 23
def bank9912 : Fin 2 → Cell := twoBank p9912 ray9912
theorem signs9912 : ∀ j, Signs p9912 (bank9912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9913 := params 24
abbrev ray9913 := rays 24
def bank9913 : Fin 2 → Cell := twoBank p9913 ray9913
theorem signs9913 : ∀ j, Signs p9913 (bank9913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9914 := params 25
abbrev ray9914 := rays 25
def bank9914 : Fin 2 → Cell := twoBank p9914 ray9914
theorem signs9914 : ∀ j, Signs p9914 (bank9914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9915 := params 26
abbrev ray9915 := rays 26
def bank9915 : Fin 2 → Cell := twoBank p9915 ray9915
theorem signs9915 : ∀ j, Signs p9915 (bank9915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9916 := params 27
abbrev ray9916 := rays 27
def bank9916 : Fin 2 → Cell := twoBank p9916 ray9916
theorem signs9916 : ∀ j, Signs p9916 (bank9916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9917 := params 28
abbrev ray9917 := rays 28
def bank9917 : Fin 2 → Cell := twoBank p9917 ray9917
theorem signs9917 : ∀ j, Signs p9917 (bank9917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9918 := params 29
abbrev ray9918 := rays 29
def bank9918 : Fin 2 → Cell := twoBank p9918 ray9918
theorem signs9918 : ∀ j, Signs p9918 (bank9918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9919 := params 30
abbrev ray9919 := rays 30
def bank9919 : Fin 2 → Cell := twoBank p9919 ray9919
theorem signs9919 : ∀ j, Signs p9919 (bank9919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9920 := params 31
abbrev ray9920 := rays 31
def bank9920 : Fin 2 → Cell := twoBank p9920 ray9920
theorem signs9920 : ∀ j, Signs p9920 (bank9920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09889_09920
