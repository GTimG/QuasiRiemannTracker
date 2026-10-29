/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07873_07904
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98202933814226,98202611820697,98202289805492,98201967768612,98201645710058,98201323629830,98201001527930,98200679404357,98200357259113,98200035092198,98199712903613,98199390693359,98199068461437,98198746207847,98198423932590,98198101635666,98197779317076,98197456976821,98197134614902,98196812231320,98196489826075,98196167399168,98195844950599,98195522480369,98195199988479,98194877474930,98194554939722,98194232382856,98193909804333,98193587204154,98193264582319,98192941938829,98192619273685]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7872+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7873 := params 0
abbrev ray7873 := rays 0
def bank7873 : Fin 2 → Cell := twoBank p7873 ray7873
theorem signs7873 : ∀ j, Signs p7873 (bank7873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7874 := params 1
abbrev ray7874 := rays 1
def bank7874 : Fin 2 → Cell := twoBank p7874 ray7874
theorem signs7874 : ∀ j, Signs p7874 (bank7874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7875 := params 2
abbrev ray7875 := rays 2
def bank7875 : Fin 2 → Cell := twoBank p7875 ray7875
theorem signs7875 : ∀ j, Signs p7875 (bank7875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7876 := params 3
abbrev ray7876 := rays 3
def bank7876 : Fin 2 → Cell := twoBank p7876 ray7876
theorem signs7876 : ∀ j, Signs p7876 (bank7876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7877 := params 4
abbrev ray7877 := rays 4
def bank7877 : Fin 2 → Cell := twoBank p7877 ray7877
theorem signs7877 : ∀ j, Signs p7877 (bank7877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7878 := params 5
abbrev ray7878 := rays 5
def bank7878 : Fin 2 → Cell := twoBank p7878 ray7878
theorem signs7878 : ∀ j, Signs p7878 (bank7878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7879 := params 6
abbrev ray7879 := rays 6
def bank7879 : Fin 2 → Cell := twoBank p7879 ray7879
theorem signs7879 : ∀ j, Signs p7879 (bank7879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7880 := params 7
abbrev ray7880 := rays 7
def bank7880 : Fin 2 → Cell := twoBank p7880 ray7880
theorem signs7880 : ∀ j, Signs p7880 (bank7880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7881 := params 8
abbrev ray7881 := rays 8
def bank7881 : Fin 2 → Cell := twoBank p7881 ray7881
theorem signs7881 : ∀ j, Signs p7881 (bank7881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7882 := params 9
abbrev ray7882 := rays 9
def bank7882 : Fin 2 → Cell := twoBank p7882 ray7882
theorem signs7882 : ∀ j, Signs p7882 (bank7882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7883 := params 10
abbrev ray7883 := rays 10
def bank7883 : Fin 2 → Cell := twoBank p7883 ray7883
theorem signs7883 : ∀ j, Signs p7883 (bank7883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7884 := params 11
abbrev ray7884 := rays 11
def bank7884 : Fin 2 → Cell := twoBank p7884 ray7884
theorem signs7884 : ∀ j, Signs p7884 (bank7884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7885 := params 12
abbrev ray7885 := rays 12
def bank7885 : Fin 2 → Cell := twoBank p7885 ray7885
theorem signs7885 : ∀ j, Signs p7885 (bank7885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7886 := params 13
abbrev ray7886 := rays 13
def bank7886 : Fin 2 → Cell := twoBank p7886 ray7886
theorem signs7886 : ∀ j, Signs p7886 (bank7886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7887 := params 14
abbrev ray7887 := rays 14
def bank7887 : Fin 2 → Cell := twoBank p7887 ray7887
theorem signs7887 : ∀ j, Signs p7887 (bank7887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7888 := params 15
abbrev ray7888 := rays 15
def bank7888 : Fin 2 → Cell := twoBank p7888 ray7888
theorem signs7888 : ∀ j, Signs p7888 (bank7888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7889 := params 16
abbrev ray7889 := rays 16
def bank7889 : Fin 2 → Cell := twoBank p7889 ray7889
theorem signs7889 : ∀ j, Signs p7889 (bank7889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7890 := params 17
abbrev ray7890 := rays 17
def bank7890 : Fin 2 → Cell := twoBank p7890 ray7890
theorem signs7890 : ∀ j, Signs p7890 (bank7890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7891 := params 18
abbrev ray7891 := rays 18
def bank7891 : Fin 2 → Cell := twoBank p7891 ray7891
theorem signs7891 : ∀ j, Signs p7891 (bank7891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7892 := params 19
abbrev ray7892 := rays 19
def bank7892 : Fin 2 → Cell := twoBank p7892 ray7892
theorem signs7892 : ∀ j, Signs p7892 (bank7892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7893 := params 20
abbrev ray7893 := rays 20
def bank7893 : Fin 2 → Cell := twoBank p7893 ray7893
theorem signs7893 : ∀ j, Signs p7893 (bank7893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7894 := params 21
abbrev ray7894 := rays 21
def bank7894 : Fin 2 → Cell := twoBank p7894 ray7894
theorem signs7894 : ∀ j, Signs p7894 (bank7894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7895 := params 22
abbrev ray7895 := rays 22
def bank7895 : Fin 2 → Cell := twoBank p7895 ray7895
theorem signs7895 : ∀ j, Signs p7895 (bank7895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7896 := params 23
abbrev ray7896 := rays 23
def bank7896 : Fin 2 → Cell := twoBank p7896 ray7896
theorem signs7896 : ∀ j, Signs p7896 (bank7896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7897 := params 24
abbrev ray7897 := rays 24
def bank7897 : Fin 2 → Cell := twoBank p7897 ray7897
theorem signs7897 : ∀ j, Signs p7897 (bank7897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7898 := params 25
abbrev ray7898 := rays 25
def bank7898 : Fin 2 → Cell := twoBank p7898 ray7898
theorem signs7898 : ∀ j, Signs p7898 (bank7898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7899 := params 26
abbrev ray7899 := rays 26
def bank7899 : Fin 2 → Cell := twoBank p7899 ray7899
theorem signs7899 : ∀ j, Signs p7899 (bank7899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7900 := params 27
abbrev ray7900 := rays 27
def bank7900 : Fin 2 → Cell := twoBank p7900 ray7900
theorem signs7900 : ∀ j, Signs p7900 (bank7900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7901 := params 28
abbrev ray7901 := rays 28
def bank7901 : Fin 2 → Cell := twoBank p7901 ray7901
theorem signs7901 : ∀ j, Signs p7901 (bank7901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7902 := params 29
abbrev ray7902 := rays 29
def bank7902 : Fin 2 → Cell := twoBank p7902 ray7902
theorem signs7902 : ∀ j, Signs p7902 (bank7902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7903 := params 30
abbrev ray7903 := rays 30
def bank7903 : Fin 2 → Cell := twoBank p7903 ray7903
theorem signs7903 : ∀ j, Signs p7903 (bank7903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7904 := params 31
abbrev ray7904 := rays 31
def bank7904 : Fin 2 → Cell := twoBank p7904 ray7904
theorem signs7904 : ∀ j, Signs p7904 (bank7904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07873_07904
