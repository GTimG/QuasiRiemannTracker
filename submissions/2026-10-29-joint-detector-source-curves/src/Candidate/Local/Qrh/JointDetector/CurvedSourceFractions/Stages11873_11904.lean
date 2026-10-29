/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11873_11904
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96748363195393,96747959388645,96747555562487,96747151716918,96746747851940,96746343967552,96745940063755,96745536140550,96745132197937,96744728235916,96744324254488,96743920253653,96743516233412,96743112193765,96742708134712,96742304056254,96741899958392,96741495841125,96741091704455,96740687548381,96740283372905,96739879178026,96739474963745,96739070730063,96738666476980,96738262204496,96737857912612,96737453601328,96737049270645,96736644920563,96736240551082,96735836162203,96735431753927]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11872+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11873 := params 0
abbrev ray11873 := rays 0
def bank11873 : Fin 2 → Cell := twoBank p11873 ray11873
theorem signs11873 : ∀ j, Signs p11873 (bank11873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11874 := params 1
abbrev ray11874 := rays 1
def bank11874 : Fin 2 → Cell := twoBank p11874 ray11874
theorem signs11874 : ∀ j, Signs p11874 (bank11874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11875 := params 2
abbrev ray11875 := rays 2
def bank11875 : Fin 2 → Cell := twoBank p11875 ray11875
theorem signs11875 : ∀ j, Signs p11875 (bank11875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11876 := params 3
abbrev ray11876 := rays 3
def bank11876 : Fin 2 → Cell := twoBank p11876 ray11876
theorem signs11876 : ∀ j, Signs p11876 (bank11876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11877 := params 4
abbrev ray11877 := rays 4
def bank11877 : Fin 2 → Cell := twoBank p11877 ray11877
theorem signs11877 : ∀ j, Signs p11877 (bank11877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11878 := params 5
abbrev ray11878 := rays 5
def bank11878 : Fin 2 → Cell := twoBank p11878 ray11878
theorem signs11878 : ∀ j, Signs p11878 (bank11878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11879 := params 6
abbrev ray11879 := rays 6
def bank11879 : Fin 2 → Cell := twoBank p11879 ray11879
theorem signs11879 : ∀ j, Signs p11879 (bank11879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11880 := params 7
abbrev ray11880 := rays 7
def bank11880 : Fin 2 → Cell := twoBank p11880 ray11880
theorem signs11880 : ∀ j, Signs p11880 (bank11880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11881 := params 8
abbrev ray11881 := rays 8
def bank11881 : Fin 2 → Cell := twoBank p11881 ray11881
theorem signs11881 : ∀ j, Signs p11881 (bank11881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11882 := params 9
abbrev ray11882 := rays 9
def bank11882 : Fin 2 → Cell := twoBank p11882 ray11882
theorem signs11882 : ∀ j, Signs p11882 (bank11882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11883 := params 10
abbrev ray11883 := rays 10
def bank11883 : Fin 2 → Cell := twoBank p11883 ray11883
theorem signs11883 : ∀ j, Signs p11883 (bank11883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11884 := params 11
abbrev ray11884 := rays 11
def bank11884 : Fin 2 → Cell := twoBank p11884 ray11884
theorem signs11884 : ∀ j, Signs p11884 (bank11884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11885 := params 12
abbrev ray11885 := rays 12
def bank11885 : Fin 2 → Cell := twoBank p11885 ray11885
theorem signs11885 : ∀ j, Signs p11885 (bank11885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11886 := params 13
abbrev ray11886 := rays 13
def bank11886 : Fin 2 → Cell := twoBank p11886 ray11886
theorem signs11886 : ∀ j, Signs p11886 (bank11886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11887 := params 14
abbrev ray11887 := rays 14
def bank11887 : Fin 2 → Cell := twoBank p11887 ray11887
theorem signs11887 : ∀ j, Signs p11887 (bank11887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11888 := params 15
abbrev ray11888 := rays 15
def bank11888 : Fin 2 → Cell := twoBank p11888 ray11888
theorem signs11888 : ∀ j, Signs p11888 (bank11888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11889 := params 16
abbrev ray11889 := rays 16
def bank11889 : Fin 2 → Cell := twoBank p11889 ray11889
theorem signs11889 : ∀ j, Signs p11889 (bank11889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11890 := params 17
abbrev ray11890 := rays 17
def bank11890 : Fin 2 → Cell := twoBank p11890 ray11890
theorem signs11890 : ∀ j, Signs p11890 (bank11890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11891 := params 18
abbrev ray11891 := rays 18
def bank11891 : Fin 2 → Cell := twoBank p11891 ray11891
theorem signs11891 : ∀ j, Signs p11891 (bank11891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11892 := params 19
abbrev ray11892 := rays 19
def bank11892 : Fin 2 → Cell := twoBank p11892 ray11892
theorem signs11892 : ∀ j, Signs p11892 (bank11892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11893 := params 20
abbrev ray11893 := rays 20
def bank11893 : Fin 2 → Cell := twoBank p11893 ray11893
theorem signs11893 : ∀ j, Signs p11893 (bank11893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11894 := params 21
abbrev ray11894 := rays 21
def bank11894 : Fin 2 → Cell := twoBank p11894 ray11894
theorem signs11894 : ∀ j, Signs p11894 (bank11894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11895 := params 22
abbrev ray11895 := rays 22
def bank11895 : Fin 2 → Cell := twoBank p11895 ray11895
theorem signs11895 : ∀ j, Signs p11895 (bank11895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11896 := params 23
abbrev ray11896 := rays 23
def bank11896 : Fin 2 → Cell := twoBank p11896 ray11896
theorem signs11896 : ∀ j, Signs p11896 (bank11896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11897 := params 24
abbrev ray11897 := rays 24
def bank11897 : Fin 2 → Cell := twoBank p11897 ray11897
theorem signs11897 : ∀ j, Signs p11897 (bank11897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11898 := params 25
abbrev ray11898 := rays 25
def bank11898 : Fin 2 → Cell := twoBank p11898 ray11898
theorem signs11898 : ∀ j, Signs p11898 (bank11898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11899 := params 26
abbrev ray11899 := rays 26
def bank11899 : Fin 2 → Cell := twoBank p11899 ray11899
theorem signs11899 : ∀ j, Signs p11899 (bank11899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11900 := params 27
abbrev ray11900 := rays 27
def bank11900 : Fin 2 → Cell := twoBank p11900 ray11900
theorem signs11900 : ∀ j, Signs p11900 (bank11900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11901 := params 28
abbrev ray11901 := rays 28
def bank11901 : Fin 2 → Cell := twoBank p11901 ray11901
theorem signs11901 : ∀ j, Signs p11901 (bank11901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11902 := params 29
abbrev ray11902 := rays 29
def bank11902 : Fin 2 → Cell := twoBank p11902 ray11902
theorem signs11902 : ∀ j, Signs p11902 (bank11902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11903 := params 30
abbrev ray11903 := rays 30
def bank11903 : Fin 2 → Cell := twoBank p11903 ray11903
theorem signs11903 : ∀ j, Signs p11903 (bank11903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11904 := params 31
abbrev ray11904 := rays 31
def bank11904 : Fin 2 → Cell := twoBank p11904 ray11904
theorem signs11904 : ∀ j, Signs p11904 (bank11904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11873_11904
