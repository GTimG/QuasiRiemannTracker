/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04865_04896
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99069864287460,99069611123765,99069357935832,99069104723661,99068851487253,99068598226609,99068344941730,99068091632617,99067838299271,99067584941694,99067331559886,99067078153848,99066824723581,99066571269086,99066317790365,99066064287418,99065810760246,99065557208850,99065303633232,99065050033392,99064796409331,99064542761051,99064289088552,99064035391835,99063781670902,99063527925753,99063274156389,99063020362812,99062766545022,99062512703020,99062258836808,99062004946386,99061751031756]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4864+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4865 := params 0
abbrev ray4865 := rays 0
def bank4865 : Fin 2 → Cell := twoBank p4865 ray4865
theorem signs4865 : ∀ j, Signs p4865 (bank4865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4866 := params 1
abbrev ray4866 := rays 1
def bank4866 : Fin 2 → Cell := twoBank p4866 ray4866
theorem signs4866 : ∀ j, Signs p4866 (bank4866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4867 := params 2
abbrev ray4867 := rays 2
def bank4867 : Fin 2 → Cell := twoBank p4867 ray4867
theorem signs4867 : ∀ j, Signs p4867 (bank4867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4868 := params 3
abbrev ray4868 := rays 3
def bank4868 : Fin 2 → Cell := twoBank p4868 ray4868
theorem signs4868 : ∀ j, Signs p4868 (bank4868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4869 := params 4
abbrev ray4869 := rays 4
def bank4869 : Fin 2 → Cell := twoBank p4869 ray4869
theorem signs4869 : ∀ j, Signs p4869 (bank4869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4870 := params 5
abbrev ray4870 := rays 5
def bank4870 : Fin 2 → Cell := twoBank p4870 ray4870
theorem signs4870 : ∀ j, Signs p4870 (bank4870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4871 := params 6
abbrev ray4871 := rays 6
def bank4871 : Fin 2 → Cell := twoBank p4871 ray4871
theorem signs4871 : ∀ j, Signs p4871 (bank4871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4872 := params 7
abbrev ray4872 := rays 7
def bank4872 : Fin 2 → Cell := twoBank p4872 ray4872
theorem signs4872 : ∀ j, Signs p4872 (bank4872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4873 := params 8
abbrev ray4873 := rays 8
def bank4873 : Fin 2 → Cell := twoBank p4873 ray4873
theorem signs4873 : ∀ j, Signs p4873 (bank4873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4874 := params 9
abbrev ray4874 := rays 9
def bank4874 : Fin 2 → Cell := twoBank p4874 ray4874
theorem signs4874 : ∀ j, Signs p4874 (bank4874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4875 := params 10
abbrev ray4875 := rays 10
def bank4875 : Fin 2 → Cell := twoBank p4875 ray4875
theorem signs4875 : ∀ j, Signs p4875 (bank4875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4876 := params 11
abbrev ray4876 := rays 11
def bank4876 : Fin 2 → Cell := twoBank p4876 ray4876
theorem signs4876 : ∀ j, Signs p4876 (bank4876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4877 := params 12
abbrev ray4877 := rays 12
def bank4877 : Fin 2 → Cell := twoBank p4877 ray4877
theorem signs4877 : ∀ j, Signs p4877 (bank4877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4878 := params 13
abbrev ray4878 := rays 13
def bank4878 : Fin 2 → Cell := twoBank p4878 ray4878
theorem signs4878 : ∀ j, Signs p4878 (bank4878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4879 := params 14
abbrev ray4879 := rays 14
def bank4879 : Fin 2 → Cell := twoBank p4879 ray4879
theorem signs4879 : ∀ j, Signs p4879 (bank4879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4880 := params 15
abbrev ray4880 := rays 15
def bank4880 : Fin 2 → Cell := twoBank p4880 ray4880
theorem signs4880 : ∀ j, Signs p4880 (bank4880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4881 := params 16
abbrev ray4881 := rays 16
def bank4881 : Fin 2 → Cell := twoBank p4881 ray4881
theorem signs4881 : ∀ j, Signs p4881 (bank4881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4882 := params 17
abbrev ray4882 := rays 17
def bank4882 : Fin 2 → Cell := twoBank p4882 ray4882
theorem signs4882 : ∀ j, Signs p4882 (bank4882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4883 := params 18
abbrev ray4883 := rays 18
def bank4883 : Fin 2 → Cell := twoBank p4883 ray4883
theorem signs4883 : ∀ j, Signs p4883 (bank4883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4884 := params 19
abbrev ray4884 := rays 19
def bank4884 : Fin 2 → Cell := twoBank p4884 ray4884
theorem signs4884 : ∀ j, Signs p4884 (bank4884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4885 := params 20
abbrev ray4885 := rays 20
def bank4885 : Fin 2 → Cell := twoBank p4885 ray4885
theorem signs4885 : ∀ j, Signs p4885 (bank4885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4886 := params 21
abbrev ray4886 := rays 21
def bank4886 : Fin 2 → Cell := twoBank p4886 ray4886
theorem signs4886 : ∀ j, Signs p4886 (bank4886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4887 := params 22
abbrev ray4887 := rays 22
def bank4887 : Fin 2 → Cell := twoBank p4887 ray4887
theorem signs4887 : ∀ j, Signs p4887 (bank4887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4888 := params 23
abbrev ray4888 := rays 23
def bank4888 : Fin 2 → Cell := twoBank p4888 ray4888
theorem signs4888 : ∀ j, Signs p4888 (bank4888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4889 := params 24
abbrev ray4889 := rays 24
def bank4889 : Fin 2 → Cell := twoBank p4889 ray4889
theorem signs4889 : ∀ j, Signs p4889 (bank4889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4890 := params 25
abbrev ray4890 := rays 25
def bank4890 : Fin 2 → Cell := twoBank p4890 ray4890
theorem signs4890 : ∀ j, Signs p4890 (bank4890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4891 := params 26
abbrev ray4891 := rays 26
def bank4891 : Fin 2 → Cell := twoBank p4891 ray4891
theorem signs4891 : ∀ j, Signs p4891 (bank4891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4892 := params 27
abbrev ray4892 := rays 27
def bank4892 : Fin 2 → Cell := twoBank p4892 ray4892
theorem signs4892 : ∀ j, Signs p4892 (bank4892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4893 := params 28
abbrev ray4893 := rays 28
def bank4893 : Fin 2 → Cell := twoBank p4893 ray4893
theorem signs4893 : ∀ j, Signs p4893 (bank4893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4894 := params 29
abbrev ray4894 := rays 29
def bank4894 : Fin 2 → Cell := twoBank p4894 ray4894
theorem signs4894 : ∀ j, Signs p4894 (bank4894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4895 := params 30
abbrev ray4895 := rays 30
def bank4895 : Fin 2 → Cell := twoBank p4895 ray4895
theorem signs4895 : ∀ j, Signs p4895 (bank4895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4896 := params 31
abbrev ray4896 := rays 31
def bank4896 : Fin 2 → Cell := twoBank p4896 ray4896
theorem signs4896 : ∀ j, Signs p4896 (bank4896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04865_04896
