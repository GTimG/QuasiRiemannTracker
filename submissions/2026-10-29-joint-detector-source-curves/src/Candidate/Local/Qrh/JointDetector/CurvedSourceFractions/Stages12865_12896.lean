/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12865_12896
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96338321966479,96337899303454,96337476623956,96337053927985,96336631215542,96336208486626,96335785741238,96335362979379,96334940201048,96334517406246,96334094594973,96333671767230,96333248923016,96332826062332,96332403185179,96331980291556,96331557381464,96331134454903,96330711511873,96330288552375,96329865576409,96329442583975,96329019575073,96328596549704,96328173507868,96327750449565,96327327374795,96326904283559,96326481175857,96326058051689,96325634911056,96325211753958,96324788580395]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12864+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12865 := params 0
abbrev ray12865 := rays 0
def bank12865 : Fin 1 → Cell := oneBank p12865 ray12865
theorem signs12865 : ∀ j, Signs p12865 (bank12865 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12866 := params 1
abbrev ray12866 := rays 1
def bank12866 : Fin 1 → Cell := oneBank p12866 ray12866
theorem signs12866 : ∀ j, Signs p12866 (bank12866 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12867 := params 2
abbrev ray12867 := rays 2
def bank12867 : Fin 1 → Cell := oneBank p12867 ray12867
theorem signs12867 : ∀ j, Signs p12867 (bank12867 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12868 := params 3
abbrev ray12868 := rays 3
def bank12868 : Fin 1 → Cell := oneBank p12868 ray12868
theorem signs12868 : ∀ j, Signs p12868 (bank12868 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12869 := params 4
abbrev ray12869 := rays 4
def bank12869 : Fin 1 → Cell := oneBank p12869 ray12869
theorem signs12869 : ∀ j, Signs p12869 (bank12869 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12870 := params 5
abbrev ray12870 := rays 5
def bank12870 : Fin 1 → Cell := oneBank p12870 ray12870
theorem signs12870 : ∀ j, Signs p12870 (bank12870 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12871 := params 6
abbrev ray12871 := rays 6
def bank12871 : Fin 1 → Cell := oneBank p12871 ray12871
theorem signs12871 : ∀ j, Signs p12871 (bank12871 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12872 := params 7
abbrev ray12872 := rays 7
def bank12872 : Fin 1 → Cell := oneBank p12872 ray12872
theorem signs12872 : ∀ j, Signs p12872 (bank12872 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12873 := params 8
abbrev ray12873 := rays 8
def bank12873 : Fin 1 → Cell := oneBank p12873 ray12873
theorem signs12873 : ∀ j, Signs p12873 (bank12873 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12874 := params 9
abbrev ray12874 := rays 9
def bank12874 : Fin 1 → Cell := oneBank p12874 ray12874
theorem signs12874 : ∀ j, Signs p12874 (bank12874 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12875 := params 10
abbrev ray12875 := rays 10
def bank12875 : Fin 1 → Cell := oneBank p12875 ray12875
theorem signs12875 : ∀ j, Signs p12875 (bank12875 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12876 := params 11
abbrev ray12876 := rays 11
def bank12876 : Fin 1 → Cell := oneBank p12876 ray12876
theorem signs12876 : ∀ j, Signs p12876 (bank12876 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12877 := params 12
abbrev ray12877 := rays 12
def bank12877 : Fin 1 → Cell := oneBank p12877 ray12877
theorem signs12877 : ∀ j, Signs p12877 (bank12877 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12878 := params 13
abbrev ray12878 := rays 13
def bank12878 : Fin 1 → Cell := oneBank p12878 ray12878
theorem signs12878 : ∀ j, Signs p12878 (bank12878 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12879 := params 14
abbrev ray12879 := rays 14
def bank12879 : Fin 1 → Cell := oneBank p12879 ray12879
theorem signs12879 : ∀ j, Signs p12879 (bank12879 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12880 := params 15
abbrev ray12880 := rays 15
def bank12880 : Fin 1 → Cell := oneBank p12880 ray12880
theorem signs12880 : ∀ j, Signs p12880 (bank12880 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12881 := params 16
abbrev ray12881 := rays 16
def bank12881 : Fin 1 → Cell := oneBank p12881 ray12881
theorem signs12881 : ∀ j, Signs p12881 (bank12881 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12882 := params 17
abbrev ray12882 := rays 17
def bank12882 : Fin 1 → Cell := oneBank p12882 ray12882
theorem signs12882 : ∀ j, Signs p12882 (bank12882 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12883 := params 18
abbrev ray12883 := rays 18
def bank12883 : Fin 1 → Cell := oneBank p12883 ray12883
theorem signs12883 : ∀ j, Signs p12883 (bank12883 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12884 := params 19
abbrev ray12884 := rays 19
def bank12884 : Fin 1 → Cell := oneBank p12884 ray12884
theorem signs12884 : ∀ j, Signs p12884 (bank12884 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12885 := params 20
abbrev ray12885 := rays 20
def bank12885 : Fin 1 → Cell := oneBank p12885 ray12885
theorem signs12885 : ∀ j, Signs p12885 (bank12885 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12886 := params 21
abbrev ray12886 := rays 21
def bank12886 : Fin 1 → Cell := oneBank p12886 ray12886
theorem signs12886 : ∀ j, Signs p12886 (bank12886 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12887 := params 22
abbrev ray12887 := rays 22
def bank12887 : Fin 1 → Cell := oneBank p12887 ray12887
theorem signs12887 : ∀ j, Signs p12887 (bank12887 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12888 := params 23
abbrev ray12888 := rays 23
def bank12888 : Fin 1 → Cell := oneBank p12888 ray12888
theorem signs12888 : ∀ j, Signs p12888 (bank12888 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12889 := params 24
abbrev ray12889 := rays 24
def bank12889 : Fin 1 → Cell := oneBank p12889 ray12889
theorem signs12889 : ∀ j, Signs p12889 (bank12889 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12890 := params 25
abbrev ray12890 := rays 25
def bank12890 : Fin 1 → Cell := oneBank p12890 ray12890
theorem signs12890 : ∀ j, Signs p12890 (bank12890 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12891 := params 26
abbrev ray12891 := rays 26
def bank12891 : Fin 1 → Cell := oneBank p12891 ray12891
theorem signs12891 : ∀ j, Signs p12891 (bank12891 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12892 := params 27
abbrev ray12892 := rays 27
def bank12892 : Fin 1 → Cell := oneBank p12892 ray12892
theorem signs12892 : ∀ j, Signs p12892 (bank12892 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12893 := params 28
abbrev ray12893 := rays 28
def bank12893 : Fin 1 → Cell := oneBank p12893 ray12893
theorem signs12893 : ∀ j, Signs p12893 (bank12893 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12894 := params 29
abbrev ray12894 := rays 29
def bank12894 : Fin 1 → Cell := oneBank p12894 ray12894
theorem signs12894 : ∀ j, Signs p12894 (bank12894 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12895 := params 30
abbrev ray12895 := rays 30
def bank12895 : Fin 1 → Cell := oneBank p12895 ray12895
theorem signs12895 : ∀ j, Signs p12895 (bank12895 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12896 := params 31
abbrev ray12896 := rays 31
def bank12896 : Fin 1 → Cell := oneBank p12896 ray12896
theorem signs12896 : ∀ j, Signs p12896 (bank12896 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12865_12896
