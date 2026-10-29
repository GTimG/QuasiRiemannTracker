/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16865_16896
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94518006708555,94517519520468,94517032316392,94516545096327,94516057860273,94515570608230,94515083340198,94514596056176,94514108756165,94513621440165,94513134108176,94512646760197,94512159396229,94511672016272,94511184620325,94510697208389,94510209780463,94509722336548,94509234876643,94508747400749,94508259908865,94507772400992,94507284877129,94506797337276,94506309781434,94505822209602,94505334621780,94504847017968,94504359398167,94503871762376,94503384110595,94502896442824,94502408759063]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16864+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16865 := params 0
abbrev ray16865 := rays 0
def bank16865 : Fin 1 → Cell := oneBank p16865 ray16865
theorem signs16865 : ∀ j, Signs p16865 (bank16865 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16866 := params 1
abbrev ray16866 := rays 1
def bank16866 : Fin 1 → Cell := oneBank p16866 ray16866
theorem signs16866 : ∀ j, Signs p16866 (bank16866 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16867 := params 2
abbrev ray16867 := rays 2
def bank16867 : Fin 1 → Cell := oneBank p16867 ray16867
theorem signs16867 : ∀ j, Signs p16867 (bank16867 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16868 := params 3
abbrev ray16868 := rays 3
def bank16868 : Fin 1 → Cell := oneBank p16868 ray16868
theorem signs16868 : ∀ j, Signs p16868 (bank16868 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16869 := params 4
abbrev ray16869 := rays 4
def bank16869 : Fin 1 → Cell := oneBank p16869 ray16869
theorem signs16869 : ∀ j, Signs p16869 (bank16869 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16870 := params 5
abbrev ray16870 := rays 5
def bank16870 : Fin 1 → Cell := oneBank p16870 ray16870
theorem signs16870 : ∀ j, Signs p16870 (bank16870 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16871 := params 6
abbrev ray16871 := rays 6
def bank16871 : Fin 1 → Cell := oneBank p16871 ray16871
theorem signs16871 : ∀ j, Signs p16871 (bank16871 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16872 := params 7
abbrev ray16872 := rays 7
def bank16872 : Fin 1 → Cell := oneBank p16872 ray16872
theorem signs16872 : ∀ j, Signs p16872 (bank16872 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16873 := params 8
abbrev ray16873 := rays 8
def bank16873 : Fin 1 → Cell := oneBank p16873 ray16873
theorem signs16873 : ∀ j, Signs p16873 (bank16873 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16874 := params 9
abbrev ray16874 := rays 9
def bank16874 : Fin 1 → Cell := oneBank p16874 ray16874
theorem signs16874 : ∀ j, Signs p16874 (bank16874 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16875 := params 10
abbrev ray16875 := rays 10
def bank16875 : Fin 1 → Cell := oneBank p16875 ray16875
theorem signs16875 : ∀ j, Signs p16875 (bank16875 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16876 := params 11
abbrev ray16876 := rays 11
def bank16876 : Fin 1 → Cell := oneBank p16876 ray16876
theorem signs16876 : ∀ j, Signs p16876 (bank16876 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16877 := params 12
abbrev ray16877 := rays 12
def bank16877 : Fin 1 → Cell := oneBank p16877 ray16877
theorem signs16877 : ∀ j, Signs p16877 (bank16877 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16878 := params 13
abbrev ray16878 := rays 13
def bank16878 : Fin 1 → Cell := oneBank p16878 ray16878
theorem signs16878 : ∀ j, Signs p16878 (bank16878 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16879 := params 14
abbrev ray16879 := rays 14
def bank16879 : Fin 1 → Cell := oneBank p16879 ray16879
theorem signs16879 : ∀ j, Signs p16879 (bank16879 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16880 := params 15
abbrev ray16880 := rays 15
def bank16880 : Fin 1 → Cell := oneBank p16880 ray16880
theorem signs16880 : ∀ j, Signs p16880 (bank16880 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16881 := params 16
abbrev ray16881 := rays 16
def bank16881 : Fin 1 → Cell := oneBank p16881 ray16881
theorem signs16881 : ∀ j, Signs p16881 (bank16881 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16882 := params 17
abbrev ray16882 := rays 17
def bank16882 : Fin 1 → Cell := oneBank p16882 ray16882
theorem signs16882 : ∀ j, Signs p16882 (bank16882 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16883 := params 18
abbrev ray16883 := rays 18
def bank16883 : Fin 1 → Cell := oneBank p16883 ray16883
theorem signs16883 : ∀ j, Signs p16883 (bank16883 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16884 := params 19
abbrev ray16884 := rays 19
def bank16884 : Fin 1 → Cell := oneBank p16884 ray16884
theorem signs16884 : ∀ j, Signs p16884 (bank16884 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16885 := params 20
abbrev ray16885 := rays 20
def bank16885 : Fin 1 → Cell := oneBank p16885 ray16885
theorem signs16885 : ∀ j, Signs p16885 (bank16885 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16886 := params 21
abbrev ray16886 := rays 21
def bank16886 : Fin 1 → Cell := oneBank p16886 ray16886
theorem signs16886 : ∀ j, Signs p16886 (bank16886 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16887 := params 22
abbrev ray16887 := rays 22
def bank16887 : Fin 1 → Cell := oneBank p16887 ray16887
theorem signs16887 : ∀ j, Signs p16887 (bank16887 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16888 := params 23
abbrev ray16888 := rays 23
def bank16888 : Fin 1 → Cell := oneBank p16888 ray16888
theorem signs16888 : ∀ j, Signs p16888 (bank16888 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16889 := params 24
abbrev ray16889 := rays 24
def bank16889 : Fin 1 → Cell := oneBank p16889 ray16889
theorem signs16889 : ∀ j, Signs p16889 (bank16889 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16890 := params 25
abbrev ray16890 := rays 25
def bank16890 : Fin 1 → Cell := oneBank p16890 ray16890
theorem signs16890 : ∀ j, Signs p16890 (bank16890 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16891 := params 26
abbrev ray16891 := rays 26
def bank16891 : Fin 1 → Cell := oneBank p16891 ray16891
theorem signs16891 : ∀ j, Signs p16891 (bank16891 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16892 := params 27
abbrev ray16892 := rays 27
def bank16892 : Fin 1 → Cell := oneBank p16892 ray16892
theorem signs16892 : ∀ j, Signs p16892 (bank16892 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16893 := params 28
abbrev ray16893 := rays 28
def bank16893 : Fin 1 → Cell := oneBank p16893 ray16893
theorem signs16893 : ∀ j, Signs p16893 (bank16893 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16894 := params 29
abbrev ray16894 := rays 29
def bank16894 : Fin 1 → Cell := oneBank p16894 ray16894
theorem signs16894 : ∀ j, Signs p16894 (bank16894 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16895 := params 30
abbrev ray16895 := rays 30
def bank16895 : Fin 1 → Cell := oneBank p16895 ray16895
theorem signs16895 : ∀ j, Signs p16895 (bank16895 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16896 := params 31
abbrev ray16896 := rays 31
def bank16896 : Fin 1 → Cell := oneBank p16896 ray16896
theorem signs16896 : ∀ j, Signs p16896 (bank16896 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16865_16896
