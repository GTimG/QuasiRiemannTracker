/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13857_13888
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95910984154469,95910545271309,95910106371908,95909667456266,95909228524384,95908789576261,95908350611898,95907911631294,95907472634450,95907033621367,95906594592044,95906155546482,95905716484680,95905277406639,95904838312360,95904399201842,95903960075086,95903520932091,95903081772858,95902642597387,95902203405679,95901764197733,95901324973550,95900885733130,95900446476473,95900007203580,95899567914450,95899128609084,95898689287482,95898249949644,95897810595570,95897371225261,95896931838716]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13856+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13857 := params 0
abbrev ray13857 := rays 0
def bank13857 : Fin 1 → Cell := oneBank p13857 ray13857
theorem signs13857 : ∀ j, Signs p13857 (bank13857 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13858 := params 1
abbrev ray13858 := rays 1
def bank13858 : Fin 1 → Cell := oneBank p13858 ray13858
theorem signs13858 : ∀ j, Signs p13858 (bank13858 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13859 := params 2
abbrev ray13859 := rays 2
def bank13859 : Fin 1 → Cell := oneBank p13859 ray13859
theorem signs13859 : ∀ j, Signs p13859 (bank13859 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13860 := params 3
abbrev ray13860 := rays 3
def bank13860 : Fin 1 → Cell := oneBank p13860 ray13860
theorem signs13860 : ∀ j, Signs p13860 (bank13860 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13861 := params 4
abbrev ray13861 := rays 4
def bank13861 : Fin 1 → Cell := oneBank p13861 ray13861
theorem signs13861 : ∀ j, Signs p13861 (bank13861 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13862 := params 5
abbrev ray13862 := rays 5
def bank13862 : Fin 1 → Cell := oneBank p13862 ray13862
theorem signs13862 : ∀ j, Signs p13862 (bank13862 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13863 := params 6
abbrev ray13863 := rays 6
def bank13863 : Fin 1 → Cell := oneBank p13863 ray13863
theorem signs13863 : ∀ j, Signs p13863 (bank13863 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13864 := params 7
abbrev ray13864 := rays 7
def bank13864 : Fin 1 → Cell := oneBank p13864 ray13864
theorem signs13864 : ∀ j, Signs p13864 (bank13864 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13865 := params 8
abbrev ray13865 := rays 8
def bank13865 : Fin 1 → Cell := oneBank p13865 ray13865
theorem signs13865 : ∀ j, Signs p13865 (bank13865 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13866 := params 9
abbrev ray13866 := rays 9
def bank13866 : Fin 1 → Cell := oneBank p13866 ray13866
theorem signs13866 : ∀ j, Signs p13866 (bank13866 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13867 := params 10
abbrev ray13867 := rays 10
def bank13867 : Fin 1 → Cell := oneBank p13867 ray13867
theorem signs13867 : ∀ j, Signs p13867 (bank13867 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13868 := params 11
abbrev ray13868 := rays 11
def bank13868 : Fin 1 → Cell := oneBank p13868 ray13868
theorem signs13868 : ∀ j, Signs p13868 (bank13868 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13869 := params 12
abbrev ray13869 := rays 12
def bank13869 : Fin 1 → Cell := oneBank p13869 ray13869
theorem signs13869 : ∀ j, Signs p13869 (bank13869 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13870 := params 13
abbrev ray13870 := rays 13
def bank13870 : Fin 1 → Cell := oneBank p13870 ray13870
theorem signs13870 : ∀ j, Signs p13870 (bank13870 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13871 := params 14
abbrev ray13871 := rays 14
def bank13871 : Fin 1 → Cell := oneBank p13871 ray13871
theorem signs13871 : ∀ j, Signs p13871 (bank13871 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13872 := params 15
abbrev ray13872 := rays 15
def bank13872 : Fin 1 → Cell := oneBank p13872 ray13872
theorem signs13872 : ∀ j, Signs p13872 (bank13872 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13873 := params 16
abbrev ray13873 := rays 16
def bank13873 : Fin 1 → Cell := oneBank p13873 ray13873
theorem signs13873 : ∀ j, Signs p13873 (bank13873 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13874 := params 17
abbrev ray13874 := rays 17
def bank13874 : Fin 1 → Cell := oneBank p13874 ray13874
theorem signs13874 : ∀ j, Signs p13874 (bank13874 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13875 := params 18
abbrev ray13875 := rays 18
def bank13875 : Fin 1 → Cell := oneBank p13875 ray13875
theorem signs13875 : ∀ j, Signs p13875 (bank13875 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13876 := params 19
abbrev ray13876 := rays 19
def bank13876 : Fin 1 → Cell := oneBank p13876 ray13876
theorem signs13876 : ∀ j, Signs p13876 (bank13876 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13877 := params 20
abbrev ray13877 := rays 20
def bank13877 : Fin 1 → Cell := oneBank p13877 ray13877
theorem signs13877 : ∀ j, Signs p13877 (bank13877 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13878 := params 21
abbrev ray13878 := rays 21
def bank13878 : Fin 1 → Cell := oneBank p13878 ray13878
theorem signs13878 : ∀ j, Signs p13878 (bank13878 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13879 := params 22
abbrev ray13879 := rays 22
def bank13879 : Fin 1 → Cell := oneBank p13879 ray13879
theorem signs13879 : ∀ j, Signs p13879 (bank13879 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13880 := params 23
abbrev ray13880 := rays 23
def bank13880 : Fin 1 → Cell := oneBank p13880 ray13880
theorem signs13880 : ∀ j, Signs p13880 (bank13880 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13881 := params 24
abbrev ray13881 := rays 24
def bank13881 : Fin 1 → Cell := oneBank p13881 ray13881
theorem signs13881 : ∀ j, Signs p13881 (bank13881 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13882 := params 25
abbrev ray13882 := rays 25
def bank13882 : Fin 1 → Cell := oneBank p13882 ray13882
theorem signs13882 : ∀ j, Signs p13882 (bank13882 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13883 := params 26
abbrev ray13883 := rays 26
def bank13883 : Fin 1 → Cell := oneBank p13883 ray13883
theorem signs13883 : ∀ j, Signs p13883 (bank13883 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13884 := params 27
abbrev ray13884 := rays 27
def bank13884 : Fin 1 → Cell := oneBank p13884 ray13884
theorem signs13884 : ∀ j, Signs p13884 (bank13884 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13885 := params 28
abbrev ray13885 := rays 28
def bank13885 : Fin 1 → Cell := oneBank p13885 ray13885
theorem signs13885 : ∀ j, Signs p13885 (bank13885 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13886 := params 29
abbrev ray13886 := rays 29
def bank13886 : Fin 1 → Cell := oneBank p13886 ray13886
theorem signs13886 : ∀ j, Signs p13886 (bank13886 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13887 := params 30
abbrev ray13887 := rays 30
def bank13887 : Fin 1 → Cell := oneBank p13887 ray13887
theorem signs13887 : ∀ j, Signs p13887 (bank13887 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13888 := params 31
abbrev ray13888 := rays 31
def bank13888 : Fin 1 → Cell := oneBank p13888 ray13888
theorem signs13888 : ∀ j, Signs p13888 (bank13888 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13857_13888
