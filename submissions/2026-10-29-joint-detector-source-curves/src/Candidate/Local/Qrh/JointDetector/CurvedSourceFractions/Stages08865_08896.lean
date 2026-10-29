/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08865_08896
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97872973911381,97872630751903,97872287571416,97871944369919,97871601147414,97871257903901,97870914639381,97870571353854,97870228047321,97869884719783,97869541371240,97869198001693,97868854611142,97868511199588,97868167767032,97867824313475,97867480838917,97867137343358,97866793826800,97866450289243,97866106730687,97865763151133,97865419550582,97865075929035,97864732286492,97864388622954,97864044938421,97863701232894,97863357506374,97863013758861,97862669990356,97862326200859,97861982390371]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8864+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8865 := params 0
abbrev ray8865 := rays 0
def bank8865 : Fin 2 → Cell := twoBank p8865 ray8865
theorem signs8865 : ∀ j, Signs p8865 (bank8865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8866 := params 1
abbrev ray8866 := rays 1
def bank8866 : Fin 2 → Cell := twoBank p8866 ray8866
theorem signs8866 : ∀ j, Signs p8866 (bank8866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8867 := params 2
abbrev ray8867 := rays 2
def bank8867 : Fin 2 → Cell := twoBank p8867 ray8867
theorem signs8867 : ∀ j, Signs p8867 (bank8867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8868 := params 3
abbrev ray8868 := rays 3
def bank8868 : Fin 2 → Cell := twoBank p8868 ray8868
theorem signs8868 : ∀ j, Signs p8868 (bank8868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8869 := params 4
abbrev ray8869 := rays 4
def bank8869 : Fin 2 → Cell := twoBank p8869 ray8869
theorem signs8869 : ∀ j, Signs p8869 (bank8869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8870 := params 5
abbrev ray8870 := rays 5
def bank8870 : Fin 2 → Cell := twoBank p8870 ray8870
theorem signs8870 : ∀ j, Signs p8870 (bank8870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8871 := params 6
abbrev ray8871 := rays 6
def bank8871 : Fin 2 → Cell := twoBank p8871 ray8871
theorem signs8871 : ∀ j, Signs p8871 (bank8871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8872 := params 7
abbrev ray8872 := rays 7
def bank8872 : Fin 2 → Cell := twoBank p8872 ray8872
theorem signs8872 : ∀ j, Signs p8872 (bank8872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8873 := params 8
abbrev ray8873 := rays 8
def bank8873 : Fin 2 → Cell := twoBank p8873 ray8873
theorem signs8873 : ∀ j, Signs p8873 (bank8873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8874 := params 9
abbrev ray8874 := rays 9
def bank8874 : Fin 2 → Cell := twoBank p8874 ray8874
theorem signs8874 : ∀ j, Signs p8874 (bank8874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8875 := params 10
abbrev ray8875 := rays 10
def bank8875 : Fin 2 → Cell := twoBank p8875 ray8875
theorem signs8875 : ∀ j, Signs p8875 (bank8875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8876 := params 11
abbrev ray8876 := rays 11
def bank8876 : Fin 2 → Cell := twoBank p8876 ray8876
theorem signs8876 : ∀ j, Signs p8876 (bank8876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8877 := params 12
abbrev ray8877 := rays 12
def bank8877 : Fin 2 → Cell := twoBank p8877 ray8877
theorem signs8877 : ∀ j, Signs p8877 (bank8877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8878 := params 13
abbrev ray8878 := rays 13
def bank8878 : Fin 2 → Cell := twoBank p8878 ray8878
theorem signs8878 : ∀ j, Signs p8878 (bank8878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8879 := params 14
abbrev ray8879 := rays 14
def bank8879 : Fin 2 → Cell := twoBank p8879 ray8879
theorem signs8879 : ∀ j, Signs p8879 (bank8879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8880 := params 15
abbrev ray8880 := rays 15
def bank8880 : Fin 2 → Cell := twoBank p8880 ray8880
theorem signs8880 : ∀ j, Signs p8880 (bank8880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8881 := params 16
abbrev ray8881 := rays 16
def bank8881 : Fin 2 → Cell := twoBank p8881 ray8881
theorem signs8881 : ∀ j, Signs p8881 (bank8881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8882 := params 17
abbrev ray8882 := rays 17
def bank8882 : Fin 2 → Cell := twoBank p8882 ray8882
theorem signs8882 : ∀ j, Signs p8882 (bank8882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8883 := params 18
abbrev ray8883 := rays 18
def bank8883 : Fin 2 → Cell := twoBank p8883 ray8883
theorem signs8883 : ∀ j, Signs p8883 (bank8883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8884 := params 19
abbrev ray8884 := rays 19
def bank8884 : Fin 2 → Cell := twoBank p8884 ray8884
theorem signs8884 : ∀ j, Signs p8884 (bank8884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8885 := params 20
abbrev ray8885 := rays 20
def bank8885 : Fin 2 → Cell := twoBank p8885 ray8885
theorem signs8885 : ∀ j, Signs p8885 (bank8885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8886 := params 21
abbrev ray8886 := rays 21
def bank8886 : Fin 2 → Cell := twoBank p8886 ray8886
theorem signs8886 : ∀ j, Signs p8886 (bank8886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8887 := params 22
abbrev ray8887 := rays 22
def bank8887 : Fin 2 → Cell := twoBank p8887 ray8887
theorem signs8887 : ∀ j, Signs p8887 (bank8887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8888 := params 23
abbrev ray8888 := rays 23
def bank8888 : Fin 2 → Cell := twoBank p8888 ray8888
theorem signs8888 : ∀ j, Signs p8888 (bank8888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8889 := params 24
abbrev ray8889 := rays 24
def bank8889 : Fin 2 → Cell := twoBank p8889 ray8889
theorem signs8889 : ∀ j, Signs p8889 (bank8889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8890 := params 25
abbrev ray8890 := rays 25
def bank8890 : Fin 2 → Cell := twoBank p8890 ray8890
theorem signs8890 : ∀ j, Signs p8890 (bank8890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8891 := params 26
abbrev ray8891 := rays 26
def bank8891 : Fin 2 → Cell := twoBank p8891 ray8891
theorem signs8891 : ∀ j, Signs p8891 (bank8891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8892 := params 27
abbrev ray8892 := rays 27
def bank8892 : Fin 2 → Cell := twoBank p8892 ray8892
theorem signs8892 : ∀ j, Signs p8892 (bank8892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8893 := params 28
abbrev ray8893 := rays 28
def bank8893 : Fin 2 → Cell := twoBank p8893 ray8893
theorem signs8893 : ∀ j, Signs p8893 (bank8893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8894 := params 29
abbrev ray8894 := rays 29
def bank8894 : Fin 2 → Cell := twoBank p8894 ray8894
theorem signs8894 : ∀ j, Signs p8894 (bank8894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8895 := params 30
abbrev ray8895 := rays 30
def bank8895 : Fin 2 → Cell := twoBank p8895 ray8895
theorem signs8895 : ∀ j, Signs p8895 (bank8895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8896 := params 31
abbrev ray8896 := rays 31
def bank8896 : Fin 2 → Cell := twoBank p8896 ray8896
theorem signs8896 : ∀ j, Signs p8896 (bank8896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08865_08896
