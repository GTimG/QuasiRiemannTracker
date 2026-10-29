/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09857_09888
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97522332395272,97521968693478,97521604971267,97521241228639,97520877465595,97520513682136,97520149878262,97519786053974,97519422209272,97519058344157,97518694458629,97518330552689,97517966626338,97517602679576,97517238712403,97516874724820,97516510716828,97516146688428,97515782639619,97515418570403,97515054480780,97514690370750,97514326240315,97513962089474,97513597918228,97513233726578,97512869514525,97512505282069,97512141029210,97511776755949,97511412462287,97511048148224,97510683813761]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9856+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9857 := params 0
abbrev ray9857 := rays 0
def bank9857 : Fin 2 → Cell := twoBank p9857 ray9857
theorem signs9857 : ∀ j, Signs p9857 (bank9857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9858 := params 1
abbrev ray9858 := rays 1
def bank9858 : Fin 2 → Cell := twoBank p9858 ray9858
theorem signs9858 : ∀ j, Signs p9858 (bank9858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9859 := params 2
abbrev ray9859 := rays 2
def bank9859 : Fin 2 → Cell := twoBank p9859 ray9859
theorem signs9859 : ∀ j, Signs p9859 (bank9859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9860 := params 3
abbrev ray9860 := rays 3
def bank9860 : Fin 2 → Cell := twoBank p9860 ray9860
theorem signs9860 : ∀ j, Signs p9860 (bank9860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9861 := params 4
abbrev ray9861 := rays 4
def bank9861 : Fin 2 → Cell := twoBank p9861 ray9861
theorem signs9861 : ∀ j, Signs p9861 (bank9861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9862 := params 5
abbrev ray9862 := rays 5
def bank9862 : Fin 2 → Cell := twoBank p9862 ray9862
theorem signs9862 : ∀ j, Signs p9862 (bank9862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9863 := params 6
abbrev ray9863 := rays 6
def bank9863 : Fin 2 → Cell := twoBank p9863 ray9863
theorem signs9863 : ∀ j, Signs p9863 (bank9863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9864 := params 7
abbrev ray9864 := rays 7
def bank9864 : Fin 2 → Cell := twoBank p9864 ray9864
theorem signs9864 : ∀ j, Signs p9864 (bank9864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9865 := params 8
abbrev ray9865 := rays 8
def bank9865 : Fin 2 → Cell := twoBank p9865 ray9865
theorem signs9865 : ∀ j, Signs p9865 (bank9865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9866 := params 9
abbrev ray9866 := rays 9
def bank9866 : Fin 2 → Cell := twoBank p9866 ray9866
theorem signs9866 : ∀ j, Signs p9866 (bank9866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9867 := params 10
abbrev ray9867 := rays 10
def bank9867 : Fin 2 → Cell := twoBank p9867 ray9867
theorem signs9867 : ∀ j, Signs p9867 (bank9867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9868 := params 11
abbrev ray9868 := rays 11
def bank9868 : Fin 2 → Cell := twoBank p9868 ray9868
theorem signs9868 : ∀ j, Signs p9868 (bank9868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9869 := params 12
abbrev ray9869 := rays 12
def bank9869 : Fin 2 → Cell := twoBank p9869 ray9869
theorem signs9869 : ∀ j, Signs p9869 (bank9869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9870 := params 13
abbrev ray9870 := rays 13
def bank9870 : Fin 2 → Cell := twoBank p9870 ray9870
theorem signs9870 : ∀ j, Signs p9870 (bank9870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9871 := params 14
abbrev ray9871 := rays 14
def bank9871 : Fin 2 → Cell := twoBank p9871 ray9871
theorem signs9871 : ∀ j, Signs p9871 (bank9871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9872 := params 15
abbrev ray9872 := rays 15
def bank9872 : Fin 2 → Cell := twoBank p9872 ray9872
theorem signs9872 : ∀ j, Signs p9872 (bank9872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9873 := params 16
abbrev ray9873 := rays 16
def bank9873 : Fin 2 → Cell := twoBank p9873 ray9873
theorem signs9873 : ∀ j, Signs p9873 (bank9873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9874 := params 17
abbrev ray9874 := rays 17
def bank9874 : Fin 2 → Cell := twoBank p9874 ray9874
theorem signs9874 : ∀ j, Signs p9874 (bank9874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9875 := params 18
abbrev ray9875 := rays 18
def bank9875 : Fin 2 → Cell := twoBank p9875 ray9875
theorem signs9875 : ∀ j, Signs p9875 (bank9875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9876 := params 19
abbrev ray9876 := rays 19
def bank9876 : Fin 2 → Cell := twoBank p9876 ray9876
theorem signs9876 : ∀ j, Signs p9876 (bank9876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9877 := params 20
abbrev ray9877 := rays 20
def bank9877 : Fin 2 → Cell := twoBank p9877 ray9877
theorem signs9877 : ∀ j, Signs p9877 (bank9877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9878 := params 21
abbrev ray9878 := rays 21
def bank9878 : Fin 2 → Cell := twoBank p9878 ray9878
theorem signs9878 : ∀ j, Signs p9878 (bank9878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9879 := params 22
abbrev ray9879 := rays 22
def bank9879 : Fin 2 → Cell := twoBank p9879 ray9879
theorem signs9879 : ∀ j, Signs p9879 (bank9879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9880 := params 23
abbrev ray9880 := rays 23
def bank9880 : Fin 2 → Cell := twoBank p9880 ray9880
theorem signs9880 : ∀ j, Signs p9880 (bank9880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9881 := params 24
abbrev ray9881 := rays 24
def bank9881 : Fin 2 → Cell := twoBank p9881 ray9881
theorem signs9881 : ∀ j, Signs p9881 (bank9881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9882 := params 25
abbrev ray9882 := rays 25
def bank9882 : Fin 2 → Cell := twoBank p9882 ray9882
theorem signs9882 : ∀ j, Signs p9882 (bank9882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9883 := params 26
abbrev ray9883 := rays 26
def bank9883 : Fin 2 → Cell := twoBank p9883 ray9883
theorem signs9883 : ∀ j, Signs p9883 (bank9883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9884 := params 27
abbrev ray9884 := rays 27
def bank9884 : Fin 2 → Cell := twoBank p9884 ray9884
theorem signs9884 : ∀ j, Signs p9884 (bank9884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9885 := params 28
abbrev ray9885 := rays 28
def bank9885 : Fin 2 → Cell := twoBank p9885 ray9885
theorem signs9885 : ∀ j, Signs p9885 (bank9885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9886 := params 29
abbrev ray9886 := rays 29
def bank9886 : Fin 2 → Cell := twoBank p9886 ray9886
theorem signs9886 : ∀ j, Signs p9886 (bank9886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9887 := params 30
abbrev ray9887 := rays 30
def bank9887 : Fin 2 → Cell := twoBank p9887 ray9887
theorem signs9887 : ∀ j, Signs p9887 (bank9887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9888 := params 31
abbrev ray9888 := rays 31
def bank9888 : Fin 2 → Cell := twoBank p9888 ray9888
theorem signs9888 : ∀ j, Signs p9888 (bank9888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09857_09888
