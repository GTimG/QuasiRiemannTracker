/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08833_08864
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97883943917689,97883601430860,97883258923001,97882916394112,97882573844195,97882231273249,97881888681276,97881546068276,97881203434250,97880860779198,97880518103121,97880175406020,97879832687895,97879489948747,97879147188576,97878804407383,97878461605169,97878118781935,97877775937681,97877433072407,97877090186115,97876747278805,97876404350477,97876061401132,97875718430771,97875375439395,97875032427004,97874689393599,97874346339180,97874003263748,97873660167304,97873317049848,97872973911381]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8832+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8833 := params 0
abbrev ray8833 := rays 0
def bank8833 : Fin 2 → Cell := twoBank p8833 ray8833
theorem signs8833 : ∀ j, Signs p8833 (bank8833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8834 := params 1
abbrev ray8834 := rays 1
def bank8834 : Fin 2 → Cell := twoBank p8834 ray8834
theorem signs8834 : ∀ j, Signs p8834 (bank8834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8835 := params 2
abbrev ray8835 := rays 2
def bank8835 : Fin 2 → Cell := twoBank p8835 ray8835
theorem signs8835 : ∀ j, Signs p8835 (bank8835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8836 := params 3
abbrev ray8836 := rays 3
def bank8836 : Fin 2 → Cell := twoBank p8836 ray8836
theorem signs8836 : ∀ j, Signs p8836 (bank8836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8837 := params 4
abbrev ray8837 := rays 4
def bank8837 : Fin 2 → Cell := twoBank p8837 ray8837
theorem signs8837 : ∀ j, Signs p8837 (bank8837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8838 := params 5
abbrev ray8838 := rays 5
def bank8838 : Fin 2 → Cell := twoBank p8838 ray8838
theorem signs8838 : ∀ j, Signs p8838 (bank8838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8839 := params 6
abbrev ray8839 := rays 6
def bank8839 : Fin 2 → Cell := twoBank p8839 ray8839
theorem signs8839 : ∀ j, Signs p8839 (bank8839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8840 := params 7
abbrev ray8840 := rays 7
def bank8840 : Fin 2 → Cell := twoBank p8840 ray8840
theorem signs8840 : ∀ j, Signs p8840 (bank8840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8841 := params 8
abbrev ray8841 := rays 8
def bank8841 : Fin 2 → Cell := twoBank p8841 ray8841
theorem signs8841 : ∀ j, Signs p8841 (bank8841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8842 := params 9
abbrev ray8842 := rays 9
def bank8842 : Fin 2 → Cell := twoBank p8842 ray8842
theorem signs8842 : ∀ j, Signs p8842 (bank8842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8843 := params 10
abbrev ray8843 := rays 10
def bank8843 : Fin 2 → Cell := twoBank p8843 ray8843
theorem signs8843 : ∀ j, Signs p8843 (bank8843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8844 := params 11
abbrev ray8844 := rays 11
def bank8844 : Fin 2 → Cell := twoBank p8844 ray8844
theorem signs8844 : ∀ j, Signs p8844 (bank8844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8845 := params 12
abbrev ray8845 := rays 12
def bank8845 : Fin 2 → Cell := twoBank p8845 ray8845
theorem signs8845 : ∀ j, Signs p8845 (bank8845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8846 := params 13
abbrev ray8846 := rays 13
def bank8846 : Fin 2 → Cell := twoBank p8846 ray8846
theorem signs8846 : ∀ j, Signs p8846 (bank8846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8847 := params 14
abbrev ray8847 := rays 14
def bank8847 : Fin 2 → Cell := twoBank p8847 ray8847
theorem signs8847 : ∀ j, Signs p8847 (bank8847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8848 := params 15
abbrev ray8848 := rays 15
def bank8848 : Fin 2 → Cell := twoBank p8848 ray8848
theorem signs8848 : ∀ j, Signs p8848 (bank8848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8849 := params 16
abbrev ray8849 := rays 16
def bank8849 : Fin 2 → Cell := twoBank p8849 ray8849
theorem signs8849 : ∀ j, Signs p8849 (bank8849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8850 := params 17
abbrev ray8850 := rays 17
def bank8850 : Fin 2 → Cell := twoBank p8850 ray8850
theorem signs8850 : ∀ j, Signs p8850 (bank8850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8851 := params 18
abbrev ray8851 := rays 18
def bank8851 : Fin 2 → Cell := twoBank p8851 ray8851
theorem signs8851 : ∀ j, Signs p8851 (bank8851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8852 := params 19
abbrev ray8852 := rays 19
def bank8852 : Fin 2 → Cell := twoBank p8852 ray8852
theorem signs8852 : ∀ j, Signs p8852 (bank8852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8853 := params 20
abbrev ray8853 := rays 20
def bank8853 : Fin 2 → Cell := twoBank p8853 ray8853
theorem signs8853 : ∀ j, Signs p8853 (bank8853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8854 := params 21
abbrev ray8854 := rays 21
def bank8854 : Fin 2 → Cell := twoBank p8854 ray8854
theorem signs8854 : ∀ j, Signs p8854 (bank8854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8855 := params 22
abbrev ray8855 := rays 22
def bank8855 : Fin 2 → Cell := twoBank p8855 ray8855
theorem signs8855 : ∀ j, Signs p8855 (bank8855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8856 := params 23
abbrev ray8856 := rays 23
def bank8856 : Fin 2 → Cell := twoBank p8856 ray8856
theorem signs8856 : ∀ j, Signs p8856 (bank8856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8857 := params 24
abbrev ray8857 := rays 24
def bank8857 : Fin 2 → Cell := twoBank p8857 ray8857
theorem signs8857 : ∀ j, Signs p8857 (bank8857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8858 := params 25
abbrev ray8858 := rays 25
def bank8858 : Fin 2 → Cell := twoBank p8858 ray8858
theorem signs8858 : ∀ j, Signs p8858 (bank8858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8859 := params 26
abbrev ray8859 := rays 26
def bank8859 : Fin 2 → Cell := twoBank p8859 ray8859
theorem signs8859 : ∀ j, Signs p8859 (bank8859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8860 := params 27
abbrev ray8860 := rays 27
def bank8860 : Fin 2 → Cell := twoBank p8860 ray8860
theorem signs8860 : ∀ j, Signs p8860 (bank8860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8861 := params 28
abbrev ray8861 := rays 28
def bank8861 : Fin 2 → Cell := twoBank p8861 ray8861
theorem signs8861 : ∀ j, Signs p8861 (bank8861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8862 := params 29
abbrev ray8862 := rays 29
def bank8862 : Fin 2 → Cell := twoBank p8862 ray8862
theorem signs8862 : ∀ j, Signs p8862 (bank8862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8863 := params 30
abbrev ray8863 := rays 30
def bank8863 : Fin 2 → Cell := twoBank p8863 ray8863
theorem signs8863 : ∀ j, Signs p8863 (bank8863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8864 := params 31
abbrev ray8864 := rays 31
def bank8864 : Fin 2 → Cell := twoBank p8864 ray8864
theorem signs8864 : ∀ j, Signs p8864 (bank8864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08833_08864
