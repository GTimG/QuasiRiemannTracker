/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05889_05920
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98798104240327,98797826765520,98797549267450,98797271746118,98796994201526,98796716633674,98796439042563,98796161428193,98795883790566,98795606129683,98795328445544,98795050738151,98794773007504,98794495253604,98794217476452,98793939676049,98793661852396,98793384005494,98793106135344,98792828241947,98792550325303,98792272385413,98791994422279,98791716435901,98791438426280,98791160393417,98790882337313,98790604257969,98790326155385,98790048029563,98789769880503,98789491708206,98789213512674]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5888+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5889 := params 0
abbrev ray5889 := rays 0
def bank5889 : Fin 2 → Cell := twoBank p5889 ray5889
theorem signs5889 : ∀ j, Signs p5889 (bank5889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5890 := params 1
abbrev ray5890 := rays 1
def bank5890 : Fin 2 → Cell := twoBank p5890 ray5890
theorem signs5890 : ∀ j, Signs p5890 (bank5890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5891 := params 2
abbrev ray5891 := rays 2
def bank5891 : Fin 2 → Cell := twoBank p5891 ray5891
theorem signs5891 : ∀ j, Signs p5891 (bank5891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5892 := params 3
abbrev ray5892 := rays 3
def bank5892 : Fin 2 → Cell := twoBank p5892 ray5892
theorem signs5892 : ∀ j, Signs p5892 (bank5892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5893 := params 4
abbrev ray5893 := rays 4
def bank5893 : Fin 2 → Cell := twoBank p5893 ray5893
theorem signs5893 : ∀ j, Signs p5893 (bank5893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5894 := params 5
abbrev ray5894 := rays 5
def bank5894 : Fin 2 → Cell := twoBank p5894 ray5894
theorem signs5894 : ∀ j, Signs p5894 (bank5894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5895 := params 6
abbrev ray5895 := rays 6
def bank5895 : Fin 2 → Cell := twoBank p5895 ray5895
theorem signs5895 : ∀ j, Signs p5895 (bank5895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5896 := params 7
abbrev ray5896 := rays 7
def bank5896 : Fin 2 → Cell := twoBank p5896 ray5896
theorem signs5896 : ∀ j, Signs p5896 (bank5896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5897 := params 8
abbrev ray5897 := rays 8
def bank5897 : Fin 2 → Cell := twoBank p5897 ray5897
theorem signs5897 : ∀ j, Signs p5897 (bank5897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5898 := params 9
abbrev ray5898 := rays 9
def bank5898 : Fin 2 → Cell := twoBank p5898 ray5898
theorem signs5898 : ∀ j, Signs p5898 (bank5898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5899 := params 10
abbrev ray5899 := rays 10
def bank5899 : Fin 2 → Cell := twoBank p5899 ray5899
theorem signs5899 : ∀ j, Signs p5899 (bank5899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5900 := params 11
abbrev ray5900 := rays 11
def bank5900 : Fin 2 → Cell := twoBank p5900 ray5900
theorem signs5900 : ∀ j, Signs p5900 (bank5900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5901 := params 12
abbrev ray5901 := rays 12
def bank5901 : Fin 2 → Cell := twoBank p5901 ray5901
theorem signs5901 : ∀ j, Signs p5901 (bank5901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5902 := params 13
abbrev ray5902 := rays 13
def bank5902 : Fin 2 → Cell := twoBank p5902 ray5902
theorem signs5902 : ∀ j, Signs p5902 (bank5902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5903 := params 14
abbrev ray5903 := rays 14
def bank5903 : Fin 2 → Cell := twoBank p5903 ray5903
theorem signs5903 : ∀ j, Signs p5903 (bank5903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5904 := params 15
abbrev ray5904 := rays 15
def bank5904 : Fin 2 → Cell := twoBank p5904 ray5904
theorem signs5904 : ∀ j, Signs p5904 (bank5904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5905 := params 16
abbrev ray5905 := rays 16
def bank5905 : Fin 2 → Cell := twoBank p5905 ray5905
theorem signs5905 : ∀ j, Signs p5905 (bank5905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5906 := params 17
abbrev ray5906 := rays 17
def bank5906 : Fin 2 → Cell := twoBank p5906 ray5906
theorem signs5906 : ∀ j, Signs p5906 (bank5906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5907 := params 18
abbrev ray5907 := rays 18
def bank5907 : Fin 2 → Cell := twoBank p5907 ray5907
theorem signs5907 : ∀ j, Signs p5907 (bank5907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5908 := params 19
abbrev ray5908 := rays 19
def bank5908 : Fin 2 → Cell := twoBank p5908 ray5908
theorem signs5908 : ∀ j, Signs p5908 (bank5908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5909 := params 20
abbrev ray5909 := rays 20
def bank5909 : Fin 2 → Cell := twoBank p5909 ray5909
theorem signs5909 : ∀ j, Signs p5909 (bank5909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5910 := params 21
abbrev ray5910 := rays 21
def bank5910 : Fin 2 → Cell := twoBank p5910 ray5910
theorem signs5910 : ∀ j, Signs p5910 (bank5910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5911 := params 22
abbrev ray5911 := rays 22
def bank5911 : Fin 2 → Cell := twoBank p5911 ray5911
theorem signs5911 : ∀ j, Signs p5911 (bank5911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5912 := params 23
abbrev ray5912 := rays 23
def bank5912 : Fin 2 → Cell := twoBank p5912 ray5912
theorem signs5912 : ∀ j, Signs p5912 (bank5912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5913 := params 24
abbrev ray5913 := rays 24
def bank5913 : Fin 2 → Cell := twoBank p5913 ray5913
theorem signs5913 : ∀ j, Signs p5913 (bank5913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5914 := params 25
abbrev ray5914 := rays 25
def bank5914 : Fin 2 → Cell := twoBank p5914 ray5914
theorem signs5914 : ∀ j, Signs p5914 (bank5914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5915 := params 26
abbrev ray5915 := rays 26
def bank5915 : Fin 2 → Cell := twoBank p5915 ray5915
theorem signs5915 : ∀ j, Signs p5915 (bank5915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5916 := params 27
abbrev ray5916 := rays 27
def bank5916 : Fin 2 → Cell := twoBank p5916 ray5916
theorem signs5916 : ∀ j, Signs p5916 (bank5916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5917 := params 28
abbrev ray5917 := rays 28
def bank5917 : Fin 2 → Cell := twoBank p5917 ray5917
theorem signs5917 : ∀ j, Signs p5917 (bank5917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5918 := params 29
abbrev ray5918 := rays 29
def bank5918 : Fin 2 → Cell := twoBank p5918 ray5918
theorem signs5918 : ∀ j, Signs p5918 (bank5918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5919 := params 30
abbrev ray5919 := rays 30
def bank5919 : Fin 2 → Cell := twoBank p5919 ray5919
theorem signs5919 : ∀ j, Signs p5919 (bank5919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5920 := params 31
abbrev ray5920 := rays 31
def bank5920 : Fin 2 → Cell := twoBank p5920 ray5920
theorem signs5920 : ∀ j, Signs p5920 (bank5920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05889_05920
