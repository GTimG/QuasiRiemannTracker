/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05857_05888
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98806971146123,98806694416194,98806417662973,98806140886462,98805864086661,98805587263572,98805310417195,98805033547531,98804756654581,98804479738346,98804202798827,98803925836025,98803648849940,98803371840574,98803094807927,98802817752000,98802540672795,98802263570312,98801986444552,98801709295516,98801432123204,98801154927618,98800877708759,98800600466627,98800323201224,98800045912550,98799768600606,98799491265393,98799213906912,98798936525164,98798659120150,98798381691871,98798104240327]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5856+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5857 := params 0
abbrev ray5857 := rays 0
def bank5857 : Fin 2 → Cell := twoBank p5857 ray5857
theorem signs5857 : ∀ j, Signs p5857 (bank5857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5858 := params 1
abbrev ray5858 := rays 1
def bank5858 : Fin 2 → Cell := twoBank p5858 ray5858
theorem signs5858 : ∀ j, Signs p5858 (bank5858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5859 := params 2
abbrev ray5859 := rays 2
def bank5859 : Fin 2 → Cell := twoBank p5859 ray5859
theorem signs5859 : ∀ j, Signs p5859 (bank5859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5860 := params 3
abbrev ray5860 := rays 3
def bank5860 : Fin 2 → Cell := twoBank p5860 ray5860
theorem signs5860 : ∀ j, Signs p5860 (bank5860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5861 := params 4
abbrev ray5861 := rays 4
def bank5861 : Fin 2 → Cell := twoBank p5861 ray5861
theorem signs5861 : ∀ j, Signs p5861 (bank5861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5862 := params 5
abbrev ray5862 := rays 5
def bank5862 : Fin 2 → Cell := twoBank p5862 ray5862
theorem signs5862 : ∀ j, Signs p5862 (bank5862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5863 := params 6
abbrev ray5863 := rays 6
def bank5863 : Fin 2 → Cell := twoBank p5863 ray5863
theorem signs5863 : ∀ j, Signs p5863 (bank5863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5864 := params 7
abbrev ray5864 := rays 7
def bank5864 : Fin 2 → Cell := twoBank p5864 ray5864
theorem signs5864 : ∀ j, Signs p5864 (bank5864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5865 := params 8
abbrev ray5865 := rays 8
def bank5865 : Fin 2 → Cell := twoBank p5865 ray5865
theorem signs5865 : ∀ j, Signs p5865 (bank5865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5866 := params 9
abbrev ray5866 := rays 9
def bank5866 : Fin 2 → Cell := twoBank p5866 ray5866
theorem signs5866 : ∀ j, Signs p5866 (bank5866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5867 := params 10
abbrev ray5867 := rays 10
def bank5867 : Fin 2 → Cell := twoBank p5867 ray5867
theorem signs5867 : ∀ j, Signs p5867 (bank5867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5868 := params 11
abbrev ray5868 := rays 11
def bank5868 : Fin 2 → Cell := twoBank p5868 ray5868
theorem signs5868 : ∀ j, Signs p5868 (bank5868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5869 := params 12
abbrev ray5869 := rays 12
def bank5869 : Fin 2 → Cell := twoBank p5869 ray5869
theorem signs5869 : ∀ j, Signs p5869 (bank5869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5870 := params 13
abbrev ray5870 := rays 13
def bank5870 : Fin 2 → Cell := twoBank p5870 ray5870
theorem signs5870 : ∀ j, Signs p5870 (bank5870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5871 := params 14
abbrev ray5871 := rays 14
def bank5871 : Fin 2 → Cell := twoBank p5871 ray5871
theorem signs5871 : ∀ j, Signs p5871 (bank5871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5872 := params 15
abbrev ray5872 := rays 15
def bank5872 : Fin 2 → Cell := twoBank p5872 ray5872
theorem signs5872 : ∀ j, Signs p5872 (bank5872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5873 := params 16
abbrev ray5873 := rays 16
def bank5873 : Fin 2 → Cell := twoBank p5873 ray5873
theorem signs5873 : ∀ j, Signs p5873 (bank5873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5874 := params 17
abbrev ray5874 := rays 17
def bank5874 : Fin 2 → Cell := twoBank p5874 ray5874
theorem signs5874 : ∀ j, Signs p5874 (bank5874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5875 := params 18
abbrev ray5875 := rays 18
def bank5875 : Fin 2 → Cell := twoBank p5875 ray5875
theorem signs5875 : ∀ j, Signs p5875 (bank5875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5876 := params 19
abbrev ray5876 := rays 19
def bank5876 : Fin 2 → Cell := twoBank p5876 ray5876
theorem signs5876 : ∀ j, Signs p5876 (bank5876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5877 := params 20
abbrev ray5877 := rays 20
def bank5877 : Fin 2 → Cell := twoBank p5877 ray5877
theorem signs5877 : ∀ j, Signs p5877 (bank5877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5878 := params 21
abbrev ray5878 := rays 21
def bank5878 : Fin 2 → Cell := twoBank p5878 ray5878
theorem signs5878 : ∀ j, Signs p5878 (bank5878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5879 := params 22
abbrev ray5879 := rays 22
def bank5879 : Fin 2 → Cell := twoBank p5879 ray5879
theorem signs5879 : ∀ j, Signs p5879 (bank5879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5880 := params 23
abbrev ray5880 := rays 23
def bank5880 : Fin 2 → Cell := twoBank p5880 ray5880
theorem signs5880 : ∀ j, Signs p5880 (bank5880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5881 := params 24
abbrev ray5881 := rays 24
def bank5881 : Fin 2 → Cell := twoBank p5881 ray5881
theorem signs5881 : ∀ j, Signs p5881 (bank5881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5882 := params 25
abbrev ray5882 := rays 25
def bank5882 : Fin 2 → Cell := twoBank p5882 ray5882
theorem signs5882 : ∀ j, Signs p5882 (bank5882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5883 := params 26
abbrev ray5883 := rays 26
def bank5883 : Fin 2 → Cell := twoBank p5883 ray5883
theorem signs5883 : ∀ j, Signs p5883 (bank5883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5884 := params 27
abbrev ray5884 := rays 27
def bank5884 : Fin 2 → Cell := twoBank p5884 ray5884
theorem signs5884 : ∀ j, Signs p5884 (bank5884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5885 := params 28
abbrev ray5885 := rays 28
def bank5885 : Fin 2 → Cell := twoBank p5885 ray5885
theorem signs5885 : ∀ j, Signs p5885 (bank5885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5886 := params 29
abbrev ray5886 := rays 29
def bank5886 : Fin 2 → Cell := twoBank p5886 ray5886
theorem signs5886 : ∀ j, Signs p5886 (bank5886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5887 := params 30
abbrev ray5887 := rays 30
def bank5887 : Fin 2 → Cell := twoBank p5887 ray5887
theorem signs5887 : ∀ j, Signs p5887 (bank5887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5888 := params 31
abbrev ray5888 := rays 31
def bank5888 : Fin 2 → Cell := twoBank p5888 ray5888
theorem signs5888 : ∀ j, Signs p5888 (bank5888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05857_05888
