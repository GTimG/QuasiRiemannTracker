/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05921_05952
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98789213512674,98788935293907,98788657051906,98788378786672,98788100498206,98787822186508,98787543851580,98787265493422,98786987112036,98786708707422,98786430279581,98786151828514,98785873354222,98785594856706,98785316335967,98785037792005,98784759224822,98784480634418,98784202020794,98783923383952,98783644723892,98783366040615,98783087334121,98782808604412,98782529851489,98782251075352,98781972276003,98781693453442,98781414607670,98781135738688,98780856846497,98780577931098,98780298992492]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5920+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5921 := params 0
abbrev ray5921 := rays 0
def bank5921 : Fin 2 → Cell := twoBank p5921 ray5921
theorem signs5921 : ∀ j, Signs p5921 (bank5921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5922 := params 1
abbrev ray5922 := rays 1
def bank5922 : Fin 2 → Cell := twoBank p5922 ray5922
theorem signs5922 : ∀ j, Signs p5922 (bank5922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5923 := params 2
abbrev ray5923 := rays 2
def bank5923 : Fin 2 → Cell := twoBank p5923 ray5923
theorem signs5923 : ∀ j, Signs p5923 (bank5923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5924 := params 3
abbrev ray5924 := rays 3
def bank5924 : Fin 2 → Cell := twoBank p5924 ray5924
theorem signs5924 : ∀ j, Signs p5924 (bank5924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5925 := params 4
abbrev ray5925 := rays 4
def bank5925 : Fin 2 → Cell := twoBank p5925 ray5925
theorem signs5925 : ∀ j, Signs p5925 (bank5925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5926 := params 5
abbrev ray5926 := rays 5
def bank5926 : Fin 2 → Cell := twoBank p5926 ray5926
theorem signs5926 : ∀ j, Signs p5926 (bank5926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5927 := params 6
abbrev ray5927 := rays 6
def bank5927 : Fin 2 → Cell := twoBank p5927 ray5927
theorem signs5927 : ∀ j, Signs p5927 (bank5927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5928 := params 7
abbrev ray5928 := rays 7
def bank5928 : Fin 2 → Cell := twoBank p5928 ray5928
theorem signs5928 : ∀ j, Signs p5928 (bank5928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5929 := params 8
abbrev ray5929 := rays 8
def bank5929 : Fin 2 → Cell := twoBank p5929 ray5929
theorem signs5929 : ∀ j, Signs p5929 (bank5929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5930 := params 9
abbrev ray5930 := rays 9
def bank5930 : Fin 2 → Cell := twoBank p5930 ray5930
theorem signs5930 : ∀ j, Signs p5930 (bank5930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5931 := params 10
abbrev ray5931 := rays 10
def bank5931 : Fin 2 → Cell := twoBank p5931 ray5931
theorem signs5931 : ∀ j, Signs p5931 (bank5931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5932 := params 11
abbrev ray5932 := rays 11
def bank5932 : Fin 2 → Cell := twoBank p5932 ray5932
theorem signs5932 : ∀ j, Signs p5932 (bank5932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5933 := params 12
abbrev ray5933 := rays 12
def bank5933 : Fin 2 → Cell := twoBank p5933 ray5933
theorem signs5933 : ∀ j, Signs p5933 (bank5933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5934 := params 13
abbrev ray5934 := rays 13
def bank5934 : Fin 2 → Cell := twoBank p5934 ray5934
theorem signs5934 : ∀ j, Signs p5934 (bank5934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5935 := params 14
abbrev ray5935 := rays 14
def bank5935 : Fin 2 → Cell := twoBank p5935 ray5935
theorem signs5935 : ∀ j, Signs p5935 (bank5935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5936 := params 15
abbrev ray5936 := rays 15
def bank5936 : Fin 2 → Cell := twoBank p5936 ray5936
theorem signs5936 : ∀ j, Signs p5936 (bank5936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5937 := params 16
abbrev ray5937 := rays 16
def bank5937 : Fin 2 → Cell := twoBank p5937 ray5937
theorem signs5937 : ∀ j, Signs p5937 (bank5937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5938 := params 17
abbrev ray5938 := rays 17
def bank5938 : Fin 2 → Cell := twoBank p5938 ray5938
theorem signs5938 : ∀ j, Signs p5938 (bank5938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5939 := params 18
abbrev ray5939 := rays 18
def bank5939 : Fin 2 → Cell := twoBank p5939 ray5939
theorem signs5939 : ∀ j, Signs p5939 (bank5939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5940 := params 19
abbrev ray5940 := rays 19
def bank5940 : Fin 2 → Cell := twoBank p5940 ray5940
theorem signs5940 : ∀ j, Signs p5940 (bank5940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5941 := params 20
abbrev ray5941 := rays 20
def bank5941 : Fin 2 → Cell := twoBank p5941 ray5941
theorem signs5941 : ∀ j, Signs p5941 (bank5941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5942 := params 21
abbrev ray5942 := rays 21
def bank5942 : Fin 2 → Cell := twoBank p5942 ray5942
theorem signs5942 : ∀ j, Signs p5942 (bank5942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5943 := params 22
abbrev ray5943 := rays 22
def bank5943 : Fin 2 → Cell := twoBank p5943 ray5943
theorem signs5943 : ∀ j, Signs p5943 (bank5943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5944 := params 23
abbrev ray5944 := rays 23
def bank5944 : Fin 2 → Cell := twoBank p5944 ray5944
theorem signs5944 : ∀ j, Signs p5944 (bank5944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5945 := params 24
abbrev ray5945 := rays 24
def bank5945 : Fin 2 → Cell := twoBank p5945 ray5945
theorem signs5945 : ∀ j, Signs p5945 (bank5945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5946 := params 25
abbrev ray5946 := rays 25
def bank5946 : Fin 2 → Cell := twoBank p5946 ray5946
theorem signs5946 : ∀ j, Signs p5946 (bank5946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5947 := params 26
abbrev ray5947 := rays 26
def bank5947 : Fin 2 → Cell := twoBank p5947 ray5947
theorem signs5947 : ∀ j, Signs p5947 (bank5947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5948 := params 27
abbrev ray5948 := rays 27
def bank5948 : Fin 2 → Cell := twoBank p5948 ray5948
theorem signs5948 : ∀ j, Signs p5948 (bank5948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5949 := params 28
abbrev ray5949 := rays 28
def bank5949 : Fin 2 → Cell := twoBank p5949 ray5949
theorem signs5949 : ∀ j, Signs p5949 (bank5949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5950 := params 29
abbrev ray5950 := rays 29
def bank5950 : Fin 2 → Cell := twoBank p5950 ray5950
theorem signs5950 : ∀ j, Signs p5950 (bank5950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5951 := params 30
abbrev ray5951 := rays 30
def bank5951 : Fin 2 → Cell := twoBank p5951 ray5951
theorem signs5951 : ∀ j, Signs p5951 (bank5951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5952 := params 31
abbrev ray5952 := rays 31
def bank5952 : Fin 2 → Cell := twoBank p5952 ray5952
theorem signs5952 : ∀ j, Signs p5952 (bank5952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05921_05952
