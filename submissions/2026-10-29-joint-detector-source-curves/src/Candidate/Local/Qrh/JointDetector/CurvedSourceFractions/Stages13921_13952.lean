/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13921_13952
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95882862898198,95882422975996,95881983037565,95881543082906,95881103112018,95880663124902,95880223121558,95879783101986,95879343066187,95878903014160,95878462945906,95878022861425,95877582760717,95877142643783,95876702510622,95876262361235,95875822195622,95875382013783,95874941815718,95874501601428,95874061370912,95873621124171,95873180861205,95872740582014,95872300286599,95871859974959,95871419647095,95870979303007,95870538942695,95870098566160,95869658173401,95869217764419,95868777339214]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13920+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13921 := params 0
abbrev ray13921 := rays 0
def bank13921 : Fin 1 → Cell := oneBank p13921 ray13921
theorem signs13921 : ∀ j, Signs p13921 (bank13921 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13922 := params 1
abbrev ray13922 := rays 1
def bank13922 : Fin 1 → Cell := oneBank p13922 ray13922
theorem signs13922 : ∀ j, Signs p13922 (bank13922 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13923 := params 2
abbrev ray13923 := rays 2
def bank13923 : Fin 1 → Cell := oneBank p13923 ray13923
theorem signs13923 : ∀ j, Signs p13923 (bank13923 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13924 := params 3
abbrev ray13924 := rays 3
def bank13924 : Fin 1 → Cell := oneBank p13924 ray13924
theorem signs13924 : ∀ j, Signs p13924 (bank13924 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13925 := params 4
abbrev ray13925 := rays 4
def bank13925 : Fin 1 → Cell := oneBank p13925 ray13925
theorem signs13925 : ∀ j, Signs p13925 (bank13925 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13926 := params 5
abbrev ray13926 := rays 5
def bank13926 : Fin 1 → Cell := oneBank p13926 ray13926
theorem signs13926 : ∀ j, Signs p13926 (bank13926 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13927 := params 6
abbrev ray13927 := rays 6
def bank13927 : Fin 1 → Cell := oneBank p13927 ray13927
theorem signs13927 : ∀ j, Signs p13927 (bank13927 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13928 := params 7
abbrev ray13928 := rays 7
def bank13928 : Fin 1 → Cell := oneBank p13928 ray13928
theorem signs13928 : ∀ j, Signs p13928 (bank13928 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13929 := params 8
abbrev ray13929 := rays 8
def bank13929 : Fin 1 → Cell := oneBank p13929 ray13929
theorem signs13929 : ∀ j, Signs p13929 (bank13929 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13930 := params 9
abbrev ray13930 := rays 9
def bank13930 : Fin 1 → Cell := oneBank p13930 ray13930
theorem signs13930 : ∀ j, Signs p13930 (bank13930 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13931 := params 10
abbrev ray13931 := rays 10
def bank13931 : Fin 1 → Cell := oneBank p13931 ray13931
theorem signs13931 : ∀ j, Signs p13931 (bank13931 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13932 := params 11
abbrev ray13932 := rays 11
def bank13932 : Fin 1 → Cell := oneBank p13932 ray13932
theorem signs13932 : ∀ j, Signs p13932 (bank13932 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13933 := params 12
abbrev ray13933 := rays 12
def bank13933 : Fin 1 → Cell := oneBank p13933 ray13933
theorem signs13933 : ∀ j, Signs p13933 (bank13933 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13934 := params 13
abbrev ray13934 := rays 13
def bank13934 : Fin 1 → Cell := oneBank p13934 ray13934
theorem signs13934 : ∀ j, Signs p13934 (bank13934 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13935 := params 14
abbrev ray13935 := rays 14
def bank13935 : Fin 1 → Cell := oneBank p13935 ray13935
theorem signs13935 : ∀ j, Signs p13935 (bank13935 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13936 := params 15
abbrev ray13936 := rays 15
def bank13936 : Fin 1 → Cell := oneBank p13936 ray13936
theorem signs13936 : ∀ j, Signs p13936 (bank13936 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13937 := params 16
abbrev ray13937 := rays 16
def bank13937 : Fin 1 → Cell := oneBank p13937 ray13937
theorem signs13937 : ∀ j, Signs p13937 (bank13937 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13938 := params 17
abbrev ray13938 := rays 17
def bank13938 : Fin 1 → Cell := oneBank p13938 ray13938
theorem signs13938 : ∀ j, Signs p13938 (bank13938 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13939 := params 18
abbrev ray13939 := rays 18
def bank13939 : Fin 1 → Cell := oneBank p13939 ray13939
theorem signs13939 : ∀ j, Signs p13939 (bank13939 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13940 := params 19
abbrev ray13940 := rays 19
def bank13940 : Fin 1 → Cell := oneBank p13940 ray13940
theorem signs13940 : ∀ j, Signs p13940 (bank13940 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13941 := params 20
abbrev ray13941 := rays 20
def bank13941 : Fin 1 → Cell := oneBank p13941 ray13941
theorem signs13941 : ∀ j, Signs p13941 (bank13941 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13942 := params 21
abbrev ray13942 := rays 21
def bank13942 : Fin 1 → Cell := oneBank p13942 ray13942
theorem signs13942 : ∀ j, Signs p13942 (bank13942 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13943 := params 22
abbrev ray13943 := rays 22
def bank13943 : Fin 1 → Cell := oneBank p13943 ray13943
theorem signs13943 : ∀ j, Signs p13943 (bank13943 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13944 := params 23
abbrev ray13944 := rays 23
def bank13944 : Fin 1 → Cell := oneBank p13944 ray13944
theorem signs13944 : ∀ j, Signs p13944 (bank13944 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13945 := params 24
abbrev ray13945 := rays 24
def bank13945 : Fin 1 → Cell := oneBank p13945 ray13945
theorem signs13945 : ∀ j, Signs p13945 (bank13945 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13946 := params 25
abbrev ray13946 := rays 25
def bank13946 : Fin 1 → Cell := oneBank p13946 ray13946
theorem signs13946 : ∀ j, Signs p13946 (bank13946 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13947 := params 26
abbrev ray13947 := rays 26
def bank13947 : Fin 1 → Cell := oneBank p13947 ray13947
theorem signs13947 : ∀ j, Signs p13947 (bank13947 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13948 := params 27
abbrev ray13948 := rays 27
def bank13948 : Fin 1 → Cell := oneBank p13948 ray13948
theorem signs13948 : ∀ j, Signs p13948 (bank13948 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13949 := params 28
abbrev ray13949 := rays 28
def bank13949 : Fin 1 → Cell := oneBank p13949 ray13949
theorem signs13949 : ∀ j, Signs p13949 (bank13949 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13950 := params 29
abbrev ray13950 := rays 29
def bank13950 : Fin 1 → Cell := oneBank p13950 ray13950
theorem signs13950 : ∀ j, Signs p13950 (bank13950 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13951 := params 30
abbrev ray13951 := rays 30
def bank13951 : Fin 1 → Cell := oneBank p13951 ray13951
theorem signs13951 : ∀ j, Signs p13951 (bank13951 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13952 := params 31
abbrev ray13952 := rays 31
def bank13952 : Fin 1 → Cell := oneBank p13952 ray13952
theorem signs13952 : ∀ j, Signs p13952 (bank13952 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13921_13952
