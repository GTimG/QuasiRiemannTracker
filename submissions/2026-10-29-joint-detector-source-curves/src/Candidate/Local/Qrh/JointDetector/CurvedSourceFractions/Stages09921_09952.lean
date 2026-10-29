/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09921_09952
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97499014342947,97498649335589,97498284307850,97497919259730,97497554191230,97497189102351,97496823993093,97496458863456,97496093713441,97495728543049,97495363352280,97494998141135,97494632909614,97494267657718,97493902385448,97493537092804,97493171779786,97492806446396,97492441092633,97492075718499,97491710323993,97491344909117,97490979473871,97490614018255,97490248542270,97489883045917,97489517529196,97489151992108,97488786434653,97488420856832,97488055258645,97487689640093,97487324001177]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9920+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9921 := params 0
abbrev ray9921 := rays 0
def bank9921 : Fin 2 → Cell := twoBank p9921 ray9921
theorem signs9921 : ∀ j, Signs p9921 (bank9921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9922 := params 1
abbrev ray9922 := rays 1
def bank9922 : Fin 2 → Cell := twoBank p9922 ray9922
theorem signs9922 : ∀ j, Signs p9922 (bank9922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9923 := params 2
abbrev ray9923 := rays 2
def bank9923 : Fin 2 → Cell := twoBank p9923 ray9923
theorem signs9923 : ∀ j, Signs p9923 (bank9923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9924 := params 3
abbrev ray9924 := rays 3
def bank9924 : Fin 2 → Cell := twoBank p9924 ray9924
theorem signs9924 : ∀ j, Signs p9924 (bank9924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9925 := params 4
abbrev ray9925 := rays 4
def bank9925 : Fin 2 → Cell := twoBank p9925 ray9925
theorem signs9925 : ∀ j, Signs p9925 (bank9925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9926 := params 5
abbrev ray9926 := rays 5
def bank9926 : Fin 2 → Cell := twoBank p9926 ray9926
theorem signs9926 : ∀ j, Signs p9926 (bank9926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9927 := params 6
abbrev ray9927 := rays 6
def bank9927 : Fin 2 → Cell := twoBank p9927 ray9927
theorem signs9927 : ∀ j, Signs p9927 (bank9927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9928 := params 7
abbrev ray9928 := rays 7
def bank9928 : Fin 2 → Cell := twoBank p9928 ray9928
theorem signs9928 : ∀ j, Signs p9928 (bank9928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9929 := params 8
abbrev ray9929 := rays 8
def bank9929 : Fin 2 → Cell := twoBank p9929 ray9929
theorem signs9929 : ∀ j, Signs p9929 (bank9929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9930 := params 9
abbrev ray9930 := rays 9
def bank9930 : Fin 2 → Cell := twoBank p9930 ray9930
theorem signs9930 : ∀ j, Signs p9930 (bank9930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9931 := params 10
abbrev ray9931 := rays 10
def bank9931 : Fin 2 → Cell := twoBank p9931 ray9931
theorem signs9931 : ∀ j, Signs p9931 (bank9931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9932 := params 11
abbrev ray9932 := rays 11
def bank9932 : Fin 2 → Cell := twoBank p9932 ray9932
theorem signs9932 : ∀ j, Signs p9932 (bank9932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9933 := params 12
abbrev ray9933 := rays 12
def bank9933 : Fin 2 → Cell := twoBank p9933 ray9933
theorem signs9933 : ∀ j, Signs p9933 (bank9933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9934 := params 13
abbrev ray9934 := rays 13
def bank9934 : Fin 2 → Cell := twoBank p9934 ray9934
theorem signs9934 : ∀ j, Signs p9934 (bank9934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9935 := params 14
abbrev ray9935 := rays 14
def bank9935 : Fin 2 → Cell := twoBank p9935 ray9935
theorem signs9935 : ∀ j, Signs p9935 (bank9935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9936 := params 15
abbrev ray9936 := rays 15
def bank9936 : Fin 2 → Cell := twoBank p9936 ray9936
theorem signs9936 : ∀ j, Signs p9936 (bank9936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9937 := params 16
abbrev ray9937 := rays 16
def bank9937 : Fin 2 → Cell := twoBank p9937 ray9937
theorem signs9937 : ∀ j, Signs p9937 (bank9937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9938 := params 17
abbrev ray9938 := rays 17
def bank9938 : Fin 2 → Cell := twoBank p9938 ray9938
theorem signs9938 : ∀ j, Signs p9938 (bank9938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9939 := params 18
abbrev ray9939 := rays 18
def bank9939 : Fin 2 → Cell := twoBank p9939 ray9939
theorem signs9939 : ∀ j, Signs p9939 (bank9939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9940 := params 19
abbrev ray9940 := rays 19
def bank9940 : Fin 2 → Cell := twoBank p9940 ray9940
theorem signs9940 : ∀ j, Signs p9940 (bank9940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9941 := params 20
abbrev ray9941 := rays 20
def bank9941 : Fin 2 → Cell := twoBank p9941 ray9941
theorem signs9941 : ∀ j, Signs p9941 (bank9941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9942 := params 21
abbrev ray9942 := rays 21
def bank9942 : Fin 2 → Cell := twoBank p9942 ray9942
theorem signs9942 : ∀ j, Signs p9942 (bank9942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9943 := params 22
abbrev ray9943 := rays 22
def bank9943 : Fin 2 → Cell := twoBank p9943 ray9943
theorem signs9943 : ∀ j, Signs p9943 (bank9943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9944 := params 23
abbrev ray9944 := rays 23
def bank9944 : Fin 2 → Cell := twoBank p9944 ray9944
theorem signs9944 : ∀ j, Signs p9944 (bank9944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9945 := params 24
abbrev ray9945 := rays 24
def bank9945 : Fin 2 → Cell := twoBank p9945 ray9945
theorem signs9945 : ∀ j, Signs p9945 (bank9945 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9946 := params 25
abbrev ray9946 := rays 25
def bank9946 : Fin 2 → Cell := twoBank p9946 ray9946
theorem signs9946 : ∀ j, Signs p9946 (bank9946 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9947 := params 26
abbrev ray9947 := rays 26
def bank9947 : Fin 2 → Cell := twoBank p9947 ray9947
theorem signs9947 : ∀ j, Signs p9947 (bank9947 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9948 := params 27
abbrev ray9948 := rays 27
def bank9948 : Fin 2 → Cell := twoBank p9948 ray9948
theorem signs9948 : ∀ j, Signs p9948 (bank9948 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9949 := params 28
abbrev ray9949 := rays 28
def bank9949 : Fin 2 → Cell := twoBank p9949 ray9949
theorem signs9949 : ∀ j, Signs p9949 (bank9949 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9950 := params 29
abbrev ray9950 := rays 29
def bank9950 : Fin 2 → Cell := twoBank p9950 ray9950
theorem signs9950 : ∀ j, Signs p9950 (bank9950 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9951 := params 30
abbrev ray9951 := rays 30
def bank9951 : Fin 2 → Cell := twoBank p9951 ray9951
theorem signs9951 : ∀ j, Signs p9951 (bank9951 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9952 := params 31
abbrev ray9952 := rays 31
def bank9952 : Fin 2 → Cell := twoBank p9952 ray9952
theorem signs9952 : ∀ j, Signs p9952 (bank9952 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09921_09952
