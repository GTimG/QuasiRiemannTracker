/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10913_10944
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97126996936828,97126611975339,97126226993991,97125841992785,97125456971721,97125071930800,97124686870022,97124301789388,97123916688898,97123531568553,97123146428353,97122761268298,97122376088389,97121990888627,97121605669012,97121220429545,97120835170226,97120449891056,97120064592035,97119679273163,97119293934441,97118908575870,97118523197450,97118137799182,97117752381066,97117366943102,97116981485291,97116596007634,97116210510131,97115824992782,97115439455588,97115053898550,97114668321668]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10912+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10913 := params 0
abbrev ray10913 := rays 0
def bank10913 : Fin 2 → Cell := twoBank p10913 ray10913
theorem signs10913 : ∀ j, Signs p10913 (bank10913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10914 := params 1
abbrev ray10914 := rays 1
def bank10914 : Fin 2 → Cell := twoBank p10914 ray10914
theorem signs10914 : ∀ j, Signs p10914 (bank10914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10915 := params 2
abbrev ray10915 := rays 2
def bank10915 : Fin 2 → Cell := twoBank p10915 ray10915
theorem signs10915 : ∀ j, Signs p10915 (bank10915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10916 := params 3
abbrev ray10916 := rays 3
def bank10916 : Fin 2 → Cell := twoBank p10916 ray10916
theorem signs10916 : ∀ j, Signs p10916 (bank10916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10917 := params 4
abbrev ray10917 := rays 4
def bank10917 : Fin 2 → Cell := twoBank p10917 ray10917
theorem signs10917 : ∀ j, Signs p10917 (bank10917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10918 := params 5
abbrev ray10918 := rays 5
def bank10918 : Fin 2 → Cell := twoBank p10918 ray10918
theorem signs10918 : ∀ j, Signs p10918 (bank10918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10919 := params 6
abbrev ray10919 := rays 6
def bank10919 : Fin 2 → Cell := twoBank p10919 ray10919
theorem signs10919 : ∀ j, Signs p10919 (bank10919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10920 := params 7
abbrev ray10920 := rays 7
def bank10920 : Fin 2 → Cell := twoBank p10920 ray10920
theorem signs10920 : ∀ j, Signs p10920 (bank10920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10921 := params 8
abbrev ray10921 := rays 8
def bank10921 : Fin 2 → Cell := twoBank p10921 ray10921
theorem signs10921 : ∀ j, Signs p10921 (bank10921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10922 := params 9
abbrev ray10922 := rays 9
def bank10922 : Fin 2 → Cell := twoBank p10922 ray10922
theorem signs10922 : ∀ j, Signs p10922 (bank10922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10923 := params 10
abbrev ray10923 := rays 10
def bank10923 : Fin 2 → Cell := twoBank p10923 ray10923
theorem signs10923 : ∀ j, Signs p10923 (bank10923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10924 := params 11
abbrev ray10924 := rays 11
def bank10924 : Fin 2 → Cell := twoBank p10924 ray10924
theorem signs10924 : ∀ j, Signs p10924 (bank10924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10925 := params 12
abbrev ray10925 := rays 12
def bank10925 : Fin 2 → Cell := twoBank p10925 ray10925
theorem signs10925 : ∀ j, Signs p10925 (bank10925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10926 := params 13
abbrev ray10926 := rays 13
def bank10926 : Fin 2 → Cell := twoBank p10926 ray10926
theorem signs10926 : ∀ j, Signs p10926 (bank10926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10927 := params 14
abbrev ray10927 := rays 14
def bank10927 : Fin 2 → Cell := twoBank p10927 ray10927
theorem signs10927 : ∀ j, Signs p10927 (bank10927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10928 := params 15
abbrev ray10928 := rays 15
def bank10928 : Fin 2 → Cell := twoBank p10928 ray10928
theorem signs10928 : ∀ j, Signs p10928 (bank10928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10929 := params 16
abbrev ray10929 := rays 16
def bank10929 : Fin 2 → Cell := twoBank p10929 ray10929
theorem signs10929 : ∀ j, Signs p10929 (bank10929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10930 := params 17
abbrev ray10930 := rays 17
def bank10930 : Fin 2 → Cell := twoBank p10930 ray10930
theorem signs10930 : ∀ j, Signs p10930 (bank10930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10931 := params 18
abbrev ray10931 := rays 18
def bank10931 : Fin 2 → Cell := twoBank p10931 ray10931
theorem signs10931 : ∀ j, Signs p10931 (bank10931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10932 := params 19
abbrev ray10932 := rays 19
def bank10932 : Fin 2 → Cell := twoBank p10932 ray10932
theorem signs10932 : ∀ j, Signs p10932 (bank10932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10933 := params 20
abbrev ray10933 := rays 20
def bank10933 : Fin 2 → Cell := twoBank p10933 ray10933
theorem signs10933 : ∀ j, Signs p10933 (bank10933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10934 := params 21
abbrev ray10934 := rays 21
def bank10934 : Fin 2 → Cell := twoBank p10934 ray10934
theorem signs10934 : ∀ j, Signs p10934 (bank10934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10935 := params 22
abbrev ray10935 := rays 22
def bank10935 : Fin 2 → Cell := twoBank p10935 ray10935
theorem signs10935 : ∀ j, Signs p10935 (bank10935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10936 := params 23
abbrev ray10936 := rays 23
def bank10936 : Fin 2 → Cell := twoBank p10936 ray10936
theorem signs10936 : ∀ j, Signs p10936 (bank10936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10937 := params 24
abbrev ray10937 := rays 24
def bank10937 : Fin 2 → Cell := twoBank p10937 ray10937
theorem signs10937 : ∀ j, Signs p10937 (bank10937 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10938 := params 25
abbrev ray10938 := rays 25
def bank10938 : Fin 2 → Cell := twoBank p10938 ray10938
theorem signs10938 : ∀ j, Signs p10938 (bank10938 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10939 := params 26
abbrev ray10939 := rays 26
def bank10939 : Fin 2 → Cell := twoBank p10939 ray10939
theorem signs10939 : ∀ j, Signs p10939 (bank10939 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10940 := params 27
abbrev ray10940 := rays 27
def bank10940 : Fin 2 → Cell := twoBank p10940 ray10940
theorem signs10940 : ∀ j, Signs p10940 (bank10940 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10941 := params 28
abbrev ray10941 := rays 28
def bank10941 : Fin 2 → Cell := twoBank p10941 ray10941
theorem signs10941 : ∀ j, Signs p10941 (bank10941 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10942 := params 29
abbrev ray10942 := rays 29
def bank10942 : Fin 2 → Cell := twoBank p10942 ray10942
theorem signs10942 : ∀ j, Signs p10942 (bank10942 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10943 := params 30
abbrev ray10943 := rays 30
def bank10943 : Fin 2 → Cell := twoBank p10943 ray10943
theorem signs10943 : ∀ j, Signs p10943 (bank10943 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10944 := params 31
abbrev ray10944 := rays 31
def bank10944 : Fin 2 → Cell := twoBank p10944 ray10944
theorem signs10944 : ∀ j, Signs p10944 (bank10944 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10913_10944
