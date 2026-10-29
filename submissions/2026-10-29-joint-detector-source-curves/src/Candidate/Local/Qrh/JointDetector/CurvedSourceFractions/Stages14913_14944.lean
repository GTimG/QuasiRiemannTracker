/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14913_14944
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95438511058868,95438055119571,95437599164198,95437143192750,95436687205226,95436231201627,95435775181952,95435319146202,95434863094377,95434407026477,95433950942502,95433494842452,95433038726328,95432582594129,95432126445856,95431670281508,95431214101086,95430757904590,95430301692020,95429845463376,95429389218659,95428932957868,95428476681003,95428020388065,95427564079054,95427107753970,95426651412813,95426195055583,95425738682280,95425282292904,95424825887456,95424369465935,95423913028342]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14912+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14913 := params 0
abbrev ray14913 := rays 0
def bank14913 : Fin 1 → Cell := oneBank p14913 ray14913
theorem signs14913 : ∀ j, Signs p14913 (bank14913 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14914 := params 1
abbrev ray14914 := rays 1
def bank14914 : Fin 1 → Cell := oneBank p14914 ray14914
theorem signs14914 : ∀ j, Signs p14914 (bank14914 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14915 := params 2
abbrev ray14915 := rays 2
def bank14915 : Fin 1 → Cell := oneBank p14915 ray14915
theorem signs14915 : ∀ j, Signs p14915 (bank14915 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14916 := params 3
abbrev ray14916 := rays 3
def bank14916 : Fin 1 → Cell := oneBank p14916 ray14916
theorem signs14916 : ∀ j, Signs p14916 (bank14916 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14917 := params 4
abbrev ray14917 := rays 4
def bank14917 : Fin 1 → Cell := oneBank p14917 ray14917
theorem signs14917 : ∀ j, Signs p14917 (bank14917 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14918 := params 5
abbrev ray14918 := rays 5
def bank14918 : Fin 1 → Cell := oneBank p14918 ray14918
theorem signs14918 : ∀ j, Signs p14918 (bank14918 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14919 := params 6
abbrev ray14919 := rays 6
def bank14919 : Fin 1 → Cell := oneBank p14919 ray14919
theorem signs14919 : ∀ j, Signs p14919 (bank14919 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14920 := params 7
abbrev ray14920 := rays 7
def bank14920 : Fin 1 → Cell := oneBank p14920 ray14920
theorem signs14920 : ∀ j, Signs p14920 (bank14920 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14921 := params 8
abbrev ray14921 := rays 8
def bank14921 : Fin 1 → Cell := oneBank p14921 ray14921
theorem signs14921 : ∀ j, Signs p14921 (bank14921 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14922 := params 9
abbrev ray14922 := rays 9
def bank14922 : Fin 1 → Cell := oneBank p14922 ray14922
theorem signs14922 : ∀ j, Signs p14922 (bank14922 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14923 := params 10
abbrev ray14923 := rays 10
def bank14923 : Fin 1 → Cell := oneBank p14923 ray14923
theorem signs14923 : ∀ j, Signs p14923 (bank14923 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14924 := params 11
abbrev ray14924 := rays 11
def bank14924 : Fin 1 → Cell := oneBank p14924 ray14924
theorem signs14924 : ∀ j, Signs p14924 (bank14924 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14925 := params 12
abbrev ray14925 := rays 12
def bank14925 : Fin 1 → Cell := oneBank p14925 ray14925
theorem signs14925 : ∀ j, Signs p14925 (bank14925 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14926 := params 13
abbrev ray14926 := rays 13
def bank14926 : Fin 1 → Cell := oneBank p14926 ray14926
theorem signs14926 : ∀ j, Signs p14926 (bank14926 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14927 := params 14
abbrev ray14927 := rays 14
def bank14927 : Fin 1 → Cell := oneBank p14927 ray14927
theorem signs14927 : ∀ j, Signs p14927 (bank14927 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14928 := params 15
abbrev ray14928 := rays 15
def bank14928 : Fin 1 → Cell := oneBank p14928 ray14928
theorem signs14928 : ∀ j, Signs p14928 (bank14928 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14929 := params 16
abbrev ray14929 := rays 16
def bank14929 : Fin 1 → Cell := oneBank p14929 ray14929
theorem signs14929 : ∀ j, Signs p14929 (bank14929 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14930 := params 17
abbrev ray14930 := rays 17
def bank14930 : Fin 1 → Cell := oneBank p14930 ray14930
theorem signs14930 : ∀ j, Signs p14930 (bank14930 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14931 := params 18
abbrev ray14931 := rays 18
def bank14931 : Fin 1 → Cell := oneBank p14931 ray14931
theorem signs14931 : ∀ j, Signs p14931 (bank14931 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14932 := params 19
abbrev ray14932 := rays 19
def bank14932 : Fin 1 → Cell := oneBank p14932 ray14932
theorem signs14932 : ∀ j, Signs p14932 (bank14932 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14933 := params 20
abbrev ray14933 := rays 20
def bank14933 : Fin 1 → Cell := oneBank p14933 ray14933
theorem signs14933 : ∀ j, Signs p14933 (bank14933 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14934 := params 21
abbrev ray14934 := rays 21
def bank14934 : Fin 1 → Cell := oneBank p14934 ray14934
theorem signs14934 : ∀ j, Signs p14934 (bank14934 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14935 := params 22
abbrev ray14935 := rays 22
def bank14935 : Fin 1 → Cell := oneBank p14935 ray14935
theorem signs14935 : ∀ j, Signs p14935 (bank14935 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14936 := params 23
abbrev ray14936 := rays 23
def bank14936 : Fin 1 → Cell := oneBank p14936 ray14936
theorem signs14936 : ∀ j, Signs p14936 (bank14936 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14937 := params 24
abbrev ray14937 := rays 24
def bank14937 : Fin 1 → Cell := oneBank p14937 ray14937
theorem signs14937 : ∀ j, Signs p14937 (bank14937 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14938 := params 25
abbrev ray14938 := rays 25
def bank14938 : Fin 1 → Cell := oneBank p14938 ray14938
theorem signs14938 : ∀ j, Signs p14938 (bank14938 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14939 := params 26
abbrev ray14939 := rays 26
def bank14939 : Fin 1 → Cell := oneBank p14939 ray14939
theorem signs14939 : ∀ j, Signs p14939 (bank14939 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14940 := params 27
abbrev ray14940 := rays 27
def bank14940 : Fin 1 → Cell := oneBank p14940 ray14940
theorem signs14940 : ∀ j, Signs p14940 (bank14940 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14941 := params 28
abbrev ray14941 := rays 28
def bank14941 : Fin 1 → Cell := oneBank p14941 ray14941
theorem signs14941 : ∀ j, Signs p14941 (bank14941 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14942 := params 29
abbrev ray14942 := rays 29
def bank14942 : Fin 1 → Cell := oneBank p14942 ray14942
theorem signs14942 : ∀ j, Signs p14942 (bank14942 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14943 := params 30
abbrev ray14943 := rays 30
def bank14943 : Fin 1 → Cell := oneBank p14943 ray14943
theorem signs14943 : ∀ j, Signs p14943 (bank14943 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14944 := params 31
abbrev ray14944 := rays 31
def bank14944 : Fin 1 → Cell := oneBank p14944 ray14944
theorem signs14944 : ∀ j, Signs p14944 (bank14944 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14913_14944
