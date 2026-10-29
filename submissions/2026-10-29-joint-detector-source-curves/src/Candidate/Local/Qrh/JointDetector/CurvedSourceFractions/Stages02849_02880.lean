/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02849_02880
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99529486821610,99529284762398,99529082676632,99528880564312,99528678425440,99528476260017,99528274068045,99528071849525,99527869604458,99527667332845,99527465034688,99527262709988,99527060358746,99526857980964,99526655576643,99526453145784,99526250688388,99526048204457,99525845693992,99525643156994,99525440593465,99525238003406,99525035386818,99524832743703,99524630074062,99524427377896,99524224655206,99524021905994,99523819130261,99523616328008,99523413499237,99523210643949,99523007762145]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2848+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2849 := params 0
abbrev ray2849 := rays 0
def bank2849 : Fin 2 → Cell := twoBank p2849 ray2849
theorem signs2849 : ∀ j, Signs p2849 (bank2849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2850 := params 1
abbrev ray2850 := rays 1
def bank2850 : Fin 2 → Cell := twoBank p2850 ray2850
theorem signs2850 : ∀ j, Signs p2850 (bank2850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2851 := params 2
abbrev ray2851 := rays 2
def bank2851 : Fin 2 → Cell := twoBank p2851 ray2851
theorem signs2851 : ∀ j, Signs p2851 (bank2851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2852 := params 3
abbrev ray2852 := rays 3
def bank2852 : Fin 2 → Cell := twoBank p2852 ray2852
theorem signs2852 : ∀ j, Signs p2852 (bank2852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2853 := params 4
abbrev ray2853 := rays 4
def bank2853 : Fin 2 → Cell := twoBank p2853 ray2853
theorem signs2853 : ∀ j, Signs p2853 (bank2853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2854 := params 5
abbrev ray2854 := rays 5
def bank2854 : Fin 2 → Cell := twoBank p2854 ray2854
theorem signs2854 : ∀ j, Signs p2854 (bank2854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2855 := params 6
abbrev ray2855 := rays 6
def bank2855 : Fin 2 → Cell := twoBank p2855 ray2855
theorem signs2855 : ∀ j, Signs p2855 (bank2855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2856 := params 7
abbrev ray2856 := rays 7
def bank2856 : Fin 2 → Cell := twoBank p2856 ray2856
theorem signs2856 : ∀ j, Signs p2856 (bank2856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2857 := params 8
abbrev ray2857 := rays 8
def bank2857 : Fin 2 → Cell := twoBank p2857 ray2857
theorem signs2857 : ∀ j, Signs p2857 (bank2857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2858 := params 9
abbrev ray2858 := rays 9
def bank2858 : Fin 2 → Cell := twoBank p2858 ray2858
theorem signs2858 : ∀ j, Signs p2858 (bank2858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2859 := params 10
abbrev ray2859 := rays 10
def bank2859 : Fin 2 → Cell := twoBank p2859 ray2859
theorem signs2859 : ∀ j, Signs p2859 (bank2859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2860 := params 11
abbrev ray2860 := rays 11
def bank2860 : Fin 2 → Cell := twoBank p2860 ray2860
theorem signs2860 : ∀ j, Signs p2860 (bank2860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2861 := params 12
abbrev ray2861 := rays 12
def bank2861 : Fin 2 → Cell := twoBank p2861 ray2861
theorem signs2861 : ∀ j, Signs p2861 (bank2861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2862 := params 13
abbrev ray2862 := rays 13
def bank2862 : Fin 2 → Cell := twoBank p2862 ray2862
theorem signs2862 : ∀ j, Signs p2862 (bank2862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2863 := params 14
abbrev ray2863 := rays 14
def bank2863 : Fin 2 → Cell := twoBank p2863 ray2863
theorem signs2863 : ∀ j, Signs p2863 (bank2863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2864 := params 15
abbrev ray2864 := rays 15
def bank2864 : Fin 2 → Cell := twoBank p2864 ray2864
theorem signs2864 : ∀ j, Signs p2864 (bank2864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2865 := params 16
abbrev ray2865 := rays 16
def bank2865 : Fin 2 → Cell := twoBank p2865 ray2865
theorem signs2865 : ∀ j, Signs p2865 (bank2865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2866 := params 17
abbrev ray2866 := rays 17
def bank2866 : Fin 2 → Cell := twoBank p2866 ray2866
theorem signs2866 : ∀ j, Signs p2866 (bank2866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2867 := params 18
abbrev ray2867 := rays 18
def bank2867 : Fin 2 → Cell := twoBank p2867 ray2867
theorem signs2867 : ∀ j, Signs p2867 (bank2867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2868 := params 19
abbrev ray2868 := rays 19
def bank2868 : Fin 2 → Cell := twoBank p2868 ray2868
theorem signs2868 : ∀ j, Signs p2868 (bank2868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2869 := params 20
abbrev ray2869 := rays 20
def bank2869 : Fin 2 → Cell := twoBank p2869 ray2869
theorem signs2869 : ∀ j, Signs p2869 (bank2869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2870 := params 21
abbrev ray2870 := rays 21
def bank2870 : Fin 2 → Cell := twoBank p2870 ray2870
theorem signs2870 : ∀ j, Signs p2870 (bank2870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2871 := params 22
abbrev ray2871 := rays 22
def bank2871 : Fin 2 → Cell := twoBank p2871 ray2871
theorem signs2871 : ∀ j, Signs p2871 (bank2871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2872 := params 23
abbrev ray2872 := rays 23
def bank2872 : Fin 2 → Cell := twoBank p2872 ray2872
theorem signs2872 : ∀ j, Signs p2872 (bank2872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2873 := params 24
abbrev ray2873 := rays 24
def bank2873 : Fin 2 → Cell := twoBank p2873 ray2873
theorem signs2873 : ∀ j, Signs p2873 (bank2873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2874 := params 25
abbrev ray2874 := rays 25
def bank2874 : Fin 2 → Cell := twoBank p2874 ray2874
theorem signs2874 : ∀ j, Signs p2874 (bank2874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2875 := params 26
abbrev ray2875 := rays 26
def bank2875 : Fin 2 → Cell := twoBank p2875 ray2875
theorem signs2875 : ∀ j, Signs p2875 (bank2875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2876 := params 27
abbrev ray2876 := rays 27
def bank2876 : Fin 2 → Cell := twoBank p2876 ray2876
theorem signs2876 : ∀ j, Signs p2876 (bank2876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2877 := params 28
abbrev ray2877 := rays 28
def bank2877 : Fin 2 → Cell := twoBank p2877 ray2877
theorem signs2877 : ∀ j, Signs p2877 (bank2877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2878 := params 29
abbrev ray2878 := rays 29
def bank2878 : Fin 2 → Cell := twoBank p2878 ray2878
theorem signs2878 : ∀ j, Signs p2878 (bank2878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2879 := params 30
abbrev ray2879 := rays 30
def bank2879 : Fin 2 → Cell := twoBank p2879 ray2879
theorem signs2879 : ∀ j, Signs p2879 (bank2879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2880 := params 31
abbrev ray2880 := rays 31
def bank2880 : Fin 2 → Cell := twoBank p2880 ray2880
theorem signs2880 : ∀ j, Signs p2880 (bank2880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02849_02880
