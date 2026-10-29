/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12897_12928
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96324788580395,96324365390367,96323942183875,96323518960919,96323095721499,96322672465615,96322249193268,96321825904458,96321402599185,96320979277450,96320555939252,96320132584592,96319709213471,96319285825888,96318862421844,96318439001339,96318015564374,96317592110948,96317168641062,96316745154716,96316321651911,96315898132647,96315474596924,96315051044742,96314627476101,96314203891002,96313780289445,96313356671431,96312933036959,96312509386030,96312085718644,96311662034802,96311238334503]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12896+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12897 := params 0
abbrev ray12897 := rays 0
def bank12897 : Fin 1 → Cell := oneBank p12897 ray12897
theorem signs12897 : ∀ j, Signs p12897 (bank12897 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12898 := params 1
abbrev ray12898 := rays 1
def bank12898 : Fin 1 → Cell := oneBank p12898 ray12898
theorem signs12898 : ∀ j, Signs p12898 (bank12898 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12899 := params 2
abbrev ray12899 := rays 2
def bank12899 : Fin 1 → Cell := oneBank p12899 ray12899
theorem signs12899 : ∀ j, Signs p12899 (bank12899 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12900 := params 3
abbrev ray12900 := rays 3
def bank12900 : Fin 1 → Cell := oneBank p12900 ray12900
theorem signs12900 : ∀ j, Signs p12900 (bank12900 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12901 := params 4
abbrev ray12901 := rays 4
def bank12901 : Fin 1 → Cell := oneBank p12901 ray12901
theorem signs12901 : ∀ j, Signs p12901 (bank12901 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12902 := params 5
abbrev ray12902 := rays 5
def bank12902 : Fin 1 → Cell := oneBank p12902 ray12902
theorem signs12902 : ∀ j, Signs p12902 (bank12902 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12903 := params 6
abbrev ray12903 := rays 6
def bank12903 : Fin 1 → Cell := oneBank p12903 ray12903
theorem signs12903 : ∀ j, Signs p12903 (bank12903 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12904 := params 7
abbrev ray12904 := rays 7
def bank12904 : Fin 1 → Cell := oneBank p12904 ray12904
theorem signs12904 : ∀ j, Signs p12904 (bank12904 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12905 := params 8
abbrev ray12905 := rays 8
def bank12905 : Fin 1 → Cell := oneBank p12905 ray12905
theorem signs12905 : ∀ j, Signs p12905 (bank12905 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12906 := params 9
abbrev ray12906 := rays 9
def bank12906 : Fin 1 → Cell := oneBank p12906 ray12906
theorem signs12906 : ∀ j, Signs p12906 (bank12906 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12907 := params 10
abbrev ray12907 := rays 10
def bank12907 : Fin 1 → Cell := oneBank p12907 ray12907
theorem signs12907 : ∀ j, Signs p12907 (bank12907 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12908 := params 11
abbrev ray12908 := rays 11
def bank12908 : Fin 1 → Cell := oneBank p12908 ray12908
theorem signs12908 : ∀ j, Signs p12908 (bank12908 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12909 := params 12
abbrev ray12909 := rays 12
def bank12909 : Fin 1 → Cell := oneBank p12909 ray12909
theorem signs12909 : ∀ j, Signs p12909 (bank12909 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12910 := params 13
abbrev ray12910 := rays 13
def bank12910 : Fin 1 → Cell := oneBank p12910 ray12910
theorem signs12910 : ∀ j, Signs p12910 (bank12910 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12911 := params 14
abbrev ray12911 := rays 14
def bank12911 : Fin 1 → Cell := oneBank p12911 ray12911
theorem signs12911 : ∀ j, Signs p12911 (bank12911 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12912 := params 15
abbrev ray12912 := rays 15
def bank12912 : Fin 1 → Cell := oneBank p12912 ray12912
theorem signs12912 : ∀ j, Signs p12912 (bank12912 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12913 := params 16
abbrev ray12913 := rays 16
def bank12913 : Fin 1 → Cell := oneBank p12913 ray12913
theorem signs12913 : ∀ j, Signs p12913 (bank12913 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12914 := params 17
abbrev ray12914 := rays 17
def bank12914 : Fin 1 → Cell := oneBank p12914 ray12914
theorem signs12914 : ∀ j, Signs p12914 (bank12914 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12915 := params 18
abbrev ray12915 := rays 18
def bank12915 : Fin 1 → Cell := oneBank p12915 ray12915
theorem signs12915 : ∀ j, Signs p12915 (bank12915 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12916 := params 19
abbrev ray12916 := rays 19
def bank12916 : Fin 1 → Cell := oneBank p12916 ray12916
theorem signs12916 : ∀ j, Signs p12916 (bank12916 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12917 := params 20
abbrev ray12917 := rays 20
def bank12917 : Fin 1 → Cell := oneBank p12917 ray12917
theorem signs12917 : ∀ j, Signs p12917 (bank12917 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12918 := params 21
abbrev ray12918 := rays 21
def bank12918 : Fin 1 → Cell := oneBank p12918 ray12918
theorem signs12918 : ∀ j, Signs p12918 (bank12918 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12919 := params 22
abbrev ray12919 := rays 22
def bank12919 : Fin 1 → Cell := oneBank p12919 ray12919
theorem signs12919 : ∀ j, Signs p12919 (bank12919 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12920 := params 23
abbrev ray12920 := rays 23
def bank12920 : Fin 1 → Cell := oneBank p12920 ray12920
theorem signs12920 : ∀ j, Signs p12920 (bank12920 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12921 := params 24
abbrev ray12921 := rays 24
def bank12921 : Fin 1 → Cell := oneBank p12921 ray12921
theorem signs12921 : ∀ j, Signs p12921 (bank12921 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12922 := params 25
abbrev ray12922 := rays 25
def bank12922 : Fin 1 → Cell := oneBank p12922 ray12922
theorem signs12922 : ∀ j, Signs p12922 (bank12922 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12923 := params 26
abbrev ray12923 := rays 26
def bank12923 : Fin 1 → Cell := oneBank p12923 ray12923
theorem signs12923 : ∀ j, Signs p12923 (bank12923 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12924 := params 27
abbrev ray12924 := rays 27
def bank12924 : Fin 1 → Cell := oneBank p12924 ray12924
theorem signs12924 : ∀ j, Signs p12924 (bank12924 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12925 := params 28
abbrev ray12925 := rays 28
def bank12925 : Fin 1 → Cell := oneBank p12925 ray12925
theorem signs12925 : ∀ j, Signs p12925 (bank12925 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12926 := params 29
abbrev ray12926 := rays 29
def bank12926 : Fin 1 → Cell := oneBank p12926 ray12926
theorem signs12926 : ∀ j, Signs p12926 (bank12926 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12927 := params 30
abbrev ray12927 := rays 30
def bank12927 : Fin 1 → Cell := oneBank p12927 ray12927
theorem signs12927 : ∀ j, Signs p12927 (bank12927 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12928 := params 31
abbrev ray12928 := rays 31
def bank12928 : Fin 1 → Cell := oneBank p12928 ray12928
theorem signs12928 : ∀ j, Signs p12928 (bank12928 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12897_12928
