/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10881_10912
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97139305216040,97138920890295,97138536544676,97138152179182,97137767793815,97137383388575,97136998963462,97136614518477,97136230053620,97135845568892,97135461064293,97135076539824,97134691995485,97134307431277,97133922847200,97133538243255,97133153619442,97132768975762,97132384312215,97131999628802,97131614925523,97131230202379,97130845459370,97130460696497,97130075913760,97129691111160,97129306288697,97128921446372,97128536584185,97128151702136,97127766800227,97127381878457,97126996936828]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10880+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10881 := params 0
abbrev ray10881 := rays 0
def bank10881 : Fin 2 → Cell := twoBank p10881 ray10881
theorem signs10881 : ∀ j, Signs p10881 (bank10881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10882 := params 1
abbrev ray10882 := rays 1
def bank10882 : Fin 2 → Cell := twoBank p10882 ray10882
theorem signs10882 : ∀ j, Signs p10882 (bank10882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10883 := params 2
abbrev ray10883 := rays 2
def bank10883 : Fin 2 → Cell := twoBank p10883 ray10883
theorem signs10883 : ∀ j, Signs p10883 (bank10883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10884 := params 3
abbrev ray10884 := rays 3
def bank10884 : Fin 2 → Cell := twoBank p10884 ray10884
theorem signs10884 : ∀ j, Signs p10884 (bank10884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10885 := params 4
abbrev ray10885 := rays 4
def bank10885 : Fin 2 → Cell := twoBank p10885 ray10885
theorem signs10885 : ∀ j, Signs p10885 (bank10885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10886 := params 5
abbrev ray10886 := rays 5
def bank10886 : Fin 2 → Cell := twoBank p10886 ray10886
theorem signs10886 : ∀ j, Signs p10886 (bank10886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10887 := params 6
abbrev ray10887 := rays 6
def bank10887 : Fin 2 → Cell := twoBank p10887 ray10887
theorem signs10887 : ∀ j, Signs p10887 (bank10887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10888 := params 7
abbrev ray10888 := rays 7
def bank10888 : Fin 2 → Cell := twoBank p10888 ray10888
theorem signs10888 : ∀ j, Signs p10888 (bank10888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10889 := params 8
abbrev ray10889 := rays 8
def bank10889 : Fin 2 → Cell := twoBank p10889 ray10889
theorem signs10889 : ∀ j, Signs p10889 (bank10889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10890 := params 9
abbrev ray10890 := rays 9
def bank10890 : Fin 2 → Cell := twoBank p10890 ray10890
theorem signs10890 : ∀ j, Signs p10890 (bank10890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10891 := params 10
abbrev ray10891 := rays 10
def bank10891 : Fin 2 → Cell := twoBank p10891 ray10891
theorem signs10891 : ∀ j, Signs p10891 (bank10891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10892 := params 11
abbrev ray10892 := rays 11
def bank10892 : Fin 2 → Cell := twoBank p10892 ray10892
theorem signs10892 : ∀ j, Signs p10892 (bank10892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10893 := params 12
abbrev ray10893 := rays 12
def bank10893 : Fin 2 → Cell := twoBank p10893 ray10893
theorem signs10893 : ∀ j, Signs p10893 (bank10893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10894 := params 13
abbrev ray10894 := rays 13
def bank10894 : Fin 2 → Cell := twoBank p10894 ray10894
theorem signs10894 : ∀ j, Signs p10894 (bank10894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10895 := params 14
abbrev ray10895 := rays 14
def bank10895 : Fin 2 → Cell := twoBank p10895 ray10895
theorem signs10895 : ∀ j, Signs p10895 (bank10895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10896 := params 15
abbrev ray10896 := rays 15
def bank10896 : Fin 2 → Cell := twoBank p10896 ray10896
theorem signs10896 : ∀ j, Signs p10896 (bank10896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10897 := params 16
abbrev ray10897 := rays 16
def bank10897 : Fin 2 → Cell := twoBank p10897 ray10897
theorem signs10897 : ∀ j, Signs p10897 (bank10897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10898 := params 17
abbrev ray10898 := rays 17
def bank10898 : Fin 2 → Cell := twoBank p10898 ray10898
theorem signs10898 : ∀ j, Signs p10898 (bank10898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10899 := params 18
abbrev ray10899 := rays 18
def bank10899 : Fin 2 → Cell := twoBank p10899 ray10899
theorem signs10899 : ∀ j, Signs p10899 (bank10899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10900 := params 19
abbrev ray10900 := rays 19
def bank10900 : Fin 2 → Cell := twoBank p10900 ray10900
theorem signs10900 : ∀ j, Signs p10900 (bank10900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10901 := params 20
abbrev ray10901 := rays 20
def bank10901 : Fin 2 → Cell := twoBank p10901 ray10901
theorem signs10901 : ∀ j, Signs p10901 (bank10901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10902 := params 21
abbrev ray10902 := rays 21
def bank10902 : Fin 2 → Cell := twoBank p10902 ray10902
theorem signs10902 : ∀ j, Signs p10902 (bank10902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10903 := params 22
abbrev ray10903 := rays 22
def bank10903 : Fin 2 → Cell := twoBank p10903 ray10903
theorem signs10903 : ∀ j, Signs p10903 (bank10903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10904 := params 23
abbrev ray10904 := rays 23
def bank10904 : Fin 2 → Cell := twoBank p10904 ray10904
theorem signs10904 : ∀ j, Signs p10904 (bank10904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10905 := params 24
abbrev ray10905 := rays 24
def bank10905 : Fin 2 → Cell := twoBank p10905 ray10905
theorem signs10905 : ∀ j, Signs p10905 (bank10905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10906 := params 25
abbrev ray10906 := rays 25
def bank10906 : Fin 2 → Cell := twoBank p10906 ray10906
theorem signs10906 : ∀ j, Signs p10906 (bank10906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10907 := params 26
abbrev ray10907 := rays 26
def bank10907 : Fin 2 → Cell := twoBank p10907 ray10907
theorem signs10907 : ∀ j, Signs p10907 (bank10907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10908 := params 27
abbrev ray10908 := rays 27
def bank10908 : Fin 2 → Cell := twoBank p10908 ray10908
theorem signs10908 : ∀ j, Signs p10908 (bank10908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10909 := params 28
abbrev ray10909 := rays 28
def bank10909 : Fin 2 → Cell := twoBank p10909 ray10909
theorem signs10909 : ∀ j, Signs p10909 (bank10909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10910 := params 29
abbrev ray10910 := rays 29
def bank10910 : Fin 2 → Cell := twoBank p10910 ray10910
theorem signs10910 : ∀ j, Signs p10910 (bank10910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10911 := params 30
abbrev ray10911 := rays 30
def bank10911 : Fin 2 → Cell := twoBank p10911 ray10911
theorem signs10911 : ∀ j, Signs p10911 (bank10911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10912 := params 31
abbrev ray10912 := rays 31
def bank10912 : Fin 2 → Cell := twoBank p10912 ray10912
theorem signs10912 : ∀ j, Signs p10912 (bank10912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10881_10912
