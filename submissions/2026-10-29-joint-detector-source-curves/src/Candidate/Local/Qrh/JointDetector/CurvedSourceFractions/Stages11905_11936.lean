/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11905_11936
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96735431753927,96735027326253,96734622879183,96734218412716,96733813926854,96733409421596,96733004896943,96732600352896,96732195789455,96731791206620,96731386604392,96730981982771,96730577341758,96730172681353,96729768001556,96729363302368,96728958583790,96728553845821,96728149088463,96727744311715,96727339515579,96726934700054,96726529865141,96726125010841,96725720137153,96725315244079,96724910331619,96724505399773,96724100448541,96723695477924,96723290487923,96722885478538,96722480449769]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11904+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11905 := params 0
abbrev ray11905 := rays 0
def bank11905 : Fin 2 → Cell := twoBank p11905 ray11905
theorem signs11905 : ∀ j, Signs p11905 (bank11905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11906 := params 1
abbrev ray11906 := rays 1
def bank11906 : Fin 2 → Cell := twoBank p11906 ray11906
theorem signs11906 : ∀ j, Signs p11906 (bank11906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11907 := params 2
abbrev ray11907 := rays 2
def bank11907 : Fin 2 → Cell := twoBank p11907 ray11907
theorem signs11907 : ∀ j, Signs p11907 (bank11907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11908 := params 3
abbrev ray11908 := rays 3
def bank11908 : Fin 2 → Cell := twoBank p11908 ray11908
theorem signs11908 : ∀ j, Signs p11908 (bank11908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11909 := params 4
abbrev ray11909 := rays 4
def bank11909 : Fin 2 → Cell := twoBank p11909 ray11909
theorem signs11909 : ∀ j, Signs p11909 (bank11909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11910 := params 5
abbrev ray11910 := rays 5
def bank11910 : Fin 2 → Cell := twoBank p11910 ray11910
theorem signs11910 : ∀ j, Signs p11910 (bank11910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11911 := params 6
abbrev ray11911 := rays 6
def bank11911 : Fin 2 → Cell := twoBank p11911 ray11911
theorem signs11911 : ∀ j, Signs p11911 (bank11911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11912 := params 7
abbrev ray11912 := rays 7
def bank11912 : Fin 2 → Cell := twoBank p11912 ray11912
theorem signs11912 : ∀ j, Signs p11912 (bank11912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11913 := params 8
abbrev ray11913 := rays 8
def bank11913 : Fin 2 → Cell := twoBank p11913 ray11913
theorem signs11913 : ∀ j, Signs p11913 (bank11913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11914 := params 9
abbrev ray11914 := rays 9
def bank11914 : Fin 2 → Cell := twoBank p11914 ray11914
theorem signs11914 : ∀ j, Signs p11914 (bank11914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11915 := params 10
abbrev ray11915 := rays 10
def bank11915 : Fin 2 → Cell := twoBank p11915 ray11915
theorem signs11915 : ∀ j, Signs p11915 (bank11915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11916 := params 11
abbrev ray11916 := rays 11
def bank11916 : Fin 2 → Cell := twoBank p11916 ray11916
theorem signs11916 : ∀ j, Signs p11916 (bank11916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11917 := params 12
abbrev ray11917 := rays 12
def bank11917 : Fin 2 → Cell := twoBank p11917 ray11917
theorem signs11917 : ∀ j, Signs p11917 (bank11917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11918 := params 13
abbrev ray11918 := rays 13
def bank11918 : Fin 2 → Cell := twoBank p11918 ray11918
theorem signs11918 : ∀ j, Signs p11918 (bank11918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11919 := params 14
abbrev ray11919 := rays 14
def bank11919 : Fin 2 → Cell := twoBank p11919 ray11919
theorem signs11919 : ∀ j, Signs p11919 (bank11919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11920 := params 15
abbrev ray11920 := rays 15
def bank11920 : Fin 2 → Cell := twoBank p11920 ray11920
theorem signs11920 : ∀ j, Signs p11920 (bank11920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11921 := params 16
abbrev ray11921 := rays 16
def bank11921 : Fin 2 → Cell := twoBank p11921 ray11921
theorem signs11921 : ∀ j, Signs p11921 (bank11921 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11922 := params 17
abbrev ray11922 := rays 17
def bank11922 : Fin 2 → Cell := twoBank p11922 ray11922
theorem signs11922 : ∀ j, Signs p11922 (bank11922 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11923 := params 18
abbrev ray11923 := rays 18
def bank11923 : Fin 2 → Cell := twoBank p11923 ray11923
theorem signs11923 : ∀ j, Signs p11923 (bank11923 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11924 := params 19
abbrev ray11924 := rays 19
def bank11924 : Fin 2 → Cell := twoBank p11924 ray11924
theorem signs11924 : ∀ j, Signs p11924 (bank11924 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11925 := params 20
abbrev ray11925 := rays 20
def bank11925 : Fin 2 → Cell := twoBank p11925 ray11925
theorem signs11925 : ∀ j, Signs p11925 (bank11925 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11926 := params 21
abbrev ray11926 := rays 21
def bank11926 : Fin 2 → Cell := twoBank p11926 ray11926
theorem signs11926 : ∀ j, Signs p11926 (bank11926 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11927 := params 22
abbrev ray11927 := rays 22
def bank11927 : Fin 2 → Cell := twoBank p11927 ray11927
theorem signs11927 : ∀ j, Signs p11927 (bank11927 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11928 := params 23
abbrev ray11928 := rays 23
def bank11928 : Fin 2 → Cell := twoBank p11928 ray11928
theorem signs11928 : ∀ j, Signs p11928 (bank11928 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11929 := params 24
abbrev ray11929 := rays 24
def bank11929 : Fin 2 → Cell := twoBank p11929 ray11929
theorem signs11929 : ∀ j, Signs p11929 (bank11929 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11930 := params 25
abbrev ray11930 := rays 25
def bank11930 : Fin 2 → Cell := twoBank p11930 ray11930
theorem signs11930 : ∀ j, Signs p11930 (bank11930 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11931 := params 26
abbrev ray11931 := rays 26
def bank11931 : Fin 2 → Cell := twoBank p11931 ray11931
theorem signs11931 : ∀ j, Signs p11931 (bank11931 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11932 := params 27
abbrev ray11932 := rays 27
def bank11932 : Fin 2 → Cell := twoBank p11932 ray11932
theorem signs11932 : ∀ j, Signs p11932 (bank11932 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11933 := params 28
abbrev ray11933 := rays 28
def bank11933 : Fin 2 → Cell := twoBank p11933 ray11933
theorem signs11933 : ∀ j, Signs p11933 (bank11933 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11934 := params 29
abbrev ray11934 := rays 29
def bank11934 : Fin 2 → Cell := twoBank p11934 ray11934
theorem signs11934 : ∀ j, Signs p11934 (bank11934 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11935 := params 30
abbrev ray11935 := rays 30
def bank11935 : Fin 2 → Cell := twoBank p11935 ray11935
theorem signs11935 : ∀ j, Signs p11935 (bank11935 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11936 := params 31
abbrev ray11936 := rays 31
def bank11936 : Fin 2 → Cell := twoBank p11936 ray11936
theorem signs11936 : ∀ j, Signs p11936 (bank11936 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11905_11936
