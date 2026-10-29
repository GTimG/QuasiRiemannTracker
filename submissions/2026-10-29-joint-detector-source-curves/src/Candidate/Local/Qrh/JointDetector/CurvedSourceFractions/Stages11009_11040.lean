/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11009_11040
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97089950148271,97089563282586,97089176397089,97088789491781,97088402566663,97088015621735,97087628656997,97087241672450,97086854668094,97086467643930,97086080599959,97085693536180,97085306452595,97084919349204,97084532226007,97084145083005,97083757920198,97083370737587,97082983535172,97082596312954,97082209070933,97081821809110,97081434527485,97081047226059,97080659904832,97080272563805,97079885202978,97079497822352,97079110421927,97078723001704,97078335561683,97077948101864,97077560622248]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11008+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11009 := params 0
abbrev ray11009 := rays 0
def bank11009 : Fin 2 → Cell := twoBank p11009 ray11009
theorem signs11009 : ∀ j, Signs p11009 (bank11009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11010 := params 1
abbrev ray11010 := rays 1
def bank11010 : Fin 2 → Cell := twoBank p11010 ray11010
theorem signs11010 : ∀ j, Signs p11010 (bank11010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11011 := params 2
abbrev ray11011 := rays 2
def bank11011 : Fin 2 → Cell := twoBank p11011 ray11011
theorem signs11011 : ∀ j, Signs p11011 (bank11011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11012 := params 3
abbrev ray11012 := rays 3
def bank11012 : Fin 2 → Cell := twoBank p11012 ray11012
theorem signs11012 : ∀ j, Signs p11012 (bank11012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11013 := params 4
abbrev ray11013 := rays 4
def bank11013 : Fin 2 → Cell := twoBank p11013 ray11013
theorem signs11013 : ∀ j, Signs p11013 (bank11013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11014 := params 5
abbrev ray11014 := rays 5
def bank11014 : Fin 2 → Cell := twoBank p11014 ray11014
theorem signs11014 : ∀ j, Signs p11014 (bank11014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11015 := params 6
abbrev ray11015 := rays 6
def bank11015 : Fin 2 → Cell := twoBank p11015 ray11015
theorem signs11015 : ∀ j, Signs p11015 (bank11015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11016 := params 7
abbrev ray11016 := rays 7
def bank11016 : Fin 2 → Cell := twoBank p11016 ray11016
theorem signs11016 : ∀ j, Signs p11016 (bank11016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11017 := params 8
abbrev ray11017 := rays 8
def bank11017 : Fin 2 → Cell := twoBank p11017 ray11017
theorem signs11017 : ∀ j, Signs p11017 (bank11017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11018 := params 9
abbrev ray11018 := rays 9
def bank11018 : Fin 2 → Cell := twoBank p11018 ray11018
theorem signs11018 : ∀ j, Signs p11018 (bank11018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11019 := params 10
abbrev ray11019 := rays 10
def bank11019 : Fin 2 → Cell := twoBank p11019 ray11019
theorem signs11019 : ∀ j, Signs p11019 (bank11019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11020 := params 11
abbrev ray11020 := rays 11
def bank11020 : Fin 2 → Cell := twoBank p11020 ray11020
theorem signs11020 : ∀ j, Signs p11020 (bank11020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11021 := params 12
abbrev ray11021 := rays 12
def bank11021 : Fin 2 → Cell := twoBank p11021 ray11021
theorem signs11021 : ∀ j, Signs p11021 (bank11021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11022 := params 13
abbrev ray11022 := rays 13
def bank11022 : Fin 2 → Cell := twoBank p11022 ray11022
theorem signs11022 : ∀ j, Signs p11022 (bank11022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11023 := params 14
abbrev ray11023 := rays 14
def bank11023 : Fin 2 → Cell := twoBank p11023 ray11023
theorem signs11023 : ∀ j, Signs p11023 (bank11023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11024 := params 15
abbrev ray11024 := rays 15
def bank11024 : Fin 2 → Cell := twoBank p11024 ray11024
theorem signs11024 : ∀ j, Signs p11024 (bank11024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11025 := params 16
abbrev ray11025 := rays 16
def bank11025 : Fin 2 → Cell := twoBank p11025 ray11025
theorem signs11025 : ∀ j, Signs p11025 (bank11025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11026 := params 17
abbrev ray11026 := rays 17
def bank11026 : Fin 2 → Cell := twoBank p11026 ray11026
theorem signs11026 : ∀ j, Signs p11026 (bank11026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11027 := params 18
abbrev ray11027 := rays 18
def bank11027 : Fin 2 → Cell := twoBank p11027 ray11027
theorem signs11027 : ∀ j, Signs p11027 (bank11027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11028 := params 19
abbrev ray11028 := rays 19
def bank11028 : Fin 2 → Cell := twoBank p11028 ray11028
theorem signs11028 : ∀ j, Signs p11028 (bank11028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11029 := params 20
abbrev ray11029 := rays 20
def bank11029 : Fin 2 → Cell := twoBank p11029 ray11029
theorem signs11029 : ∀ j, Signs p11029 (bank11029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11030 := params 21
abbrev ray11030 := rays 21
def bank11030 : Fin 2 → Cell := twoBank p11030 ray11030
theorem signs11030 : ∀ j, Signs p11030 (bank11030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11031 := params 22
abbrev ray11031 := rays 22
def bank11031 : Fin 2 → Cell := twoBank p11031 ray11031
theorem signs11031 : ∀ j, Signs p11031 (bank11031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11032 := params 23
abbrev ray11032 := rays 23
def bank11032 : Fin 2 → Cell := twoBank p11032 ray11032
theorem signs11032 : ∀ j, Signs p11032 (bank11032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11033 := params 24
abbrev ray11033 := rays 24
def bank11033 : Fin 2 → Cell := twoBank p11033 ray11033
theorem signs11033 : ∀ j, Signs p11033 (bank11033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11034 := params 25
abbrev ray11034 := rays 25
def bank11034 : Fin 2 → Cell := twoBank p11034 ray11034
theorem signs11034 : ∀ j, Signs p11034 (bank11034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11035 := params 26
abbrev ray11035 := rays 26
def bank11035 : Fin 2 → Cell := twoBank p11035 ray11035
theorem signs11035 : ∀ j, Signs p11035 (bank11035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11036 := params 27
abbrev ray11036 := rays 27
def bank11036 : Fin 2 → Cell := twoBank p11036 ray11036
theorem signs11036 : ∀ j, Signs p11036 (bank11036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11037 := params 28
abbrev ray11037 := rays 28
def bank11037 : Fin 2 → Cell := twoBank p11037 ray11037
theorem signs11037 : ∀ j, Signs p11037 (bank11037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11038 := params 29
abbrev ray11038 := rays 29
def bank11038 : Fin 2 → Cell := twoBank p11038 ray11038
theorem signs11038 : ∀ j, Signs p11038 (bank11038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11039 := params 30
abbrev ray11039 := rays 30
def bank11039 : Fin 2 → Cell := twoBank p11039 ray11039
theorem signs11039 : ∀ j, Signs p11039 (bank11039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11040 := params 31
abbrev ray11040 := rays 31
def bank11040 : Fin 2 → Cell := twoBank p11040 ray11040
theorem signs11040 : ∀ j, Signs p11040 (bank11040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11009_11040
