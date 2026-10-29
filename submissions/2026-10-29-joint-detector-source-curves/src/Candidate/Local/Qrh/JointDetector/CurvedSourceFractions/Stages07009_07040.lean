/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07009_07040
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98472957819839,98472654828837,98472351815513,98472048779868,98471745721903,98471442641618,98471139539015,98470836414094,98470533266856,98470230097301,98469926905431,98469623691246,98469320454747,98469017195935,98468713914811,98468410611375,98468107285629,98467803937573,98467500567207,98467197174533,98466893759551,98466590322262,98466286862667,98465983380767,98465679876563,98465376350055,98465072801244,98464769230131,98464465636716,98464162021001,98463858382986,98463554722672,98463251040060]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7008+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7009 := params 0
abbrev ray7009 := rays 0
def bank7009 : Fin 2 → Cell := twoBank p7009 ray7009
theorem signs7009 : ∀ j, Signs p7009 (bank7009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7010 := params 1
abbrev ray7010 := rays 1
def bank7010 : Fin 2 → Cell := twoBank p7010 ray7010
theorem signs7010 : ∀ j, Signs p7010 (bank7010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7011 := params 2
abbrev ray7011 := rays 2
def bank7011 : Fin 2 → Cell := twoBank p7011 ray7011
theorem signs7011 : ∀ j, Signs p7011 (bank7011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7012 := params 3
abbrev ray7012 := rays 3
def bank7012 : Fin 2 → Cell := twoBank p7012 ray7012
theorem signs7012 : ∀ j, Signs p7012 (bank7012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7013 := params 4
abbrev ray7013 := rays 4
def bank7013 : Fin 2 → Cell := twoBank p7013 ray7013
theorem signs7013 : ∀ j, Signs p7013 (bank7013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7014 := params 5
abbrev ray7014 := rays 5
def bank7014 : Fin 2 → Cell := twoBank p7014 ray7014
theorem signs7014 : ∀ j, Signs p7014 (bank7014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7015 := params 6
abbrev ray7015 := rays 6
def bank7015 : Fin 2 → Cell := twoBank p7015 ray7015
theorem signs7015 : ∀ j, Signs p7015 (bank7015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7016 := params 7
abbrev ray7016 := rays 7
def bank7016 : Fin 2 → Cell := twoBank p7016 ray7016
theorem signs7016 : ∀ j, Signs p7016 (bank7016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7017 := params 8
abbrev ray7017 := rays 8
def bank7017 : Fin 2 → Cell := twoBank p7017 ray7017
theorem signs7017 : ∀ j, Signs p7017 (bank7017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7018 := params 9
abbrev ray7018 := rays 9
def bank7018 : Fin 2 → Cell := twoBank p7018 ray7018
theorem signs7018 : ∀ j, Signs p7018 (bank7018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7019 := params 10
abbrev ray7019 := rays 10
def bank7019 : Fin 2 → Cell := twoBank p7019 ray7019
theorem signs7019 : ∀ j, Signs p7019 (bank7019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7020 := params 11
abbrev ray7020 := rays 11
def bank7020 : Fin 2 → Cell := twoBank p7020 ray7020
theorem signs7020 : ∀ j, Signs p7020 (bank7020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7021 := params 12
abbrev ray7021 := rays 12
def bank7021 : Fin 2 → Cell := twoBank p7021 ray7021
theorem signs7021 : ∀ j, Signs p7021 (bank7021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7022 := params 13
abbrev ray7022 := rays 13
def bank7022 : Fin 2 → Cell := twoBank p7022 ray7022
theorem signs7022 : ∀ j, Signs p7022 (bank7022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7023 := params 14
abbrev ray7023 := rays 14
def bank7023 : Fin 2 → Cell := twoBank p7023 ray7023
theorem signs7023 : ∀ j, Signs p7023 (bank7023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7024 := params 15
abbrev ray7024 := rays 15
def bank7024 : Fin 2 → Cell := twoBank p7024 ray7024
theorem signs7024 : ∀ j, Signs p7024 (bank7024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7025 := params 16
abbrev ray7025 := rays 16
def bank7025 : Fin 2 → Cell := twoBank p7025 ray7025
theorem signs7025 : ∀ j, Signs p7025 (bank7025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7026 := params 17
abbrev ray7026 := rays 17
def bank7026 : Fin 2 → Cell := twoBank p7026 ray7026
theorem signs7026 : ∀ j, Signs p7026 (bank7026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7027 := params 18
abbrev ray7027 := rays 18
def bank7027 : Fin 2 → Cell := twoBank p7027 ray7027
theorem signs7027 : ∀ j, Signs p7027 (bank7027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7028 := params 19
abbrev ray7028 := rays 19
def bank7028 : Fin 2 → Cell := twoBank p7028 ray7028
theorem signs7028 : ∀ j, Signs p7028 (bank7028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7029 := params 20
abbrev ray7029 := rays 20
def bank7029 : Fin 2 → Cell := twoBank p7029 ray7029
theorem signs7029 : ∀ j, Signs p7029 (bank7029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7030 := params 21
abbrev ray7030 := rays 21
def bank7030 : Fin 2 → Cell := twoBank p7030 ray7030
theorem signs7030 : ∀ j, Signs p7030 (bank7030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7031 := params 22
abbrev ray7031 := rays 22
def bank7031 : Fin 2 → Cell := twoBank p7031 ray7031
theorem signs7031 : ∀ j, Signs p7031 (bank7031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7032 := params 23
abbrev ray7032 := rays 23
def bank7032 : Fin 2 → Cell := twoBank p7032 ray7032
theorem signs7032 : ∀ j, Signs p7032 (bank7032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7033 := params 24
abbrev ray7033 := rays 24
def bank7033 : Fin 2 → Cell := twoBank p7033 ray7033
theorem signs7033 : ∀ j, Signs p7033 (bank7033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7034 := params 25
abbrev ray7034 := rays 25
def bank7034 : Fin 2 → Cell := twoBank p7034 ray7034
theorem signs7034 : ∀ j, Signs p7034 (bank7034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7035 := params 26
abbrev ray7035 := rays 26
def bank7035 : Fin 2 → Cell := twoBank p7035 ray7035
theorem signs7035 : ∀ j, Signs p7035 (bank7035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7036 := params 27
abbrev ray7036 := rays 27
def bank7036 : Fin 2 → Cell := twoBank p7036 ray7036
theorem signs7036 : ∀ j, Signs p7036 (bank7036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7037 := params 28
abbrev ray7037 := rays 28
def bank7037 : Fin 2 → Cell := twoBank p7037 ray7037
theorem signs7037 : ∀ j, Signs p7037 (bank7037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7038 := params 29
abbrev ray7038 := rays 29
def bank7038 : Fin 2 → Cell := twoBank p7038 ray7038
theorem signs7038 : ∀ j, Signs p7038 (bank7038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7039 := params 30
abbrev ray7039 := rays 30
def bank7039 : Fin 2 → Cell := twoBank p7039 ray7039
theorem signs7039 : ∀ j, Signs p7039 (bank7039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7040 := params 31
abbrev ray7040 := rays 31
def bank7040 : Fin 2 → Cell := twoBank p7040 ray7040
theorem signs7040 : ∀ j, Signs p7040 (bank7040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07009_07040
