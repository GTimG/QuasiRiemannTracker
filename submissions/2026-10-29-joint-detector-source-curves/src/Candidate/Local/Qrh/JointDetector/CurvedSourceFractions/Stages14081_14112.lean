/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14081_14112
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95812269042052,95811826525629,95811383993006,95810941444184,95810498879164,95810056297945,95809613700528,95809171086912,95808728457098,95808285811086,95807843148877,95807400470470,95806957775866,95806515065065,95806072338067,95805629594872,95805186835480,95804744059892,95804301268108,95803858460127,95803415635951,95802972795579,95802529939011,95802087066248,95801644177290,95801201272137,95800758350789,95800315413246,95799872459509,95799429489577,95798986503451,95798543501131,95798100482617]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14080+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14081 := params 0
abbrev ray14081 := rays 0
def bank14081 : Fin 1 → Cell := oneBank p14081 ray14081
theorem signs14081 : ∀ j, Signs p14081 (bank14081 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14082 := params 1
abbrev ray14082 := rays 1
def bank14082 : Fin 1 → Cell := oneBank p14082 ray14082
theorem signs14082 : ∀ j, Signs p14082 (bank14082 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14083 := params 2
abbrev ray14083 := rays 2
def bank14083 : Fin 1 → Cell := oneBank p14083 ray14083
theorem signs14083 : ∀ j, Signs p14083 (bank14083 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14084 := params 3
abbrev ray14084 := rays 3
def bank14084 : Fin 1 → Cell := oneBank p14084 ray14084
theorem signs14084 : ∀ j, Signs p14084 (bank14084 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14085 := params 4
abbrev ray14085 := rays 4
def bank14085 : Fin 1 → Cell := oneBank p14085 ray14085
theorem signs14085 : ∀ j, Signs p14085 (bank14085 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14086 := params 5
abbrev ray14086 := rays 5
def bank14086 : Fin 1 → Cell := oneBank p14086 ray14086
theorem signs14086 : ∀ j, Signs p14086 (bank14086 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14087 := params 6
abbrev ray14087 := rays 6
def bank14087 : Fin 1 → Cell := oneBank p14087 ray14087
theorem signs14087 : ∀ j, Signs p14087 (bank14087 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14088 := params 7
abbrev ray14088 := rays 7
def bank14088 : Fin 1 → Cell := oneBank p14088 ray14088
theorem signs14088 : ∀ j, Signs p14088 (bank14088 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14089 := params 8
abbrev ray14089 := rays 8
def bank14089 : Fin 1 → Cell := oneBank p14089 ray14089
theorem signs14089 : ∀ j, Signs p14089 (bank14089 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14090 := params 9
abbrev ray14090 := rays 9
def bank14090 : Fin 1 → Cell := oneBank p14090 ray14090
theorem signs14090 : ∀ j, Signs p14090 (bank14090 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14091 := params 10
abbrev ray14091 := rays 10
def bank14091 : Fin 1 → Cell := oneBank p14091 ray14091
theorem signs14091 : ∀ j, Signs p14091 (bank14091 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14092 := params 11
abbrev ray14092 := rays 11
def bank14092 : Fin 1 → Cell := oneBank p14092 ray14092
theorem signs14092 : ∀ j, Signs p14092 (bank14092 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14093 := params 12
abbrev ray14093 := rays 12
def bank14093 : Fin 1 → Cell := oneBank p14093 ray14093
theorem signs14093 : ∀ j, Signs p14093 (bank14093 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14094 := params 13
abbrev ray14094 := rays 13
def bank14094 : Fin 1 → Cell := oneBank p14094 ray14094
theorem signs14094 : ∀ j, Signs p14094 (bank14094 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14095 := params 14
abbrev ray14095 := rays 14
def bank14095 : Fin 1 → Cell := oneBank p14095 ray14095
theorem signs14095 : ∀ j, Signs p14095 (bank14095 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14096 := params 15
abbrev ray14096 := rays 15
def bank14096 : Fin 1 → Cell := oneBank p14096 ray14096
theorem signs14096 : ∀ j, Signs p14096 (bank14096 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14097 := params 16
abbrev ray14097 := rays 16
def bank14097 : Fin 1 → Cell := oneBank p14097 ray14097
theorem signs14097 : ∀ j, Signs p14097 (bank14097 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14098 := params 17
abbrev ray14098 := rays 17
def bank14098 : Fin 1 → Cell := oneBank p14098 ray14098
theorem signs14098 : ∀ j, Signs p14098 (bank14098 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14099 := params 18
abbrev ray14099 := rays 18
def bank14099 : Fin 1 → Cell := oneBank p14099 ray14099
theorem signs14099 : ∀ j, Signs p14099 (bank14099 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14100 := params 19
abbrev ray14100 := rays 19
def bank14100 : Fin 1 → Cell := oneBank p14100 ray14100
theorem signs14100 : ∀ j, Signs p14100 (bank14100 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14101 := params 20
abbrev ray14101 := rays 20
def bank14101 : Fin 1 → Cell := oneBank p14101 ray14101
theorem signs14101 : ∀ j, Signs p14101 (bank14101 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14102 := params 21
abbrev ray14102 := rays 21
def bank14102 : Fin 1 → Cell := oneBank p14102 ray14102
theorem signs14102 : ∀ j, Signs p14102 (bank14102 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14103 := params 22
abbrev ray14103 := rays 22
def bank14103 : Fin 1 → Cell := oneBank p14103 ray14103
theorem signs14103 : ∀ j, Signs p14103 (bank14103 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14104 := params 23
abbrev ray14104 := rays 23
def bank14104 : Fin 1 → Cell := oneBank p14104 ray14104
theorem signs14104 : ∀ j, Signs p14104 (bank14104 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14105 := params 24
abbrev ray14105 := rays 24
def bank14105 : Fin 1 → Cell := oneBank p14105 ray14105
theorem signs14105 : ∀ j, Signs p14105 (bank14105 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14106 := params 25
abbrev ray14106 := rays 25
def bank14106 : Fin 1 → Cell := oneBank p14106 ray14106
theorem signs14106 : ∀ j, Signs p14106 (bank14106 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14107 := params 26
abbrev ray14107 := rays 26
def bank14107 : Fin 1 → Cell := oneBank p14107 ray14107
theorem signs14107 : ∀ j, Signs p14107 (bank14107 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14108 := params 27
abbrev ray14108 := rays 27
def bank14108 : Fin 1 → Cell := oneBank p14108 ray14108
theorem signs14108 : ∀ j, Signs p14108 (bank14108 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14109 := params 28
abbrev ray14109 := rays 28
def bank14109 : Fin 1 → Cell := oneBank p14109 ray14109
theorem signs14109 : ∀ j, Signs p14109 (bank14109 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14110 := params 29
abbrev ray14110 := rays 29
def bank14110 : Fin 1 → Cell := oneBank p14110 ray14110
theorem signs14110 : ∀ j, Signs p14110 (bank14110 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14111 := params 30
abbrev ray14111 := rays 30
def bank14111 : Fin 1 → Cell := oneBank p14111 ray14111
theorem signs14111 : ∀ j, Signs p14111 (bank14111 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14112 := params 31
abbrev ray14112 := rays 31
def bank14112 : Fin 1 → Cell := oneBank p14112 ray14112
theorem signs14112 : ∀ j, Signs p14112 (bank14112 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14081_14112
