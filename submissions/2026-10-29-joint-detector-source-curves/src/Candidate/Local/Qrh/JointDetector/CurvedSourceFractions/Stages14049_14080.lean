/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14049_14080
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95826421013384,95825979015428,95825537001267,95825094970901,95824652924331,95824210861556,95823768782577,95823326687394,95822884576007,95822442448417,95822000304623,95821558144626,95821115968426,95820673776023,95820231567417,95819789342609,95819347101598,95818904844385,95818462570970,95818020281353,95817577975535,95817135653515,95816693315294,95816250960872,95815808590249,95815366203425,95814923800401,95814481381176,95814038945751,95813596494126,95813154026301,95812711542276,95812269042052]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14048+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14049 := params 0
abbrev ray14049 := rays 0
def bank14049 : Fin 1 → Cell := oneBank p14049 ray14049
theorem signs14049 : ∀ j, Signs p14049 (bank14049 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14050 := params 1
abbrev ray14050 := rays 1
def bank14050 : Fin 1 → Cell := oneBank p14050 ray14050
theorem signs14050 : ∀ j, Signs p14050 (bank14050 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14051 := params 2
abbrev ray14051 := rays 2
def bank14051 : Fin 1 → Cell := oneBank p14051 ray14051
theorem signs14051 : ∀ j, Signs p14051 (bank14051 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14052 := params 3
abbrev ray14052 := rays 3
def bank14052 : Fin 1 → Cell := oneBank p14052 ray14052
theorem signs14052 : ∀ j, Signs p14052 (bank14052 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14053 := params 4
abbrev ray14053 := rays 4
def bank14053 : Fin 1 → Cell := oneBank p14053 ray14053
theorem signs14053 : ∀ j, Signs p14053 (bank14053 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14054 := params 5
abbrev ray14054 := rays 5
def bank14054 : Fin 1 → Cell := oneBank p14054 ray14054
theorem signs14054 : ∀ j, Signs p14054 (bank14054 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14055 := params 6
abbrev ray14055 := rays 6
def bank14055 : Fin 1 → Cell := oneBank p14055 ray14055
theorem signs14055 : ∀ j, Signs p14055 (bank14055 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14056 := params 7
abbrev ray14056 := rays 7
def bank14056 : Fin 1 → Cell := oneBank p14056 ray14056
theorem signs14056 : ∀ j, Signs p14056 (bank14056 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14057 := params 8
abbrev ray14057 := rays 8
def bank14057 : Fin 1 → Cell := oneBank p14057 ray14057
theorem signs14057 : ∀ j, Signs p14057 (bank14057 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14058 := params 9
abbrev ray14058 := rays 9
def bank14058 : Fin 1 → Cell := oneBank p14058 ray14058
theorem signs14058 : ∀ j, Signs p14058 (bank14058 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14059 := params 10
abbrev ray14059 := rays 10
def bank14059 : Fin 1 → Cell := oneBank p14059 ray14059
theorem signs14059 : ∀ j, Signs p14059 (bank14059 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14060 := params 11
abbrev ray14060 := rays 11
def bank14060 : Fin 1 → Cell := oneBank p14060 ray14060
theorem signs14060 : ∀ j, Signs p14060 (bank14060 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14061 := params 12
abbrev ray14061 := rays 12
def bank14061 : Fin 1 → Cell := oneBank p14061 ray14061
theorem signs14061 : ∀ j, Signs p14061 (bank14061 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14062 := params 13
abbrev ray14062 := rays 13
def bank14062 : Fin 1 → Cell := oneBank p14062 ray14062
theorem signs14062 : ∀ j, Signs p14062 (bank14062 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14063 := params 14
abbrev ray14063 := rays 14
def bank14063 : Fin 1 → Cell := oneBank p14063 ray14063
theorem signs14063 : ∀ j, Signs p14063 (bank14063 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14064 := params 15
abbrev ray14064 := rays 15
def bank14064 : Fin 1 → Cell := oneBank p14064 ray14064
theorem signs14064 : ∀ j, Signs p14064 (bank14064 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14065 := params 16
abbrev ray14065 := rays 16
def bank14065 : Fin 1 → Cell := oneBank p14065 ray14065
theorem signs14065 : ∀ j, Signs p14065 (bank14065 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14066 := params 17
abbrev ray14066 := rays 17
def bank14066 : Fin 1 → Cell := oneBank p14066 ray14066
theorem signs14066 : ∀ j, Signs p14066 (bank14066 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14067 := params 18
abbrev ray14067 := rays 18
def bank14067 : Fin 1 → Cell := oneBank p14067 ray14067
theorem signs14067 : ∀ j, Signs p14067 (bank14067 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14068 := params 19
abbrev ray14068 := rays 19
def bank14068 : Fin 1 → Cell := oneBank p14068 ray14068
theorem signs14068 : ∀ j, Signs p14068 (bank14068 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14069 := params 20
abbrev ray14069 := rays 20
def bank14069 : Fin 1 → Cell := oneBank p14069 ray14069
theorem signs14069 : ∀ j, Signs p14069 (bank14069 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14070 := params 21
abbrev ray14070 := rays 21
def bank14070 : Fin 1 → Cell := oneBank p14070 ray14070
theorem signs14070 : ∀ j, Signs p14070 (bank14070 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14071 := params 22
abbrev ray14071 := rays 22
def bank14071 : Fin 1 → Cell := oneBank p14071 ray14071
theorem signs14071 : ∀ j, Signs p14071 (bank14071 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14072 := params 23
abbrev ray14072 := rays 23
def bank14072 : Fin 1 → Cell := oneBank p14072 ray14072
theorem signs14072 : ∀ j, Signs p14072 (bank14072 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14073 := params 24
abbrev ray14073 := rays 24
def bank14073 : Fin 1 → Cell := oneBank p14073 ray14073
theorem signs14073 : ∀ j, Signs p14073 (bank14073 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14074 := params 25
abbrev ray14074 := rays 25
def bank14074 : Fin 1 → Cell := oneBank p14074 ray14074
theorem signs14074 : ∀ j, Signs p14074 (bank14074 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14075 := params 26
abbrev ray14075 := rays 26
def bank14075 : Fin 1 → Cell := oneBank p14075 ray14075
theorem signs14075 : ∀ j, Signs p14075 (bank14075 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14076 := params 27
abbrev ray14076 := rays 27
def bank14076 : Fin 1 → Cell := oneBank p14076 ray14076
theorem signs14076 : ∀ j, Signs p14076 (bank14076 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14077 := params 28
abbrev ray14077 := rays 28
def bank14077 : Fin 1 → Cell := oneBank p14077 ray14077
theorem signs14077 : ∀ j, Signs p14077 (bank14077 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14078 := params 29
abbrev ray14078 := rays 29
def bank14078 : Fin 1 → Cell := oneBank p14078 ray14078
theorem signs14078 : ∀ j, Signs p14078 (bank14078 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14079 := params 30
abbrev ray14079 := rays 30
def bank14079 : Fin 1 → Cell := oneBank p14079 ray14079
theorem signs14079 : ∀ j, Signs p14079 (bank14079 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14080 := params 31
abbrev ray14080 := rays 31
def bank14080 : Fin 1 → Cell := oneBank p14080 ray14080
theorem signs14080 : ∀ j, Signs p14080 (bank14080 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14049_14080
