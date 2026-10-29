/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11041_11072
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97077560622248,97077173122836,97076785603628,97076398064625,97076010505827,97075622927234,97075235328847,97074847710667,97074460072694,97074072414928,97073684737370,97073297040021,97072909322881,97072521585950,97072133829229,97071746052719,97071358256420,97070970440332,97070582604456,97070194748792,97069806873341,97069418978104,97069031063080,97068643128271,97068255173676,97067867199297,97067479205134,97067091191187,97066703157457,97066315103944,97065927030649,97065538937572,97065150824713]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11040+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11041 := params 0
abbrev ray11041 := rays 0
def bank11041 : Fin 2 → Cell := twoBank p11041 ray11041
theorem signs11041 : ∀ j, Signs p11041 (bank11041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11042 := params 1
abbrev ray11042 := rays 1
def bank11042 : Fin 2 → Cell := twoBank p11042 ray11042
theorem signs11042 : ∀ j, Signs p11042 (bank11042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11043 := params 2
abbrev ray11043 := rays 2
def bank11043 : Fin 2 → Cell := twoBank p11043 ray11043
theorem signs11043 : ∀ j, Signs p11043 (bank11043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11044 := params 3
abbrev ray11044 := rays 3
def bank11044 : Fin 2 → Cell := twoBank p11044 ray11044
theorem signs11044 : ∀ j, Signs p11044 (bank11044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11045 := params 4
abbrev ray11045 := rays 4
def bank11045 : Fin 2 → Cell := twoBank p11045 ray11045
theorem signs11045 : ∀ j, Signs p11045 (bank11045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11046 := params 5
abbrev ray11046 := rays 5
def bank11046 : Fin 2 → Cell := twoBank p11046 ray11046
theorem signs11046 : ∀ j, Signs p11046 (bank11046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11047 := params 6
abbrev ray11047 := rays 6
def bank11047 : Fin 2 → Cell := twoBank p11047 ray11047
theorem signs11047 : ∀ j, Signs p11047 (bank11047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11048 := params 7
abbrev ray11048 := rays 7
def bank11048 : Fin 2 → Cell := twoBank p11048 ray11048
theorem signs11048 : ∀ j, Signs p11048 (bank11048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11049 := params 8
abbrev ray11049 := rays 8
def bank11049 : Fin 2 → Cell := twoBank p11049 ray11049
theorem signs11049 : ∀ j, Signs p11049 (bank11049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11050 := params 9
abbrev ray11050 := rays 9
def bank11050 : Fin 2 → Cell := twoBank p11050 ray11050
theorem signs11050 : ∀ j, Signs p11050 (bank11050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11051 := params 10
abbrev ray11051 := rays 10
def bank11051 : Fin 2 → Cell := twoBank p11051 ray11051
theorem signs11051 : ∀ j, Signs p11051 (bank11051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11052 := params 11
abbrev ray11052 := rays 11
def bank11052 : Fin 2 → Cell := twoBank p11052 ray11052
theorem signs11052 : ∀ j, Signs p11052 (bank11052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11053 := params 12
abbrev ray11053 := rays 12
def bank11053 : Fin 2 → Cell := twoBank p11053 ray11053
theorem signs11053 : ∀ j, Signs p11053 (bank11053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11054 := params 13
abbrev ray11054 := rays 13
def bank11054 : Fin 2 → Cell := twoBank p11054 ray11054
theorem signs11054 : ∀ j, Signs p11054 (bank11054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11055 := params 14
abbrev ray11055 := rays 14
def bank11055 : Fin 2 → Cell := twoBank p11055 ray11055
theorem signs11055 : ∀ j, Signs p11055 (bank11055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11056 := params 15
abbrev ray11056 := rays 15
def bank11056 : Fin 2 → Cell := twoBank p11056 ray11056
theorem signs11056 : ∀ j, Signs p11056 (bank11056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11057 := params 16
abbrev ray11057 := rays 16
def bank11057 : Fin 2 → Cell := twoBank p11057 ray11057
theorem signs11057 : ∀ j, Signs p11057 (bank11057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11058 := params 17
abbrev ray11058 := rays 17
def bank11058 : Fin 2 → Cell := twoBank p11058 ray11058
theorem signs11058 : ∀ j, Signs p11058 (bank11058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11059 := params 18
abbrev ray11059 := rays 18
def bank11059 : Fin 2 → Cell := twoBank p11059 ray11059
theorem signs11059 : ∀ j, Signs p11059 (bank11059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11060 := params 19
abbrev ray11060 := rays 19
def bank11060 : Fin 2 → Cell := twoBank p11060 ray11060
theorem signs11060 : ∀ j, Signs p11060 (bank11060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11061 := params 20
abbrev ray11061 := rays 20
def bank11061 : Fin 2 → Cell := twoBank p11061 ray11061
theorem signs11061 : ∀ j, Signs p11061 (bank11061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11062 := params 21
abbrev ray11062 := rays 21
def bank11062 : Fin 2 → Cell := twoBank p11062 ray11062
theorem signs11062 : ∀ j, Signs p11062 (bank11062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11063 := params 22
abbrev ray11063 := rays 22
def bank11063 : Fin 2 → Cell := twoBank p11063 ray11063
theorem signs11063 : ∀ j, Signs p11063 (bank11063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11064 := params 23
abbrev ray11064 := rays 23
def bank11064 : Fin 2 → Cell := twoBank p11064 ray11064
theorem signs11064 : ∀ j, Signs p11064 (bank11064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11065 := params 24
abbrev ray11065 := rays 24
def bank11065 : Fin 2 → Cell := twoBank p11065 ray11065
theorem signs11065 : ∀ j, Signs p11065 (bank11065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11066 := params 25
abbrev ray11066 := rays 25
def bank11066 : Fin 2 → Cell := twoBank p11066 ray11066
theorem signs11066 : ∀ j, Signs p11066 (bank11066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11067 := params 26
abbrev ray11067 := rays 26
def bank11067 : Fin 2 → Cell := twoBank p11067 ray11067
theorem signs11067 : ∀ j, Signs p11067 (bank11067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11068 := params 27
abbrev ray11068 := rays 27
def bank11068 : Fin 2 → Cell := twoBank p11068 ray11068
theorem signs11068 : ∀ j, Signs p11068 (bank11068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11069 := params 28
abbrev ray11069 := rays 28
def bank11069 : Fin 2 → Cell := twoBank p11069 ray11069
theorem signs11069 : ∀ j, Signs p11069 (bank11069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11070 := params 29
abbrev ray11070 := rays 29
def bank11070 : Fin 2 → Cell := twoBank p11070 ray11070
theorem signs11070 : ∀ j, Signs p11070 (bank11070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11071 := params 30
abbrev ray11071 := rays 30
def bank11071 : Fin 2 → Cell := twoBank p11071 ray11071
theorem signs11071 : ∀ j, Signs p11071 (bank11071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11072 := params 31
abbrev ray11072 := rays 31
def bank11072 : Fin 2 → Cell := twoBank p11072 ray11072
theorem signs11072 : ∀ j, Signs p11072 (bank11072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11041_11072
