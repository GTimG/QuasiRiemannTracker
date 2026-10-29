/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05057_05088
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99020813583032,99020555783898,99020297960718,99020040113492,99019782242221,99019524346907,99019266427550,99019008484151,99018750516711,99018492525232,99018234509714,99017976470158,99017718406565,99017460318937,99017202207274,99016944071577,99016685911847,99016427728085,99016169520293,99015911288471,99015653032620,99015394752741,99015136448835,99014878120903,99014619768946,99014361392965,99014102992962,99013844568937,99013586120891,99013327648825,99013069152740,99012810632637,99012552088517]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5056+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5057 := params 0
abbrev ray5057 := rays 0
def bank5057 : Fin 2 → Cell := twoBank p5057 ray5057
theorem signs5057 : ∀ j, Signs p5057 (bank5057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5058 := params 1
abbrev ray5058 := rays 1
def bank5058 : Fin 2 → Cell := twoBank p5058 ray5058
theorem signs5058 : ∀ j, Signs p5058 (bank5058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5059 := params 2
abbrev ray5059 := rays 2
def bank5059 : Fin 2 → Cell := twoBank p5059 ray5059
theorem signs5059 : ∀ j, Signs p5059 (bank5059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5060 := params 3
abbrev ray5060 := rays 3
def bank5060 : Fin 2 → Cell := twoBank p5060 ray5060
theorem signs5060 : ∀ j, Signs p5060 (bank5060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5061 := params 4
abbrev ray5061 := rays 4
def bank5061 : Fin 2 → Cell := twoBank p5061 ray5061
theorem signs5061 : ∀ j, Signs p5061 (bank5061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5062 := params 5
abbrev ray5062 := rays 5
def bank5062 : Fin 2 → Cell := twoBank p5062 ray5062
theorem signs5062 : ∀ j, Signs p5062 (bank5062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5063 := params 6
abbrev ray5063 := rays 6
def bank5063 : Fin 2 → Cell := twoBank p5063 ray5063
theorem signs5063 : ∀ j, Signs p5063 (bank5063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5064 := params 7
abbrev ray5064 := rays 7
def bank5064 : Fin 2 → Cell := twoBank p5064 ray5064
theorem signs5064 : ∀ j, Signs p5064 (bank5064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5065 := params 8
abbrev ray5065 := rays 8
def bank5065 : Fin 2 → Cell := twoBank p5065 ray5065
theorem signs5065 : ∀ j, Signs p5065 (bank5065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5066 := params 9
abbrev ray5066 := rays 9
def bank5066 : Fin 2 → Cell := twoBank p5066 ray5066
theorem signs5066 : ∀ j, Signs p5066 (bank5066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5067 := params 10
abbrev ray5067 := rays 10
def bank5067 : Fin 2 → Cell := twoBank p5067 ray5067
theorem signs5067 : ∀ j, Signs p5067 (bank5067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5068 := params 11
abbrev ray5068 := rays 11
def bank5068 : Fin 2 → Cell := twoBank p5068 ray5068
theorem signs5068 : ∀ j, Signs p5068 (bank5068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5069 := params 12
abbrev ray5069 := rays 12
def bank5069 : Fin 2 → Cell := twoBank p5069 ray5069
theorem signs5069 : ∀ j, Signs p5069 (bank5069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5070 := params 13
abbrev ray5070 := rays 13
def bank5070 : Fin 2 → Cell := twoBank p5070 ray5070
theorem signs5070 : ∀ j, Signs p5070 (bank5070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5071 := params 14
abbrev ray5071 := rays 14
def bank5071 : Fin 2 → Cell := twoBank p5071 ray5071
theorem signs5071 : ∀ j, Signs p5071 (bank5071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5072 := params 15
abbrev ray5072 := rays 15
def bank5072 : Fin 2 → Cell := twoBank p5072 ray5072
theorem signs5072 : ∀ j, Signs p5072 (bank5072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5073 := params 16
abbrev ray5073 := rays 16
def bank5073 : Fin 2 → Cell := twoBank p5073 ray5073
theorem signs5073 : ∀ j, Signs p5073 (bank5073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5074 := params 17
abbrev ray5074 := rays 17
def bank5074 : Fin 2 → Cell := twoBank p5074 ray5074
theorem signs5074 : ∀ j, Signs p5074 (bank5074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5075 := params 18
abbrev ray5075 := rays 18
def bank5075 : Fin 2 → Cell := twoBank p5075 ray5075
theorem signs5075 : ∀ j, Signs p5075 (bank5075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5076 := params 19
abbrev ray5076 := rays 19
def bank5076 : Fin 2 → Cell := twoBank p5076 ray5076
theorem signs5076 : ∀ j, Signs p5076 (bank5076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5077 := params 20
abbrev ray5077 := rays 20
def bank5077 : Fin 2 → Cell := twoBank p5077 ray5077
theorem signs5077 : ∀ j, Signs p5077 (bank5077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5078 := params 21
abbrev ray5078 := rays 21
def bank5078 : Fin 2 → Cell := twoBank p5078 ray5078
theorem signs5078 : ∀ j, Signs p5078 (bank5078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5079 := params 22
abbrev ray5079 := rays 22
def bank5079 : Fin 2 → Cell := twoBank p5079 ray5079
theorem signs5079 : ∀ j, Signs p5079 (bank5079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5080 := params 23
abbrev ray5080 := rays 23
def bank5080 : Fin 2 → Cell := twoBank p5080 ray5080
theorem signs5080 : ∀ j, Signs p5080 (bank5080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5081 := params 24
abbrev ray5081 := rays 24
def bank5081 : Fin 2 → Cell := twoBank p5081 ray5081
theorem signs5081 : ∀ j, Signs p5081 (bank5081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5082 := params 25
abbrev ray5082 := rays 25
def bank5082 : Fin 2 → Cell := twoBank p5082 ray5082
theorem signs5082 : ∀ j, Signs p5082 (bank5082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5083 := params 26
abbrev ray5083 := rays 26
def bank5083 : Fin 2 → Cell := twoBank p5083 ray5083
theorem signs5083 : ∀ j, Signs p5083 (bank5083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5084 := params 27
abbrev ray5084 := rays 27
def bank5084 : Fin 2 → Cell := twoBank p5084 ray5084
theorem signs5084 : ∀ j, Signs p5084 (bank5084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5085 := params 28
abbrev ray5085 := rays 28
def bank5085 : Fin 2 → Cell := twoBank p5085 ray5085
theorem signs5085 : ∀ j, Signs p5085 (bank5085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5086 := params 29
abbrev ray5086 := rays 29
def bank5086 : Fin 2 → Cell := twoBank p5086 ray5086
theorem signs5086 : ∀ j, Signs p5086 (bank5086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5087 := params 30
abbrev ray5087 := rays 30
def bank5087 : Fin 2 → Cell := twoBank p5087 ray5087
theorem signs5087 : ∀ j, Signs p5087 (bank5087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5088 := params 31
abbrev ray5088 := rays 31
def bank5088 : Fin 2 → Cell := twoBank p5088 ray5088
theorem signs5088 : ∀ j, Signs p5088 (bank5088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05057_05088
