/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12065_12096
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96670476891154,96670069365526,96669661820570,96669254256287,96668846672677,96668439069741,96668031447479,96667623805892,96667216144980,96666808464744,96666400765183,96665993046299,96665585308092,96665177550562,96664769773709,96664361977534,96663954162038,96663546327221,96663138473083,96662730599625,96662322706847,96661914794749,96661506863333,96661098912598,96660690942545,96660282953174,96659874944486,96659466916481,96659058869160,96658650802523,96658242716570,96657834611302,96657426486719]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12064+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12065 := params 0
abbrev ray12065 := rays 0
def bank12065 : Fin 2 → Cell := twoBank p12065 ray12065
theorem signs12065 : ∀ j, Signs p12065 (bank12065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12066 := params 1
abbrev ray12066 := rays 1
def bank12066 : Fin 2 → Cell := twoBank p12066 ray12066
theorem signs12066 : ∀ j, Signs p12066 (bank12066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12067 := params 2
abbrev ray12067 := rays 2
def bank12067 : Fin 2 → Cell := twoBank p12067 ray12067
theorem signs12067 : ∀ j, Signs p12067 (bank12067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12068 := params 3
abbrev ray12068 := rays 3
def bank12068 : Fin 2 → Cell := twoBank p12068 ray12068
theorem signs12068 : ∀ j, Signs p12068 (bank12068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12069 := params 4
abbrev ray12069 := rays 4
def bank12069 : Fin 2 → Cell := twoBank p12069 ray12069
theorem signs12069 : ∀ j, Signs p12069 (bank12069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12070 := params 5
abbrev ray12070 := rays 5
def bank12070 : Fin 2 → Cell := twoBank p12070 ray12070
theorem signs12070 : ∀ j, Signs p12070 (bank12070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12071 := params 6
abbrev ray12071 := rays 6
def bank12071 : Fin 2 → Cell := twoBank p12071 ray12071
theorem signs12071 : ∀ j, Signs p12071 (bank12071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12072 := params 7
abbrev ray12072 := rays 7
def bank12072 : Fin 2 → Cell := twoBank p12072 ray12072
theorem signs12072 : ∀ j, Signs p12072 (bank12072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12073 := params 8
abbrev ray12073 := rays 8
def bank12073 : Fin 2 → Cell := twoBank p12073 ray12073
theorem signs12073 : ∀ j, Signs p12073 (bank12073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12074 := params 9
abbrev ray12074 := rays 9
def bank12074 : Fin 2 → Cell := twoBank p12074 ray12074
theorem signs12074 : ∀ j, Signs p12074 (bank12074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12075 := params 10
abbrev ray12075 := rays 10
def bank12075 : Fin 2 → Cell := twoBank p12075 ray12075
theorem signs12075 : ∀ j, Signs p12075 (bank12075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12076 := params 11
abbrev ray12076 := rays 11
def bank12076 : Fin 2 → Cell := twoBank p12076 ray12076
theorem signs12076 : ∀ j, Signs p12076 (bank12076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12077 := params 12
abbrev ray12077 := rays 12
def bank12077 : Fin 2 → Cell := twoBank p12077 ray12077
theorem signs12077 : ∀ j, Signs p12077 (bank12077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12078 := params 13
abbrev ray12078 := rays 13
def bank12078 : Fin 2 → Cell := twoBank p12078 ray12078
theorem signs12078 : ∀ j, Signs p12078 (bank12078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12079 := params 14
abbrev ray12079 := rays 14
def bank12079 : Fin 2 → Cell := twoBank p12079 ray12079
theorem signs12079 : ∀ j, Signs p12079 (bank12079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12080 := params 15
abbrev ray12080 := rays 15
def bank12080 : Fin 2 → Cell := twoBank p12080 ray12080
theorem signs12080 : ∀ j, Signs p12080 (bank12080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12081 := params 16
abbrev ray12081 := rays 16
def bank12081 : Fin 2 → Cell := twoBank p12081 ray12081
theorem signs12081 : ∀ j, Signs p12081 (bank12081 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12082 := params 17
abbrev ray12082 := rays 17
def bank12082 : Fin 2 → Cell := twoBank p12082 ray12082
theorem signs12082 : ∀ j, Signs p12082 (bank12082 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12083 := params 18
abbrev ray12083 := rays 18
def bank12083 : Fin 2 → Cell := twoBank p12083 ray12083
theorem signs12083 : ∀ j, Signs p12083 (bank12083 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12084 := params 19
abbrev ray12084 := rays 19
def bank12084 : Fin 2 → Cell := twoBank p12084 ray12084
theorem signs12084 : ∀ j, Signs p12084 (bank12084 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12085 := params 20
abbrev ray12085 := rays 20
def bank12085 : Fin 2 → Cell := twoBank p12085 ray12085
theorem signs12085 : ∀ j, Signs p12085 (bank12085 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12086 := params 21
abbrev ray12086 := rays 21
def bank12086 : Fin 2 → Cell := twoBank p12086 ray12086
theorem signs12086 : ∀ j, Signs p12086 (bank12086 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12087 := params 22
abbrev ray12087 := rays 22
def bank12087 : Fin 2 → Cell := twoBank p12087 ray12087
theorem signs12087 : ∀ j, Signs p12087 (bank12087 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12088 := params 23
abbrev ray12088 := rays 23
def bank12088 : Fin 2 → Cell := twoBank p12088 ray12088
theorem signs12088 : ∀ j, Signs p12088 (bank12088 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12089 := params 24
abbrev ray12089 := rays 24
def bank12089 : Fin 2 → Cell := twoBank p12089 ray12089
theorem signs12089 : ∀ j, Signs p12089 (bank12089 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12090 := params 25
abbrev ray12090 := rays 25
def bank12090 : Fin 2 → Cell := twoBank p12090 ray12090
theorem signs12090 : ∀ j, Signs p12090 (bank12090 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12091 := params 26
abbrev ray12091 := rays 26
def bank12091 : Fin 2 → Cell := twoBank p12091 ray12091
theorem signs12091 : ∀ j, Signs p12091 (bank12091 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12092 := params 27
abbrev ray12092 := rays 27
def bank12092 : Fin 2 → Cell := twoBank p12092 ray12092
theorem signs12092 : ∀ j, Signs p12092 (bank12092 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12093 := params 28
abbrev ray12093 := rays 28
def bank12093 : Fin 2 → Cell := twoBank p12093 ray12093
theorem signs12093 : ∀ j, Signs p12093 (bank12093 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12094 := params 29
abbrev ray12094 := rays 29
def bank12094 : Fin 2 → Cell := twoBank p12094 ray12094
theorem signs12094 : ∀ j, Signs p12094 (bank12094 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12095 := params 30
abbrev ray12095 := rays 30
def bank12095 : Fin 2 → Cell := twoBank p12095 ray12095
theorem signs12095 : ∀ j, Signs p12095 (bank12095 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12096 := params 31
abbrev ray12096 := rays 31
def bank12096 : Fin 2 → Cell := twoBank p12096 ray12096
theorem signs12096 : ∀ j, Signs p12096 (bank12096 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12065_12096
