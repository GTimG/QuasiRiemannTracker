/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13089_13120
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96243234512828,96242808166489,96242381803736,96241955424570,96241529028990,96241102616997,96240676188591,96240249743772,96239823282540,96239396804896,96238970310840,96238543800372,96238117273493,96237690730202,96237264170500,96236837594388,96236411001865,96235984392932,96235557767589,96235131125836,96234704467673,96234277793101,96233851102120,96233424394730,96232997670932,96232570930726,96232144174112,96231717401090,96231290611661,96230863805824,96230436983580,96230010144930,96229583289873]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13088+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13089 := params 0
abbrev ray13089 := rays 0
def bank13089 : Fin 1 → Cell := oneBank p13089 ray13089
theorem signs13089 : ∀ j, Signs p13089 (bank13089 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13090 := params 1
abbrev ray13090 := rays 1
def bank13090 : Fin 1 → Cell := oneBank p13090 ray13090
theorem signs13090 : ∀ j, Signs p13090 (bank13090 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13091 := params 2
abbrev ray13091 := rays 2
def bank13091 : Fin 1 → Cell := oneBank p13091 ray13091
theorem signs13091 : ∀ j, Signs p13091 (bank13091 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13092 := params 3
abbrev ray13092 := rays 3
def bank13092 : Fin 1 → Cell := oneBank p13092 ray13092
theorem signs13092 : ∀ j, Signs p13092 (bank13092 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13093 := params 4
abbrev ray13093 := rays 4
def bank13093 : Fin 1 → Cell := oneBank p13093 ray13093
theorem signs13093 : ∀ j, Signs p13093 (bank13093 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13094 := params 5
abbrev ray13094 := rays 5
def bank13094 : Fin 1 → Cell := oneBank p13094 ray13094
theorem signs13094 : ∀ j, Signs p13094 (bank13094 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13095 := params 6
abbrev ray13095 := rays 6
def bank13095 : Fin 1 → Cell := oneBank p13095 ray13095
theorem signs13095 : ∀ j, Signs p13095 (bank13095 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13096 := params 7
abbrev ray13096 := rays 7
def bank13096 : Fin 1 → Cell := oneBank p13096 ray13096
theorem signs13096 : ∀ j, Signs p13096 (bank13096 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13097 := params 8
abbrev ray13097 := rays 8
def bank13097 : Fin 1 → Cell := oneBank p13097 ray13097
theorem signs13097 : ∀ j, Signs p13097 (bank13097 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13098 := params 9
abbrev ray13098 := rays 9
def bank13098 : Fin 1 → Cell := oneBank p13098 ray13098
theorem signs13098 : ∀ j, Signs p13098 (bank13098 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13099 := params 10
abbrev ray13099 := rays 10
def bank13099 : Fin 1 → Cell := oneBank p13099 ray13099
theorem signs13099 : ∀ j, Signs p13099 (bank13099 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13100 := params 11
abbrev ray13100 := rays 11
def bank13100 : Fin 1 → Cell := oneBank p13100 ray13100
theorem signs13100 : ∀ j, Signs p13100 (bank13100 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13101 := params 12
abbrev ray13101 := rays 12
def bank13101 : Fin 1 → Cell := oneBank p13101 ray13101
theorem signs13101 : ∀ j, Signs p13101 (bank13101 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13102 := params 13
abbrev ray13102 := rays 13
def bank13102 : Fin 1 → Cell := oneBank p13102 ray13102
theorem signs13102 : ∀ j, Signs p13102 (bank13102 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13103 := params 14
abbrev ray13103 := rays 14
def bank13103 : Fin 1 → Cell := oneBank p13103 ray13103
theorem signs13103 : ∀ j, Signs p13103 (bank13103 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13104 := params 15
abbrev ray13104 := rays 15
def bank13104 : Fin 1 → Cell := oneBank p13104 ray13104
theorem signs13104 : ∀ j, Signs p13104 (bank13104 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13105 := params 16
abbrev ray13105 := rays 16
def bank13105 : Fin 1 → Cell := oneBank p13105 ray13105
theorem signs13105 : ∀ j, Signs p13105 (bank13105 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13106 := params 17
abbrev ray13106 := rays 17
def bank13106 : Fin 1 → Cell := oneBank p13106 ray13106
theorem signs13106 : ∀ j, Signs p13106 (bank13106 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13107 := params 18
abbrev ray13107 := rays 18
def bank13107 : Fin 1 → Cell := oneBank p13107 ray13107
theorem signs13107 : ∀ j, Signs p13107 (bank13107 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13108 := params 19
abbrev ray13108 := rays 19
def bank13108 : Fin 1 → Cell := oneBank p13108 ray13108
theorem signs13108 : ∀ j, Signs p13108 (bank13108 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13109 := params 20
abbrev ray13109 := rays 20
def bank13109 : Fin 1 → Cell := oneBank p13109 ray13109
theorem signs13109 : ∀ j, Signs p13109 (bank13109 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13110 := params 21
abbrev ray13110 := rays 21
def bank13110 : Fin 1 → Cell := oneBank p13110 ray13110
theorem signs13110 : ∀ j, Signs p13110 (bank13110 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13111 := params 22
abbrev ray13111 := rays 22
def bank13111 : Fin 1 → Cell := oneBank p13111 ray13111
theorem signs13111 : ∀ j, Signs p13111 (bank13111 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13112 := params 23
abbrev ray13112 := rays 23
def bank13112 : Fin 1 → Cell := oneBank p13112 ray13112
theorem signs13112 : ∀ j, Signs p13112 (bank13112 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13113 := params 24
abbrev ray13113 := rays 24
def bank13113 : Fin 1 → Cell := oneBank p13113 ray13113
theorem signs13113 : ∀ j, Signs p13113 (bank13113 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13114 := params 25
abbrev ray13114 := rays 25
def bank13114 : Fin 1 → Cell := oneBank p13114 ray13114
theorem signs13114 : ∀ j, Signs p13114 (bank13114 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13115 := params 26
abbrev ray13115 := rays 26
def bank13115 : Fin 1 → Cell := oneBank p13115 ray13115
theorem signs13115 : ∀ j, Signs p13115 (bank13115 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13116 := params 27
abbrev ray13116 := rays 27
def bank13116 : Fin 1 → Cell := oneBank p13116 ray13116
theorem signs13116 : ∀ j, Signs p13116 (bank13116 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13117 := params 28
abbrev ray13117 := rays 28
def bank13117 : Fin 1 → Cell := oneBank p13117 ray13117
theorem signs13117 : ∀ j, Signs p13117 (bank13117 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13118 := params 29
abbrev ray13118 := rays 29
def bank13118 : Fin 1 → Cell := oneBank p13118 ray13118
theorem signs13118 : ∀ j, Signs p13118 (bank13118 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13119 := params 30
abbrev ray13119 := rays 30
def bank13119 : Fin 1 → Cell := oneBank p13119 ray13119
theorem signs13119 : ∀ j, Signs p13119 (bank13119 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13120 := params 31
abbrev ray13120 := rays 31
def bank13120 : Fin 1 → Cell := oneBank p13120 ray13120
theorem signs13120 : ∀ j, Signs p13120 (bank13120 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13089_13120
