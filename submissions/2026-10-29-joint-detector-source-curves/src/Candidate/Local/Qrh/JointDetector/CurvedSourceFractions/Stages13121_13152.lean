/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13121_13152
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96229583289873,96229156418410,96228729530541,96228302626266,96227875705586,96227448768501,96227021815011,96226594845116,96226167858816,96225740856112,96225313837004,96224886801493,96224459749578,96224032681260,96223605596539,96223178495415,96222751377889,96222324243961,96221897093631,96221469926899,96221042743766,96220615544231,96220188328295,96219761095959,96219333847222,96218906582085,96218479300548,96218052002611,96217624688275,96217197357540,96216770010406,96216342646873,96215915266942]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13120+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13121 := params 0
abbrev ray13121 := rays 0
def bank13121 : Fin 1 → Cell := oneBank p13121 ray13121
theorem signs13121 : ∀ j, Signs p13121 (bank13121 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13122 := params 1
abbrev ray13122 := rays 1
def bank13122 : Fin 1 → Cell := oneBank p13122 ray13122
theorem signs13122 : ∀ j, Signs p13122 (bank13122 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13123 := params 2
abbrev ray13123 := rays 2
def bank13123 : Fin 1 → Cell := oneBank p13123 ray13123
theorem signs13123 : ∀ j, Signs p13123 (bank13123 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13124 := params 3
abbrev ray13124 := rays 3
def bank13124 : Fin 1 → Cell := oneBank p13124 ray13124
theorem signs13124 : ∀ j, Signs p13124 (bank13124 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13125 := params 4
abbrev ray13125 := rays 4
def bank13125 : Fin 1 → Cell := oneBank p13125 ray13125
theorem signs13125 : ∀ j, Signs p13125 (bank13125 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13126 := params 5
abbrev ray13126 := rays 5
def bank13126 : Fin 1 → Cell := oneBank p13126 ray13126
theorem signs13126 : ∀ j, Signs p13126 (bank13126 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13127 := params 6
abbrev ray13127 := rays 6
def bank13127 : Fin 1 → Cell := oneBank p13127 ray13127
theorem signs13127 : ∀ j, Signs p13127 (bank13127 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13128 := params 7
abbrev ray13128 := rays 7
def bank13128 : Fin 1 → Cell := oneBank p13128 ray13128
theorem signs13128 : ∀ j, Signs p13128 (bank13128 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13129 := params 8
abbrev ray13129 := rays 8
def bank13129 : Fin 1 → Cell := oneBank p13129 ray13129
theorem signs13129 : ∀ j, Signs p13129 (bank13129 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13130 := params 9
abbrev ray13130 := rays 9
def bank13130 : Fin 1 → Cell := oneBank p13130 ray13130
theorem signs13130 : ∀ j, Signs p13130 (bank13130 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13131 := params 10
abbrev ray13131 := rays 10
def bank13131 : Fin 1 → Cell := oneBank p13131 ray13131
theorem signs13131 : ∀ j, Signs p13131 (bank13131 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13132 := params 11
abbrev ray13132 := rays 11
def bank13132 : Fin 1 → Cell := oneBank p13132 ray13132
theorem signs13132 : ∀ j, Signs p13132 (bank13132 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13133 := params 12
abbrev ray13133 := rays 12
def bank13133 : Fin 1 → Cell := oneBank p13133 ray13133
theorem signs13133 : ∀ j, Signs p13133 (bank13133 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13134 := params 13
abbrev ray13134 := rays 13
def bank13134 : Fin 1 → Cell := oneBank p13134 ray13134
theorem signs13134 : ∀ j, Signs p13134 (bank13134 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13135 := params 14
abbrev ray13135 := rays 14
def bank13135 : Fin 1 → Cell := oneBank p13135 ray13135
theorem signs13135 : ∀ j, Signs p13135 (bank13135 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13136 := params 15
abbrev ray13136 := rays 15
def bank13136 : Fin 1 → Cell := oneBank p13136 ray13136
theorem signs13136 : ∀ j, Signs p13136 (bank13136 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13137 := params 16
abbrev ray13137 := rays 16
def bank13137 : Fin 1 → Cell := oneBank p13137 ray13137
theorem signs13137 : ∀ j, Signs p13137 (bank13137 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13138 := params 17
abbrev ray13138 := rays 17
def bank13138 : Fin 1 → Cell := oneBank p13138 ray13138
theorem signs13138 : ∀ j, Signs p13138 (bank13138 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13139 := params 18
abbrev ray13139 := rays 18
def bank13139 : Fin 1 → Cell := oneBank p13139 ray13139
theorem signs13139 : ∀ j, Signs p13139 (bank13139 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13140 := params 19
abbrev ray13140 := rays 19
def bank13140 : Fin 1 → Cell := oneBank p13140 ray13140
theorem signs13140 : ∀ j, Signs p13140 (bank13140 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13141 := params 20
abbrev ray13141 := rays 20
def bank13141 : Fin 1 → Cell := oneBank p13141 ray13141
theorem signs13141 : ∀ j, Signs p13141 (bank13141 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13142 := params 21
abbrev ray13142 := rays 21
def bank13142 : Fin 1 → Cell := oneBank p13142 ray13142
theorem signs13142 : ∀ j, Signs p13142 (bank13142 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13143 := params 22
abbrev ray13143 := rays 22
def bank13143 : Fin 1 → Cell := oneBank p13143 ray13143
theorem signs13143 : ∀ j, Signs p13143 (bank13143 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13144 := params 23
abbrev ray13144 := rays 23
def bank13144 : Fin 1 → Cell := oneBank p13144 ray13144
theorem signs13144 : ∀ j, Signs p13144 (bank13144 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13145 := params 24
abbrev ray13145 := rays 24
def bank13145 : Fin 1 → Cell := oneBank p13145 ray13145
theorem signs13145 : ∀ j, Signs p13145 (bank13145 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13146 := params 25
abbrev ray13146 := rays 25
def bank13146 : Fin 1 → Cell := oneBank p13146 ray13146
theorem signs13146 : ∀ j, Signs p13146 (bank13146 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13147 := params 26
abbrev ray13147 := rays 26
def bank13147 : Fin 1 → Cell := oneBank p13147 ray13147
theorem signs13147 : ∀ j, Signs p13147 (bank13147 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13148 := params 27
abbrev ray13148 := rays 27
def bank13148 : Fin 1 → Cell := oneBank p13148 ray13148
theorem signs13148 : ∀ j, Signs p13148 (bank13148 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13149 := params 28
abbrev ray13149 := rays 28
def bank13149 : Fin 1 → Cell := oneBank p13149 ray13149
theorem signs13149 : ∀ j, Signs p13149 (bank13149 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13150 := params 29
abbrev ray13150 := rays 29
def bank13150 : Fin 1 → Cell := oneBank p13150 ray13150
theorem signs13150 : ∀ j, Signs p13150 (bank13150 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13151 := params 30
abbrev ray13151 := rays 30
def bank13151 : Fin 1 → Cell := oneBank p13151 ray13151
theorem signs13151 : ∀ j, Signs p13151 (bank13151 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13152 := params 31
abbrev ray13152 := rays 31
def bank13152 : Fin 1 → Cell := oneBank p13152 ray13152
theorem signs13152 : ∀ j, Signs p13152 (bank13152 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13121_13152
