/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11137_11168
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97040270478842,97039881081238,97039491663885,97039102226783,97038712769932,97038323293333,97037933796987,97037544280894,97037154745054,97036765189468,97036375614137,97035986019061,97035596404240,97035206769675,97034817115367,97034427441315,97034037747521,97033648033985,97033258300707,97032868547688,97032478774928,97032088982428,97031699170188,97031309338209,97030919486491,97030529615035,97030139723841,97029749812910,97029359882242,97028969931837,97028579961696,97028189971820,97027799962209]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11136+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11137 := params 0
abbrev ray11137 := rays 0
def bank11137 : Fin 2 → Cell := twoBank p11137 ray11137
theorem signs11137 : ∀ j, Signs p11137 (bank11137 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11138 := params 1
abbrev ray11138 := rays 1
def bank11138 : Fin 2 → Cell := twoBank p11138 ray11138
theorem signs11138 : ∀ j, Signs p11138 (bank11138 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11139 := params 2
abbrev ray11139 := rays 2
def bank11139 : Fin 2 → Cell := twoBank p11139 ray11139
theorem signs11139 : ∀ j, Signs p11139 (bank11139 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11140 := params 3
abbrev ray11140 := rays 3
def bank11140 : Fin 2 → Cell := twoBank p11140 ray11140
theorem signs11140 : ∀ j, Signs p11140 (bank11140 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11141 := params 4
abbrev ray11141 := rays 4
def bank11141 : Fin 2 → Cell := twoBank p11141 ray11141
theorem signs11141 : ∀ j, Signs p11141 (bank11141 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11142 := params 5
abbrev ray11142 := rays 5
def bank11142 : Fin 2 → Cell := twoBank p11142 ray11142
theorem signs11142 : ∀ j, Signs p11142 (bank11142 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11143 := params 6
abbrev ray11143 := rays 6
def bank11143 : Fin 2 → Cell := twoBank p11143 ray11143
theorem signs11143 : ∀ j, Signs p11143 (bank11143 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11144 := params 7
abbrev ray11144 := rays 7
def bank11144 : Fin 2 → Cell := twoBank p11144 ray11144
theorem signs11144 : ∀ j, Signs p11144 (bank11144 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11145 := params 8
abbrev ray11145 := rays 8
def bank11145 : Fin 2 → Cell := twoBank p11145 ray11145
theorem signs11145 : ∀ j, Signs p11145 (bank11145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11146 := params 9
abbrev ray11146 := rays 9
def bank11146 : Fin 2 → Cell := twoBank p11146 ray11146
theorem signs11146 : ∀ j, Signs p11146 (bank11146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11147 := params 10
abbrev ray11147 := rays 10
def bank11147 : Fin 2 → Cell := twoBank p11147 ray11147
theorem signs11147 : ∀ j, Signs p11147 (bank11147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11148 := params 11
abbrev ray11148 := rays 11
def bank11148 : Fin 2 → Cell := twoBank p11148 ray11148
theorem signs11148 : ∀ j, Signs p11148 (bank11148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11149 := params 12
abbrev ray11149 := rays 12
def bank11149 : Fin 2 → Cell := twoBank p11149 ray11149
theorem signs11149 : ∀ j, Signs p11149 (bank11149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11150 := params 13
abbrev ray11150 := rays 13
def bank11150 : Fin 2 → Cell := twoBank p11150 ray11150
theorem signs11150 : ∀ j, Signs p11150 (bank11150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11151 := params 14
abbrev ray11151 := rays 14
def bank11151 : Fin 2 → Cell := twoBank p11151 ray11151
theorem signs11151 : ∀ j, Signs p11151 (bank11151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11152 := params 15
abbrev ray11152 := rays 15
def bank11152 : Fin 2 → Cell := twoBank p11152 ray11152
theorem signs11152 : ∀ j, Signs p11152 (bank11152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11153 := params 16
abbrev ray11153 := rays 16
def bank11153 : Fin 2 → Cell := twoBank p11153 ray11153
theorem signs11153 : ∀ j, Signs p11153 (bank11153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11154 := params 17
abbrev ray11154 := rays 17
def bank11154 : Fin 2 → Cell := twoBank p11154 ray11154
theorem signs11154 : ∀ j, Signs p11154 (bank11154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11155 := params 18
abbrev ray11155 := rays 18
def bank11155 : Fin 2 → Cell := twoBank p11155 ray11155
theorem signs11155 : ∀ j, Signs p11155 (bank11155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11156 := params 19
abbrev ray11156 := rays 19
def bank11156 : Fin 2 → Cell := twoBank p11156 ray11156
theorem signs11156 : ∀ j, Signs p11156 (bank11156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11157 := params 20
abbrev ray11157 := rays 20
def bank11157 : Fin 2 → Cell := twoBank p11157 ray11157
theorem signs11157 : ∀ j, Signs p11157 (bank11157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11158 := params 21
abbrev ray11158 := rays 21
def bank11158 : Fin 2 → Cell := twoBank p11158 ray11158
theorem signs11158 : ∀ j, Signs p11158 (bank11158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11159 := params 22
abbrev ray11159 := rays 22
def bank11159 : Fin 2 → Cell := twoBank p11159 ray11159
theorem signs11159 : ∀ j, Signs p11159 (bank11159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11160 := params 23
abbrev ray11160 := rays 23
def bank11160 : Fin 2 → Cell := twoBank p11160 ray11160
theorem signs11160 : ∀ j, Signs p11160 (bank11160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11161 := params 24
abbrev ray11161 := rays 24
def bank11161 : Fin 2 → Cell := twoBank p11161 ray11161
theorem signs11161 : ∀ j, Signs p11161 (bank11161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11162 := params 25
abbrev ray11162 := rays 25
def bank11162 : Fin 2 → Cell := twoBank p11162 ray11162
theorem signs11162 : ∀ j, Signs p11162 (bank11162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11163 := params 26
abbrev ray11163 := rays 26
def bank11163 : Fin 2 → Cell := twoBank p11163 ray11163
theorem signs11163 : ∀ j, Signs p11163 (bank11163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11164 := params 27
abbrev ray11164 := rays 27
def bank11164 : Fin 2 → Cell := twoBank p11164 ray11164
theorem signs11164 : ∀ j, Signs p11164 (bank11164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11165 := params 28
abbrev ray11165 := rays 28
def bank11165 : Fin 2 → Cell := twoBank p11165 ray11165
theorem signs11165 : ∀ j, Signs p11165 (bank11165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11166 := params 29
abbrev ray11166 := rays 29
def bank11166 : Fin 2 → Cell := twoBank p11166 ray11166
theorem signs11166 : ∀ j, Signs p11166 (bank11166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11167 := params 30
abbrev ray11167 := rays 30
def bank11167 : Fin 2 → Cell := twoBank p11167 ray11167
theorem signs11167 : ∀ j, Signs p11167 (bank11167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11168 := params 31
abbrev ray11168 := rays 31
def bank11168 : Fin 2 → Cell := twoBank p11168 ray11168
theorem signs11168 : ∀ j, Signs p11168 (bank11168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11137_11168
