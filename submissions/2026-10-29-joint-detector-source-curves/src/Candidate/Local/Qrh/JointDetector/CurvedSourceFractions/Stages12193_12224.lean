/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12193_12224
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96618156662072,96617746665979,96617336650613,96616926615974,96616516562063,96616106488880,96615696396425,96615286284699,96614876153702,96614466003435,96614055833898,96613645645092,96613235437017,96612825209673,96612414963061,96612004697181,96611594412034,96611184107620,96610773783940,96610363440993,96609953078781,96609542697304,96609132296562,96608721876555,96608311437284,96607900978750,96607490500953,96607080003893,96606669487571,96606258951987,96605848397141,96605437823034,96605027229667]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12192+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12193 := params 0
abbrev ray12193 := rays 0
def bank12193 : Fin 2 → Cell := twoBank p12193 ray12193
theorem signs12193 : ∀ j, Signs p12193 (bank12193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12194 := params 1
abbrev ray12194 := rays 1
def bank12194 : Fin 2 → Cell := twoBank p12194 ray12194
theorem signs12194 : ∀ j, Signs p12194 (bank12194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12195 := params 2
abbrev ray12195 := rays 2
def bank12195 : Fin 2 → Cell := twoBank p12195 ray12195
theorem signs12195 : ∀ j, Signs p12195 (bank12195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12196 := params 3
abbrev ray12196 := rays 3
def bank12196 : Fin 2 → Cell := twoBank p12196 ray12196
theorem signs12196 : ∀ j, Signs p12196 (bank12196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12197 := params 4
abbrev ray12197 := rays 4
def bank12197 : Fin 2 → Cell := twoBank p12197 ray12197
theorem signs12197 : ∀ j, Signs p12197 (bank12197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12198 := params 5
abbrev ray12198 := rays 5
def bank12198 : Fin 2 → Cell := twoBank p12198 ray12198
theorem signs12198 : ∀ j, Signs p12198 (bank12198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12199 := params 6
abbrev ray12199 := rays 6
def bank12199 : Fin 2 → Cell := twoBank p12199 ray12199
theorem signs12199 : ∀ j, Signs p12199 (bank12199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12200 := params 7
abbrev ray12200 := rays 7
def bank12200 : Fin 2 → Cell := twoBank p12200 ray12200
theorem signs12200 : ∀ j, Signs p12200 (bank12200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12201 := params 8
abbrev ray12201 := rays 8
def bank12201 : Fin 2 → Cell := twoBank p12201 ray12201
theorem signs12201 : ∀ j, Signs p12201 (bank12201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12202 := params 9
abbrev ray12202 := rays 9
def bank12202 : Fin 2 → Cell := twoBank p12202 ray12202
theorem signs12202 : ∀ j, Signs p12202 (bank12202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12203 := params 10
abbrev ray12203 := rays 10
def bank12203 : Fin 2 → Cell := twoBank p12203 ray12203
theorem signs12203 : ∀ j, Signs p12203 (bank12203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12204 := params 11
abbrev ray12204 := rays 11
def bank12204 : Fin 2 → Cell := twoBank p12204 ray12204
theorem signs12204 : ∀ j, Signs p12204 (bank12204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12205 := params 12
abbrev ray12205 := rays 12
def bank12205 : Fin 2 → Cell := twoBank p12205 ray12205
theorem signs12205 : ∀ j, Signs p12205 (bank12205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12206 := params 13
abbrev ray12206 := rays 13
def bank12206 : Fin 2 → Cell := twoBank p12206 ray12206
theorem signs12206 : ∀ j, Signs p12206 (bank12206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12207 := params 14
abbrev ray12207 := rays 14
def bank12207 : Fin 2 → Cell := twoBank p12207 ray12207
theorem signs12207 : ∀ j, Signs p12207 (bank12207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12208 := params 15
abbrev ray12208 := rays 15
def bank12208 : Fin 2 → Cell := twoBank p12208 ray12208
theorem signs12208 : ∀ j, Signs p12208 (bank12208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12209 := params 16
abbrev ray12209 := rays 16
def bank12209 : Fin 2 → Cell := twoBank p12209 ray12209
theorem signs12209 : ∀ j, Signs p12209 (bank12209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12210 := params 17
abbrev ray12210 := rays 17
def bank12210 : Fin 2 → Cell := twoBank p12210 ray12210
theorem signs12210 : ∀ j, Signs p12210 (bank12210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12211 := params 18
abbrev ray12211 := rays 18
def bank12211 : Fin 2 → Cell := twoBank p12211 ray12211
theorem signs12211 : ∀ j, Signs p12211 (bank12211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12212 := params 19
abbrev ray12212 := rays 19
def bank12212 : Fin 2 → Cell := twoBank p12212 ray12212
theorem signs12212 : ∀ j, Signs p12212 (bank12212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12213 := params 20
abbrev ray12213 := rays 20
def bank12213 : Fin 2 → Cell := twoBank p12213 ray12213
theorem signs12213 : ∀ j, Signs p12213 (bank12213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12214 := params 21
abbrev ray12214 := rays 21
def bank12214 : Fin 2 → Cell := twoBank p12214 ray12214
theorem signs12214 : ∀ j, Signs p12214 (bank12214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12215 := params 22
abbrev ray12215 := rays 22
def bank12215 : Fin 2 → Cell := twoBank p12215 ray12215
theorem signs12215 : ∀ j, Signs p12215 (bank12215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12216 := params 23
abbrev ray12216 := rays 23
def bank12216 : Fin 2 → Cell := twoBank p12216 ray12216
theorem signs12216 : ∀ j, Signs p12216 (bank12216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12217 := params 24
abbrev ray12217 := rays 24
def bank12217 : Fin 2 → Cell := twoBank p12217 ray12217
theorem signs12217 : ∀ j, Signs p12217 (bank12217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12218 := params 25
abbrev ray12218 := rays 25
def bank12218 : Fin 2 → Cell := twoBank p12218 ray12218
theorem signs12218 : ∀ j, Signs p12218 (bank12218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12219 := params 26
abbrev ray12219 := rays 26
def bank12219 : Fin 2 → Cell := twoBank p12219 ray12219
theorem signs12219 : ∀ j, Signs p12219 (bank12219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12220 := params 27
abbrev ray12220 := rays 27
def bank12220 : Fin 2 → Cell := twoBank p12220 ray12220
theorem signs12220 : ∀ j, Signs p12220 (bank12220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12221 := params 28
abbrev ray12221 := rays 28
def bank12221 : Fin 2 → Cell := twoBank p12221 ray12221
theorem signs12221 : ∀ j, Signs p12221 (bank12221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12222 := params 29
abbrev ray12222 := rays 29
def bank12222 : Fin 2 → Cell := twoBank p12222 ray12222
theorem signs12222 : ∀ j, Signs p12222 (bank12222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12223 := params 30
abbrev ray12223 := rays 30
def bank12223 : Fin 2 → Cell := twoBank p12223 ray12223
theorem signs12223 : ∀ j, Signs p12223 (bank12223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12224 := params 31
abbrev ray12224 := rays 31
def bank12224 : Fin 2 → Cell := twoBank p12224 ray12224
theorem signs12224 : ∀ j, Signs p12224 (bank12224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12193_12224
