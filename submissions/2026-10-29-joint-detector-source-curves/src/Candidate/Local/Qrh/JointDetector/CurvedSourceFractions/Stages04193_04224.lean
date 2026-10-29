/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04193_04224
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99234456671469,99234220031703,99233983366989,99233746677328,99233509962721,99233273223169,99233036458673,99232799669235,99232562854856,99232326015536,99232089151277,99231852262080,99231615347946,99231378408876,99231141444871,99230904455932,99230667442061,99230430403258,99230193339525,99229956250862,99229719137271,99229481998753,99229244835309,99229007646940,99228770433647,99228533195431,99228295932294,99228058644236,99227821331258,99227583993362,99227346630549,99227109242820,99226871830175]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4192+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4193 := params 0
abbrev ray4193 := rays 0
def bank4193 : Fin 2 → Cell := twoBank p4193 ray4193
theorem signs4193 : ∀ j, Signs p4193 (bank4193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4194 := params 1
abbrev ray4194 := rays 1
def bank4194 : Fin 2 → Cell := twoBank p4194 ray4194
theorem signs4194 : ∀ j, Signs p4194 (bank4194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4195 := params 2
abbrev ray4195 := rays 2
def bank4195 : Fin 2 → Cell := twoBank p4195 ray4195
theorem signs4195 : ∀ j, Signs p4195 (bank4195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4196 := params 3
abbrev ray4196 := rays 3
def bank4196 : Fin 2 → Cell := twoBank p4196 ray4196
theorem signs4196 : ∀ j, Signs p4196 (bank4196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4197 := params 4
abbrev ray4197 := rays 4
def bank4197 : Fin 2 → Cell := twoBank p4197 ray4197
theorem signs4197 : ∀ j, Signs p4197 (bank4197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4198 := params 5
abbrev ray4198 := rays 5
def bank4198 : Fin 2 → Cell := twoBank p4198 ray4198
theorem signs4198 : ∀ j, Signs p4198 (bank4198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4199 := params 6
abbrev ray4199 := rays 6
def bank4199 : Fin 2 → Cell := twoBank p4199 ray4199
theorem signs4199 : ∀ j, Signs p4199 (bank4199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4200 := params 7
abbrev ray4200 := rays 7
def bank4200 : Fin 2 → Cell := twoBank p4200 ray4200
theorem signs4200 : ∀ j, Signs p4200 (bank4200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4201 := params 8
abbrev ray4201 := rays 8
def bank4201 : Fin 2 → Cell := twoBank p4201 ray4201
theorem signs4201 : ∀ j, Signs p4201 (bank4201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4202 := params 9
abbrev ray4202 := rays 9
def bank4202 : Fin 2 → Cell := twoBank p4202 ray4202
theorem signs4202 : ∀ j, Signs p4202 (bank4202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4203 := params 10
abbrev ray4203 := rays 10
def bank4203 : Fin 2 → Cell := twoBank p4203 ray4203
theorem signs4203 : ∀ j, Signs p4203 (bank4203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4204 := params 11
abbrev ray4204 := rays 11
def bank4204 : Fin 2 → Cell := twoBank p4204 ray4204
theorem signs4204 : ∀ j, Signs p4204 (bank4204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4205 := params 12
abbrev ray4205 := rays 12
def bank4205 : Fin 2 → Cell := twoBank p4205 ray4205
theorem signs4205 : ∀ j, Signs p4205 (bank4205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4206 := params 13
abbrev ray4206 := rays 13
def bank4206 : Fin 2 → Cell := twoBank p4206 ray4206
theorem signs4206 : ∀ j, Signs p4206 (bank4206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4207 := params 14
abbrev ray4207 := rays 14
def bank4207 : Fin 2 → Cell := twoBank p4207 ray4207
theorem signs4207 : ∀ j, Signs p4207 (bank4207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4208 := params 15
abbrev ray4208 := rays 15
def bank4208 : Fin 2 → Cell := twoBank p4208 ray4208
theorem signs4208 : ∀ j, Signs p4208 (bank4208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4209 := params 16
abbrev ray4209 := rays 16
def bank4209 : Fin 2 → Cell := twoBank p4209 ray4209
theorem signs4209 : ∀ j, Signs p4209 (bank4209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4210 := params 17
abbrev ray4210 := rays 17
def bank4210 : Fin 2 → Cell := twoBank p4210 ray4210
theorem signs4210 : ∀ j, Signs p4210 (bank4210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4211 := params 18
abbrev ray4211 := rays 18
def bank4211 : Fin 2 → Cell := twoBank p4211 ray4211
theorem signs4211 : ∀ j, Signs p4211 (bank4211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4212 := params 19
abbrev ray4212 := rays 19
def bank4212 : Fin 2 → Cell := twoBank p4212 ray4212
theorem signs4212 : ∀ j, Signs p4212 (bank4212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4213 := params 20
abbrev ray4213 := rays 20
def bank4213 : Fin 2 → Cell := twoBank p4213 ray4213
theorem signs4213 : ∀ j, Signs p4213 (bank4213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4214 := params 21
abbrev ray4214 := rays 21
def bank4214 : Fin 2 → Cell := twoBank p4214 ray4214
theorem signs4214 : ∀ j, Signs p4214 (bank4214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4215 := params 22
abbrev ray4215 := rays 22
def bank4215 : Fin 2 → Cell := twoBank p4215 ray4215
theorem signs4215 : ∀ j, Signs p4215 (bank4215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4216 := params 23
abbrev ray4216 := rays 23
def bank4216 : Fin 2 → Cell := twoBank p4216 ray4216
theorem signs4216 : ∀ j, Signs p4216 (bank4216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4217 := params 24
abbrev ray4217 := rays 24
def bank4217 : Fin 2 → Cell := twoBank p4217 ray4217
theorem signs4217 : ∀ j, Signs p4217 (bank4217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4218 := params 25
abbrev ray4218 := rays 25
def bank4218 : Fin 2 → Cell := twoBank p4218 ray4218
theorem signs4218 : ∀ j, Signs p4218 (bank4218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4219 := params 26
abbrev ray4219 := rays 26
def bank4219 : Fin 2 → Cell := twoBank p4219 ray4219
theorem signs4219 : ∀ j, Signs p4219 (bank4219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4220 := params 27
abbrev ray4220 := rays 27
def bank4220 : Fin 2 → Cell := twoBank p4220 ray4220
theorem signs4220 : ∀ j, Signs p4220 (bank4220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4221 := params 28
abbrev ray4221 := rays 28
def bank4221 : Fin 2 → Cell := twoBank p4221 ray4221
theorem signs4221 : ∀ j, Signs p4221 (bank4221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4222 := params 29
abbrev ray4222 := rays 29
def bank4222 : Fin 2 → Cell := twoBank p4222 ray4222
theorem signs4222 : ∀ j, Signs p4222 (bank4222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4223 := params 30
abbrev ray4223 := rays 30
def bank4223 : Fin 2 → Cell := twoBank p4223 ray4223
theorem signs4223 : ∀ j, Signs p4223 (bank4223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4224 := params 31
abbrev ray4224 := rays 31
def bank4224 : Fin 2 → Cell := twoBank p4224 ray4224
theorem signs4224 : ∀ j, Signs p4224 (bank4224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04193_04224
