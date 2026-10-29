/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15297_15328
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95262249249619,95261787145139,95261325024622,95260862888069,95260400735480,95259938566855,95259476382194,95259014181498,95258551964766,95258089731998,95257627483195,95257165218356,95256702937482,95256240640573,95255778327629,95255315998649,95254853653634,95254391292585,95253928915501,95253466522382,95253004113228,95252541688040,95252079246817,95251616789560,95251154316269,95250691826943,95250229321583,95249766800189,95249304262761,95248841709300,95248379139805,95247916554276,95247453952713]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15296+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15297 := params 0
abbrev ray15297 := rays 0
def bank15297 : Fin 1 → Cell := oneBank p15297 ray15297
theorem signs15297 : ∀ j, Signs p15297 (bank15297 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15298 := params 1
abbrev ray15298 := rays 1
def bank15298 : Fin 1 → Cell := oneBank p15298 ray15298
theorem signs15298 : ∀ j, Signs p15298 (bank15298 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15299 := params 2
abbrev ray15299 := rays 2
def bank15299 : Fin 1 → Cell := oneBank p15299 ray15299
theorem signs15299 : ∀ j, Signs p15299 (bank15299 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15300 := params 3
abbrev ray15300 := rays 3
def bank15300 : Fin 1 → Cell := oneBank p15300 ray15300
theorem signs15300 : ∀ j, Signs p15300 (bank15300 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15301 := params 4
abbrev ray15301 := rays 4
def bank15301 : Fin 1 → Cell := oneBank p15301 ray15301
theorem signs15301 : ∀ j, Signs p15301 (bank15301 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15302 := params 5
abbrev ray15302 := rays 5
def bank15302 : Fin 1 → Cell := oneBank p15302 ray15302
theorem signs15302 : ∀ j, Signs p15302 (bank15302 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15303 := params 6
abbrev ray15303 := rays 6
def bank15303 : Fin 1 → Cell := oneBank p15303 ray15303
theorem signs15303 : ∀ j, Signs p15303 (bank15303 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15304 := params 7
abbrev ray15304 := rays 7
def bank15304 : Fin 1 → Cell := oneBank p15304 ray15304
theorem signs15304 : ∀ j, Signs p15304 (bank15304 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15305 := params 8
abbrev ray15305 := rays 8
def bank15305 : Fin 1 → Cell := oneBank p15305 ray15305
theorem signs15305 : ∀ j, Signs p15305 (bank15305 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15306 := params 9
abbrev ray15306 := rays 9
def bank15306 : Fin 1 → Cell := oneBank p15306 ray15306
theorem signs15306 : ∀ j, Signs p15306 (bank15306 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15307 := params 10
abbrev ray15307 := rays 10
def bank15307 : Fin 1 → Cell := oneBank p15307 ray15307
theorem signs15307 : ∀ j, Signs p15307 (bank15307 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15308 := params 11
abbrev ray15308 := rays 11
def bank15308 : Fin 1 → Cell := oneBank p15308 ray15308
theorem signs15308 : ∀ j, Signs p15308 (bank15308 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15309 := params 12
abbrev ray15309 := rays 12
def bank15309 : Fin 1 → Cell := oneBank p15309 ray15309
theorem signs15309 : ∀ j, Signs p15309 (bank15309 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15310 := params 13
abbrev ray15310 := rays 13
def bank15310 : Fin 1 → Cell := oneBank p15310 ray15310
theorem signs15310 : ∀ j, Signs p15310 (bank15310 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15311 := params 14
abbrev ray15311 := rays 14
def bank15311 : Fin 1 → Cell := oneBank p15311 ray15311
theorem signs15311 : ∀ j, Signs p15311 (bank15311 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15312 := params 15
abbrev ray15312 := rays 15
def bank15312 : Fin 1 → Cell := oneBank p15312 ray15312
theorem signs15312 : ∀ j, Signs p15312 (bank15312 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15313 := params 16
abbrev ray15313 := rays 16
def bank15313 : Fin 1 → Cell := oneBank p15313 ray15313
theorem signs15313 : ∀ j, Signs p15313 (bank15313 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15314 := params 17
abbrev ray15314 := rays 17
def bank15314 : Fin 1 → Cell := oneBank p15314 ray15314
theorem signs15314 : ∀ j, Signs p15314 (bank15314 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15315 := params 18
abbrev ray15315 := rays 18
def bank15315 : Fin 1 → Cell := oneBank p15315 ray15315
theorem signs15315 : ∀ j, Signs p15315 (bank15315 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15316 := params 19
abbrev ray15316 := rays 19
def bank15316 : Fin 1 → Cell := oneBank p15316 ray15316
theorem signs15316 : ∀ j, Signs p15316 (bank15316 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15317 := params 20
abbrev ray15317 := rays 20
def bank15317 : Fin 1 → Cell := oneBank p15317 ray15317
theorem signs15317 : ∀ j, Signs p15317 (bank15317 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15318 := params 21
abbrev ray15318 := rays 21
def bank15318 : Fin 1 → Cell := oneBank p15318 ray15318
theorem signs15318 : ∀ j, Signs p15318 (bank15318 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15319 := params 22
abbrev ray15319 := rays 22
def bank15319 : Fin 1 → Cell := oneBank p15319 ray15319
theorem signs15319 : ∀ j, Signs p15319 (bank15319 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15320 := params 23
abbrev ray15320 := rays 23
def bank15320 : Fin 1 → Cell := oneBank p15320 ray15320
theorem signs15320 : ∀ j, Signs p15320 (bank15320 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15321 := params 24
abbrev ray15321 := rays 24
def bank15321 : Fin 1 → Cell := oneBank p15321 ray15321
theorem signs15321 : ∀ j, Signs p15321 (bank15321 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15322 := params 25
abbrev ray15322 := rays 25
def bank15322 : Fin 1 → Cell := oneBank p15322 ray15322
theorem signs15322 : ∀ j, Signs p15322 (bank15322 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15323 := params 26
abbrev ray15323 := rays 26
def bank15323 : Fin 1 → Cell := oneBank p15323 ray15323
theorem signs15323 : ∀ j, Signs p15323 (bank15323 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15324 := params 27
abbrev ray15324 := rays 27
def bank15324 : Fin 1 → Cell := oneBank p15324 ray15324
theorem signs15324 : ∀ j, Signs p15324 (bank15324 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15325 := params 28
abbrev ray15325 := rays 28
def bank15325 : Fin 1 → Cell := oneBank p15325 ray15325
theorem signs15325 : ∀ j, Signs p15325 (bank15325 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15326 := params 29
abbrev ray15326 := rays 29
def bank15326 : Fin 1 → Cell := oneBank p15326 ray15326
theorem signs15326 : ∀ j, Signs p15326 (bank15326 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15327 := params 30
abbrev ray15327 := rays 30
def bank15327 : Fin 1 → Cell := oneBank p15327 ray15327
theorem signs15327 : ∀ j, Signs p15327 (bank15327 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15328 := params 31
abbrev ray15328 := rays 31
def bank15328 : Fin 1 → Cell := oneBank p15328 ray15328
theorem signs15328 : ∀ j, Signs p15328 (bank15328 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15297_15328
