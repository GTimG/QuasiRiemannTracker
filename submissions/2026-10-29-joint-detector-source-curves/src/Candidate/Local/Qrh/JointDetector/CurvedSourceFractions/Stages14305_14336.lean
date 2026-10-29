/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14305_14336
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95712741097099,95712294956406,95711848799552,95711402626537,95710956437362,95710510232026,95710064010530,95709617772874,95709171519058,95708725249083,95708278962948,95707832660654,95707386342200,95706940007587,95706493656815,95706047289885,95705600906796,95705154507549,95704708092143,95704261660579,95703815212857,95703368748977,95702922268940,95702475772745,95702029260393,95701582731884,95701136187218,95700689626395,95700243049415,95699796456279,95699349846987,95698903221538,95698456579933]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14304+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14305 := params 0
abbrev ray14305 := rays 0
def bank14305 : Fin 1 → Cell := oneBank p14305 ray14305
theorem signs14305 : ∀ j, Signs p14305 (bank14305 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14306 := params 1
abbrev ray14306 := rays 1
def bank14306 : Fin 1 → Cell := oneBank p14306 ray14306
theorem signs14306 : ∀ j, Signs p14306 (bank14306 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14307 := params 2
abbrev ray14307 := rays 2
def bank14307 : Fin 1 → Cell := oneBank p14307 ray14307
theorem signs14307 : ∀ j, Signs p14307 (bank14307 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14308 := params 3
abbrev ray14308 := rays 3
def bank14308 : Fin 1 → Cell := oneBank p14308 ray14308
theorem signs14308 : ∀ j, Signs p14308 (bank14308 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14309 := params 4
abbrev ray14309 := rays 4
def bank14309 : Fin 1 → Cell := oneBank p14309 ray14309
theorem signs14309 : ∀ j, Signs p14309 (bank14309 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14310 := params 5
abbrev ray14310 := rays 5
def bank14310 : Fin 1 → Cell := oneBank p14310 ray14310
theorem signs14310 : ∀ j, Signs p14310 (bank14310 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14311 := params 6
abbrev ray14311 := rays 6
def bank14311 : Fin 1 → Cell := oneBank p14311 ray14311
theorem signs14311 : ∀ j, Signs p14311 (bank14311 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14312 := params 7
abbrev ray14312 := rays 7
def bank14312 : Fin 1 → Cell := oneBank p14312 ray14312
theorem signs14312 : ∀ j, Signs p14312 (bank14312 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14313 := params 8
abbrev ray14313 := rays 8
def bank14313 : Fin 1 → Cell := oneBank p14313 ray14313
theorem signs14313 : ∀ j, Signs p14313 (bank14313 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14314 := params 9
abbrev ray14314 := rays 9
def bank14314 : Fin 1 → Cell := oneBank p14314 ray14314
theorem signs14314 : ∀ j, Signs p14314 (bank14314 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14315 := params 10
abbrev ray14315 := rays 10
def bank14315 : Fin 1 → Cell := oneBank p14315 ray14315
theorem signs14315 : ∀ j, Signs p14315 (bank14315 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14316 := params 11
abbrev ray14316 := rays 11
def bank14316 : Fin 1 → Cell := oneBank p14316 ray14316
theorem signs14316 : ∀ j, Signs p14316 (bank14316 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14317 := params 12
abbrev ray14317 := rays 12
def bank14317 : Fin 1 → Cell := oneBank p14317 ray14317
theorem signs14317 : ∀ j, Signs p14317 (bank14317 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14318 := params 13
abbrev ray14318 := rays 13
def bank14318 : Fin 1 → Cell := oneBank p14318 ray14318
theorem signs14318 : ∀ j, Signs p14318 (bank14318 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14319 := params 14
abbrev ray14319 := rays 14
def bank14319 : Fin 1 → Cell := oneBank p14319 ray14319
theorem signs14319 : ∀ j, Signs p14319 (bank14319 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14320 := params 15
abbrev ray14320 := rays 15
def bank14320 : Fin 1 → Cell := oneBank p14320 ray14320
theorem signs14320 : ∀ j, Signs p14320 (bank14320 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14321 := params 16
abbrev ray14321 := rays 16
def bank14321 : Fin 1 → Cell := oneBank p14321 ray14321
theorem signs14321 : ∀ j, Signs p14321 (bank14321 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14322 := params 17
abbrev ray14322 := rays 17
def bank14322 : Fin 1 → Cell := oneBank p14322 ray14322
theorem signs14322 : ∀ j, Signs p14322 (bank14322 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14323 := params 18
abbrev ray14323 := rays 18
def bank14323 : Fin 1 → Cell := oneBank p14323 ray14323
theorem signs14323 : ∀ j, Signs p14323 (bank14323 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14324 := params 19
abbrev ray14324 := rays 19
def bank14324 : Fin 1 → Cell := oneBank p14324 ray14324
theorem signs14324 : ∀ j, Signs p14324 (bank14324 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14325 := params 20
abbrev ray14325 := rays 20
def bank14325 : Fin 1 → Cell := oneBank p14325 ray14325
theorem signs14325 : ∀ j, Signs p14325 (bank14325 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14326 := params 21
abbrev ray14326 := rays 21
def bank14326 : Fin 1 → Cell := oneBank p14326 ray14326
theorem signs14326 : ∀ j, Signs p14326 (bank14326 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14327 := params 22
abbrev ray14327 := rays 22
def bank14327 : Fin 1 → Cell := oneBank p14327 ray14327
theorem signs14327 : ∀ j, Signs p14327 (bank14327 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14328 := params 23
abbrev ray14328 := rays 23
def bank14328 : Fin 1 → Cell := oneBank p14328 ray14328
theorem signs14328 : ∀ j, Signs p14328 (bank14328 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14329 := params 24
abbrev ray14329 := rays 24
def bank14329 : Fin 1 → Cell := oneBank p14329 ray14329
theorem signs14329 : ∀ j, Signs p14329 (bank14329 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14330 := params 25
abbrev ray14330 := rays 25
def bank14330 : Fin 1 → Cell := oneBank p14330 ray14330
theorem signs14330 : ∀ j, Signs p14330 (bank14330 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14331 := params 26
abbrev ray14331 := rays 26
def bank14331 : Fin 1 → Cell := oneBank p14331 ray14331
theorem signs14331 : ∀ j, Signs p14331 (bank14331 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14332 := params 27
abbrev ray14332 := rays 27
def bank14332 : Fin 1 → Cell := oneBank p14332 ray14332
theorem signs14332 : ∀ j, Signs p14332 (bank14332 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14333 := params 28
abbrev ray14333 := rays 28
def bank14333 : Fin 1 → Cell := oneBank p14333 ray14333
theorem signs14333 : ∀ j, Signs p14333 (bank14333 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14334 := params 29
abbrev ray14334 := rays 29
def bank14334 : Fin 1 → Cell := oneBank p14334 ray14334
theorem signs14334 : ∀ j, Signs p14334 (bank14334 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14335 := params 30
abbrev ray14335 := rays 30
def bank14335 : Fin 1 → Cell := oneBank p14335 ray14335
theorem signs14335 : ∀ j, Signs p14335 (bank14335 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14336 := params 31
abbrev ray14336 := rays 31
def bank14336 : Fin 1 → Cell := oneBank p14336 ray14336
theorem signs14336 : ∀ j, Signs p14336 (bank14336 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14305_14336
