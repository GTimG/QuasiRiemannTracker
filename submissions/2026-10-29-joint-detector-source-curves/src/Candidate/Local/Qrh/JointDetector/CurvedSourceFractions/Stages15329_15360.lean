/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15329_15360
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95247453952713,95246991335117,95246528701488,95246066051825,95245603386129,95245140704400,95244678006638,95244215292843,95243752563015,95243289817154,95242827055260,95242364277334,95241901483375,95241438673384,95240975847360,95240513005304,95240050147216,95239587273095,95239124382942,95238661476757,95238198554541,95237735616293,95237272662013,95236809691701,95236346705358,95235883702983,95235420684577,95234957650140,95234494599672,95234031533172,95233568450641,95233105352079,95232642237487]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15328+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15329 := params 0
abbrev ray15329 := rays 0
def bank15329 : Fin 1 → Cell := oneBank p15329 ray15329
theorem signs15329 : ∀ j, Signs p15329 (bank15329 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15330 := params 1
abbrev ray15330 := rays 1
def bank15330 : Fin 1 → Cell := oneBank p15330 ray15330
theorem signs15330 : ∀ j, Signs p15330 (bank15330 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15331 := params 2
abbrev ray15331 := rays 2
def bank15331 : Fin 1 → Cell := oneBank p15331 ray15331
theorem signs15331 : ∀ j, Signs p15331 (bank15331 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15332 := params 3
abbrev ray15332 := rays 3
def bank15332 : Fin 1 → Cell := oneBank p15332 ray15332
theorem signs15332 : ∀ j, Signs p15332 (bank15332 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15333 := params 4
abbrev ray15333 := rays 4
def bank15333 : Fin 1 → Cell := oneBank p15333 ray15333
theorem signs15333 : ∀ j, Signs p15333 (bank15333 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15334 := params 5
abbrev ray15334 := rays 5
def bank15334 : Fin 1 → Cell := oneBank p15334 ray15334
theorem signs15334 : ∀ j, Signs p15334 (bank15334 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15335 := params 6
abbrev ray15335 := rays 6
def bank15335 : Fin 1 → Cell := oneBank p15335 ray15335
theorem signs15335 : ∀ j, Signs p15335 (bank15335 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15336 := params 7
abbrev ray15336 := rays 7
def bank15336 : Fin 1 → Cell := oneBank p15336 ray15336
theorem signs15336 : ∀ j, Signs p15336 (bank15336 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15337 := params 8
abbrev ray15337 := rays 8
def bank15337 : Fin 1 → Cell := oneBank p15337 ray15337
theorem signs15337 : ∀ j, Signs p15337 (bank15337 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15338 := params 9
abbrev ray15338 := rays 9
def bank15338 : Fin 1 → Cell := oneBank p15338 ray15338
theorem signs15338 : ∀ j, Signs p15338 (bank15338 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15339 := params 10
abbrev ray15339 := rays 10
def bank15339 : Fin 1 → Cell := oneBank p15339 ray15339
theorem signs15339 : ∀ j, Signs p15339 (bank15339 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15340 := params 11
abbrev ray15340 := rays 11
def bank15340 : Fin 1 → Cell := oneBank p15340 ray15340
theorem signs15340 : ∀ j, Signs p15340 (bank15340 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15341 := params 12
abbrev ray15341 := rays 12
def bank15341 : Fin 1 → Cell := oneBank p15341 ray15341
theorem signs15341 : ∀ j, Signs p15341 (bank15341 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15342 := params 13
abbrev ray15342 := rays 13
def bank15342 : Fin 1 → Cell := oneBank p15342 ray15342
theorem signs15342 : ∀ j, Signs p15342 (bank15342 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15343 := params 14
abbrev ray15343 := rays 14
def bank15343 : Fin 1 → Cell := oneBank p15343 ray15343
theorem signs15343 : ∀ j, Signs p15343 (bank15343 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15344 := params 15
abbrev ray15344 := rays 15
def bank15344 : Fin 1 → Cell := oneBank p15344 ray15344
theorem signs15344 : ∀ j, Signs p15344 (bank15344 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15345 := params 16
abbrev ray15345 := rays 16
def bank15345 : Fin 1 → Cell := oneBank p15345 ray15345
theorem signs15345 : ∀ j, Signs p15345 (bank15345 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15346 := params 17
abbrev ray15346 := rays 17
def bank15346 : Fin 1 → Cell := oneBank p15346 ray15346
theorem signs15346 : ∀ j, Signs p15346 (bank15346 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15347 := params 18
abbrev ray15347 := rays 18
def bank15347 : Fin 1 → Cell := oneBank p15347 ray15347
theorem signs15347 : ∀ j, Signs p15347 (bank15347 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15348 := params 19
abbrev ray15348 := rays 19
def bank15348 : Fin 1 → Cell := oneBank p15348 ray15348
theorem signs15348 : ∀ j, Signs p15348 (bank15348 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15349 := params 20
abbrev ray15349 := rays 20
def bank15349 : Fin 1 → Cell := oneBank p15349 ray15349
theorem signs15349 : ∀ j, Signs p15349 (bank15349 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15350 := params 21
abbrev ray15350 := rays 21
def bank15350 : Fin 1 → Cell := oneBank p15350 ray15350
theorem signs15350 : ∀ j, Signs p15350 (bank15350 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15351 := params 22
abbrev ray15351 := rays 22
def bank15351 : Fin 1 → Cell := oneBank p15351 ray15351
theorem signs15351 : ∀ j, Signs p15351 (bank15351 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15352 := params 23
abbrev ray15352 := rays 23
def bank15352 : Fin 1 → Cell := oneBank p15352 ray15352
theorem signs15352 : ∀ j, Signs p15352 (bank15352 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15353 := params 24
abbrev ray15353 := rays 24
def bank15353 : Fin 1 → Cell := oneBank p15353 ray15353
theorem signs15353 : ∀ j, Signs p15353 (bank15353 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15354 := params 25
abbrev ray15354 := rays 25
def bank15354 : Fin 1 → Cell := oneBank p15354 ray15354
theorem signs15354 : ∀ j, Signs p15354 (bank15354 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15355 := params 26
abbrev ray15355 := rays 26
def bank15355 : Fin 1 → Cell := oneBank p15355 ray15355
theorem signs15355 : ∀ j, Signs p15355 (bank15355 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15356 := params 27
abbrev ray15356 := rays 27
def bank15356 : Fin 1 → Cell := oneBank p15356 ray15356
theorem signs15356 : ∀ j, Signs p15356 (bank15356 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15357 := params 28
abbrev ray15357 := rays 28
def bank15357 : Fin 1 → Cell := oneBank p15357 ray15357
theorem signs15357 : ∀ j, Signs p15357 (bank15357 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15358 := params 29
abbrev ray15358 := rays 29
def bank15358 : Fin 1 → Cell := oneBank p15358 ray15358
theorem signs15358 : ∀ j, Signs p15358 (bank15358 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15359 := params 30
abbrev ray15359 := rays 30
def bank15359 : Fin 1 → Cell := oneBank p15359 ray15359
theorem signs15359 : ∀ j, Signs p15359 (bank15359 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15360 := params 31
abbrev ray15360 := rays 31
def bank15360 : Fin 1 → Cell := oneBank p15360 ray15360
theorem signs15360 : ∀ j, Signs p15360 (bank15360 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15329_15360
