/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16321_16352
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94780667326114,94780188833760,94779710325422,94779231801099,94778753260792,94778274704501,94777796132225,94777317543965,94776838939721,94776360319492,94775881683279,94775403031082,94774924362901,94774445678735,94773966978585,94773488262451,94773009530333,94772530782231,94772052018144,94771573238073,94771094442018,94770615629979,94770136801956,94769657957949,94769179097958,94768700221983,94768221330023,94767742422079,94767263498151,94766784558239,94766305602343,94765826630463,94765347642599]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16320+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16321 := params 0
abbrev ray16321 := rays 0
def bank16321 : Fin 1 → Cell := oneBank p16321 ray16321
theorem signs16321 : ∀ j, Signs p16321 (bank16321 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16322 := params 1
abbrev ray16322 := rays 1
def bank16322 : Fin 1 → Cell := oneBank p16322 ray16322
theorem signs16322 : ∀ j, Signs p16322 (bank16322 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16323 := params 2
abbrev ray16323 := rays 2
def bank16323 : Fin 1 → Cell := oneBank p16323 ray16323
theorem signs16323 : ∀ j, Signs p16323 (bank16323 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16324 := params 3
abbrev ray16324 := rays 3
def bank16324 : Fin 1 → Cell := oneBank p16324 ray16324
theorem signs16324 : ∀ j, Signs p16324 (bank16324 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16325 := params 4
abbrev ray16325 := rays 4
def bank16325 : Fin 1 → Cell := oneBank p16325 ray16325
theorem signs16325 : ∀ j, Signs p16325 (bank16325 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16326 := params 5
abbrev ray16326 := rays 5
def bank16326 : Fin 1 → Cell := oneBank p16326 ray16326
theorem signs16326 : ∀ j, Signs p16326 (bank16326 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16327 := params 6
abbrev ray16327 := rays 6
def bank16327 : Fin 1 → Cell := oneBank p16327 ray16327
theorem signs16327 : ∀ j, Signs p16327 (bank16327 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16328 := params 7
abbrev ray16328 := rays 7
def bank16328 : Fin 1 → Cell := oneBank p16328 ray16328
theorem signs16328 : ∀ j, Signs p16328 (bank16328 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16329 := params 8
abbrev ray16329 := rays 8
def bank16329 : Fin 1 → Cell := oneBank p16329 ray16329
theorem signs16329 : ∀ j, Signs p16329 (bank16329 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16330 := params 9
abbrev ray16330 := rays 9
def bank16330 : Fin 1 → Cell := oneBank p16330 ray16330
theorem signs16330 : ∀ j, Signs p16330 (bank16330 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16331 := params 10
abbrev ray16331 := rays 10
def bank16331 : Fin 1 → Cell := oneBank p16331 ray16331
theorem signs16331 : ∀ j, Signs p16331 (bank16331 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16332 := params 11
abbrev ray16332 := rays 11
def bank16332 : Fin 1 → Cell := oneBank p16332 ray16332
theorem signs16332 : ∀ j, Signs p16332 (bank16332 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16333 := params 12
abbrev ray16333 := rays 12
def bank16333 : Fin 1 → Cell := oneBank p16333 ray16333
theorem signs16333 : ∀ j, Signs p16333 (bank16333 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16334 := params 13
abbrev ray16334 := rays 13
def bank16334 : Fin 1 → Cell := oneBank p16334 ray16334
theorem signs16334 : ∀ j, Signs p16334 (bank16334 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16335 := params 14
abbrev ray16335 := rays 14
def bank16335 : Fin 1 → Cell := oneBank p16335 ray16335
theorem signs16335 : ∀ j, Signs p16335 (bank16335 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16336 := params 15
abbrev ray16336 := rays 15
def bank16336 : Fin 1 → Cell := oneBank p16336 ray16336
theorem signs16336 : ∀ j, Signs p16336 (bank16336 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16337 := params 16
abbrev ray16337 := rays 16
def bank16337 : Fin 1 → Cell := oneBank p16337 ray16337
theorem signs16337 : ∀ j, Signs p16337 (bank16337 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16338 := params 17
abbrev ray16338 := rays 17
def bank16338 : Fin 1 → Cell := oneBank p16338 ray16338
theorem signs16338 : ∀ j, Signs p16338 (bank16338 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16339 := params 18
abbrev ray16339 := rays 18
def bank16339 : Fin 1 → Cell := oneBank p16339 ray16339
theorem signs16339 : ∀ j, Signs p16339 (bank16339 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16340 := params 19
abbrev ray16340 := rays 19
def bank16340 : Fin 1 → Cell := oneBank p16340 ray16340
theorem signs16340 : ∀ j, Signs p16340 (bank16340 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16341 := params 20
abbrev ray16341 := rays 20
def bank16341 : Fin 1 → Cell := oneBank p16341 ray16341
theorem signs16341 : ∀ j, Signs p16341 (bank16341 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16342 := params 21
abbrev ray16342 := rays 21
def bank16342 : Fin 1 → Cell := oneBank p16342 ray16342
theorem signs16342 : ∀ j, Signs p16342 (bank16342 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16343 := params 22
abbrev ray16343 := rays 22
def bank16343 : Fin 1 → Cell := oneBank p16343 ray16343
theorem signs16343 : ∀ j, Signs p16343 (bank16343 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16344 := params 23
abbrev ray16344 := rays 23
def bank16344 : Fin 1 → Cell := oneBank p16344 ray16344
theorem signs16344 : ∀ j, Signs p16344 (bank16344 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16345 := params 24
abbrev ray16345 := rays 24
def bank16345 : Fin 1 → Cell := oneBank p16345 ray16345
theorem signs16345 : ∀ j, Signs p16345 (bank16345 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16346 := params 25
abbrev ray16346 := rays 25
def bank16346 : Fin 1 → Cell := oneBank p16346 ray16346
theorem signs16346 : ∀ j, Signs p16346 (bank16346 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16347 := params 26
abbrev ray16347 := rays 26
def bank16347 : Fin 1 → Cell := oneBank p16347 ray16347
theorem signs16347 : ∀ j, Signs p16347 (bank16347 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16348 := params 27
abbrev ray16348 := rays 27
def bank16348 : Fin 1 → Cell := oneBank p16348 ray16348
theorem signs16348 : ∀ j, Signs p16348 (bank16348 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16349 := params 28
abbrev ray16349 := rays 28
def bank16349 : Fin 1 → Cell := oneBank p16349 ray16349
theorem signs16349 : ∀ j, Signs p16349 (bank16349 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16350 := params 29
abbrev ray16350 := rays 29
def bank16350 : Fin 1 → Cell := oneBank p16350 ray16350
theorem signs16350 : ∀ j, Signs p16350 (bank16350 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16351 := params 30
abbrev ray16351 := rays 30
def bank16351 : Fin 1 → Cell := oneBank p16351 ray16351
theorem signs16351 : ∀ j, Signs p16351 (bank16351 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16352 := params 31
abbrev ray16352 := rays 31
def bank16352 : Fin 1 → Cell := oneBank p16352 ray16352
theorem signs16352 : ∀ j, Signs p16352 (bank16352 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16321_16352
