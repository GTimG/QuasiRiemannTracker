/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16353_16384
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94765347642599,94764868638751,94764389618919,94763910583103,94763431531303,94762952463519,94762473379751,94761994279999,94761515164263,94761036032543,94760556884839,94760077721151,94759598541480,94759119345825,94758640134186,94758160906563,94757681662956,94757202403365,94756723127790,94756243836231,94755764528689,94755285205163,94754805865653,94754326510159,94753847138681,94753367751219,94752888347774,94752408928345,94751929492932,94751450041535,94750970574154,94750491090790,94750011591442]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16352+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16353 := params 0
abbrev ray16353 := rays 0
def bank16353 : Fin 1 → Cell := oneBank p16353 ray16353
theorem signs16353 : ∀ j, Signs p16353 (bank16353 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16354 := params 1
abbrev ray16354 := rays 1
def bank16354 : Fin 1 → Cell := oneBank p16354 ray16354
theorem signs16354 : ∀ j, Signs p16354 (bank16354 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16355 := params 2
abbrev ray16355 := rays 2
def bank16355 : Fin 1 → Cell := oneBank p16355 ray16355
theorem signs16355 : ∀ j, Signs p16355 (bank16355 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16356 := params 3
abbrev ray16356 := rays 3
def bank16356 : Fin 1 → Cell := oneBank p16356 ray16356
theorem signs16356 : ∀ j, Signs p16356 (bank16356 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16357 := params 4
abbrev ray16357 := rays 4
def bank16357 : Fin 1 → Cell := oneBank p16357 ray16357
theorem signs16357 : ∀ j, Signs p16357 (bank16357 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16358 := params 5
abbrev ray16358 := rays 5
def bank16358 : Fin 1 → Cell := oneBank p16358 ray16358
theorem signs16358 : ∀ j, Signs p16358 (bank16358 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16359 := params 6
abbrev ray16359 := rays 6
def bank16359 : Fin 1 → Cell := oneBank p16359 ray16359
theorem signs16359 : ∀ j, Signs p16359 (bank16359 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16360 := params 7
abbrev ray16360 := rays 7
def bank16360 : Fin 1 → Cell := oneBank p16360 ray16360
theorem signs16360 : ∀ j, Signs p16360 (bank16360 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16361 := params 8
abbrev ray16361 := rays 8
def bank16361 : Fin 1 → Cell := oneBank p16361 ray16361
theorem signs16361 : ∀ j, Signs p16361 (bank16361 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16362 := params 9
abbrev ray16362 := rays 9
def bank16362 : Fin 1 → Cell := oneBank p16362 ray16362
theorem signs16362 : ∀ j, Signs p16362 (bank16362 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16363 := params 10
abbrev ray16363 := rays 10
def bank16363 : Fin 1 → Cell := oneBank p16363 ray16363
theorem signs16363 : ∀ j, Signs p16363 (bank16363 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16364 := params 11
abbrev ray16364 := rays 11
def bank16364 : Fin 1 → Cell := oneBank p16364 ray16364
theorem signs16364 : ∀ j, Signs p16364 (bank16364 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16365 := params 12
abbrev ray16365 := rays 12
def bank16365 : Fin 1 → Cell := oneBank p16365 ray16365
theorem signs16365 : ∀ j, Signs p16365 (bank16365 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16366 := params 13
abbrev ray16366 := rays 13
def bank16366 : Fin 1 → Cell := oneBank p16366 ray16366
theorem signs16366 : ∀ j, Signs p16366 (bank16366 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16367 := params 14
abbrev ray16367 := rays 14
def bank16367 : Fin 1 → Cell := oneBank p16367 ray16367
theorem signs16367 : ∀ j, Signs p16367 (bank16367 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16368 := params 15
abbrev ray16368 := rays 15
def bank16368 : Fin 1 → Cell := oneBank p16368 ray16368
theorem signs16368 : ∀ j, Signs p16368 (bank16368 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16369 := params 16
abbrev ray16369 := rays 16
def bank16369 : Fin 1 → Cell := oneBank p16369 ray16369
theorem signs16369 : ∀ j, Signs p16369 (bank16369 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16370 := params 17
abbrev ray16370 := rays 17
def bank16370 : Fin 1 → Cell := oneBank p16370 ray16370
theorem signs16370 : ∀ j, Signs p16370 (bank16370 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16371 := params 18
abbrev ray16371 := rays 18
def bank16371 : Fin 1 → Cell := oneBank p16371 ray16371
theorem signs16371 : ∀ j, Signs p16371 (bank16371 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16372 := params 19
abbrev ray16372 := rays 19
def bank16372 : Fin 1 → Cell := oneBank p16372 ray16372
theorem signs16372 : ∀ j, Signs p16372 (bank16372 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16373 := params 20
abbrev ray16373 := rays 20
def bank16373 : Fin 1 → Cell := oneBank p16373 ray16373
theorem signs16373 : ∀ j, Signs p16373 (bank16373 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16374 := params 21
abbrev ray16374 := rays 21
def bank16374 : Fin 1 → Cell := oneBank p16374 ray16374
theorem signs16374 : ∀ j, Signs p16374 (bank16374 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16375 := params 22
abbrev ray16375 := rays 22
def bank16375 : Fin 1 → Cell := oneBank p16375 ray16375
theorem signs16375 : ∀ j, Signs p16375 (bank16375 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16376 := params 23
abbrev ray16376 := rays 23
def bank16376 : Fin 1 → Cell := oneBank p16376 ray16376
theorem signs16376 : ∀ j, Signs p16376 (bank16376 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16377 := params 24
abbrev ray16377 := rays 24
def bank16377 : Fin 1 → Cell := oneBank p16377 ray16377
theorem signs16377 : ∀ j, Signs p16377 (bank16377 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16378 := params 25
abbrev ray16378 := rays 25
def bank16378 : Fin 1 → Cell := oneBank p16378 ray16378
theorem signs16378 : ∀ j, Signs p16378 (bank16378 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16379 := params 26
abbrev ray16379 := rays 26
def bank16379 : Fin 1 → Cell := oneBank p16379 ray16379
theorem signs16379 : ∀ j, Signs p16379 (bank16379 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16380 := params 27
abbrev ray16380 := rays 27
def bank16380 : Fin 1 → Cell := oneBank p16380 ray16380
theorem signs16380 : ∀ j, Signs p16380 (bank16380 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16381 := params 28
abbrev ray16381 := rays 28
def bank16381 : Fin 1 → Cell := oneBank p16381 ray16381
theorem signs16381 : ∀ j, Signs p16381 (bank16381 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16382 := params 29
abbrev ray16382 := rays 29
def bank16382 : Fin 1 → Cell := oneBank p16382 ray16382
theorem signs16382 : ∀ j, Signs p16382 (bank16382 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16383 := params 30
abbrev ray16383 := rays 30
def bank16383 : Fin 1 → Cell := oneBank p16383 ray16383
theorem signs16383 : ∀ j, Signs p16383 (bank16383 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16384 := params 31
abbrev ray16384 := rays 31
def bank16384 : Fin 1 → Cell := oneBank p16384 ray16384
theorem signs16384 : ∀ j, Signs p16384 (bank16384 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16353_16384
