/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02401_02432
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99617318705185,99617128675633,99616938618928,99616748535070,99616558424062,99616368285904,99616178120598,99615987928146,99615797708548,99615607461806,99615417187922,99615226886897,99615036558732,99614846203429,99614655820989,99614465411413,99614274974703,99614084510860,99613894019885,99613703501780,99613512956546,99613322384185,99613131784698,99612941158086,99612750504351,99612559823494,99612369115516,99612178380419,99611987618204,99611796828873,99611606012427,99611415168867,99611224298195]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2400+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2401 := params 0
abbrev ray2401 := rays 0
def bank2401 : Fin 2 → Cell := twoBank p2401 ray2401
theorem signs2401 : ∀ j, Signs p2401 (bank2401 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2402 := params 1
abbrev ray2402 := rays 1
def bank2402 : Fin 2 → Cell := twoBank p2402 ray2402
theorem signs2402 : ∀ j, Signs p2402 (bank2402 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2403 := params 2
abbrev ray2403 := rays 2
def bank2403 : Fin 2 → Cell := twoBank p2403 ray2403
theorem signs2403 : ∀ j, Signs p2403 (bank2403 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2404 := params 3
abbrev ray2404 := rays 3
def bank2404 : Fin 2 → Cell := twoBank p2404 ray2404
theorem signs2404 : ∀ j, Signs p2404 (bank2404 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2405 := params 4
abbrev ray2405 := rays 4
def bank2405 : Fin 2 → Cell := twoBank p2405 ray2405
theorem signs2405 : ∀ j, Signs p2405 (bank2405 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2406 := params 5
abbrev ray2406 := rays 5
def bank2406 : Fin 2 → Cell := twoBank p2406 ray2406
theorem signs2406 : ∀ j, Signs p2406 (bank2406 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2407 := params 6
abbrev ray2407 := rays 6
def bank2407 : Fin 2 → Cell := twoBank p2407 ray2407
theorem signs2407 : ∀ j, Signs p2407 (bank2407 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2408 := params 7
abbrev ray2408 := rays 7
def bank2408 : Fin 2 → Cell := twoBank p2408 ray2408
theorem signs2408 : ∀ j, Signs p2408 (bank2408 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2409 := params 8
abbrev ray2409 := rays 8
def bank2409 : Fin 2 → Cell := twoBank p2409 ray2409
theorem signs2409 : ∀ j, Signs p2409 (bank2409 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2410 := params 9
abbrev ray2410 := rays 9
def bank2410 : Fin 2 → Cell := twoBank p2410 ray2410
theorem signs2410 : ∀ j, Signs p2410 (bank2410 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2411 := params 10
abbrev ray2411 := rays 10
def bank2411 : Fin 2 → Cell := twoBank p2411 ray2411
theorem signs2411 : ∀ j, Signs p2411 (bank2411 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2412 := params 11
abbrev ray2412 := rays 11
def bank2412 : Fin 2 → Cell := twoBank p2412 ray2412
theorem signs2412 : ∀ j, Signs p2412 (bank2412 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2413 := params 12
abbrev ray2413 := rays 12
def bank2413 : Fin 2 → Cell := twoBank p2413 ray2413
theorem signs2413 : ∀ j, Signs p2413 (bank2413 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2414 := params 13
abbrev ray2414 := rays 13
def bank2414 : Fin 2 → Cell := twoBank p2414 ray2414
theorem signs2414 : ∀ j, Signs p2414 (bank2414 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2415 := params 14
abbrev ray2415 := rays 14
def bank2415 : Fin 2 → Cell := twoBank p2415 ray2415
theorem signs2415 : ∀ j, Signs p2415 (bank2415 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2416 := params 15
abbrev ray2416 := rays 15
def bank2416 : Fin 2 → Cell := twoBank p2416 ray2416
theorem signs2416 : ∀ j, Signs p2416 (bank2416 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2417 := params 16
abbrev ray2417 := rays 16
def bank2417 : Fin 2 → Cell := twoBank p2417 ray2417
theorem signs2417 : ∀ j, Signs p2417 (bank2417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2418 := params 17
abbrev ray2418 := rays 17
def bank2418 : Fin 2 → Cell := twoBank p2418 ray2418
theorem signs2418 : ∀ j, Signs p2418 (bank2418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2419 := params 18
abbrev ray2419 := rays 18
def bank2419 : Fin 2 → Cell := twoBank p2419 ray2419
theorem signs2419 : ∀ j, Signs p2419 (bank2419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2420 := params 19
abbrev ray2420 := rays 19
def bank2420 : Fin 2 → Cell := twoBank p2420 ray2420
theorem signs2420 : ∀ j, Signs p2420 (bank2420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2421 := params 20
abbrev ray2421 := rays 20
def bank2421 : Fin 2 → Cell := twoBank p2421 ray2421
theorem signs2421 : ∀ j, Signs p2421 (bank2421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2422 := params 21
abbrev ray2422 := rays 21
def bank2422 : Fin 2 → Cell := twoBank p2422 ray2422
theorem signs2422 : ∀ j, Signs p2422 (bank2422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2423 := params 22
abbrev ray2423 := rays 22
def bank2423 : Fin 2 → Cell := twoBank p2423 ray2423
theorem signs2423 : ∀ j, Signs p2423 (bank2423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2424 := params 23
abbrev ray2424 := rays 23
def bank2424 : Fin 2 → Cell := twoBank p2424 ray2424
theorem signs2424 : ∀ j, Signs p2424 (bank2424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2425 := params 24
abbrev ray2425 := rays 24
def bank2425 : Fin 2 → Cell := twoBank p2425 ray2425
theorem signs2425 : ∀ j, Signs p2425 (bank2425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2426 := params 25
abbrev ray2426 := rays 25
def bank2426 : Fin 2 → Cell := twoBank p2426 ray2426
theorem signs2426 : ∀ j, Signs p2426 (bank2426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2427 := params 26
abbrev ray2427 := rays 26
def bank2427 : Fin 2 → Cell := twoBank p2427 ray2427
theorem signs2427 : ∀ j, Signs p2427 (bank2427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2428 := params 27
abbrev ray2428 := rays 27
def bank2428 : Fin 2 → Cell := twoBank p2428 ray2428
theorem signs2428 : ∀ j, Signs p2428 (bank2428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2429 := params 28
abbrev ray2429 := rays 28
def bank2429 : Fin 2 → Cell := twoBank p2429 ray2429
theorem signs2429 : ∀ j, Signs p2429 (bank2429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2430 := params 29
abbrev ray2430 := rays 29
def bank2430 : Fin 2 → Cell := twoBank p2430 ray2430
theorem signs2430 : ∀ j, Signs p2430 (bank2430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2431 := params 30
abbrev ray2431 := rays 30
def bank2431 : Fin 2 → Cell := twoBank p2431 ray2431
theorem signs2431 : ∀ j, Signs p2431 (bank2431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2432 := params 31
abbrev ray2432 := rays 31
def bank2432 : Fin 2 → Cell := twoBank p2432 ray2432
theorem signs2432 : ∀ j, Signs p2432 (bank2432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02401_02432
