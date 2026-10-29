/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13441_13472
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96092148391561,96091716282635,96091284157380,96090852015796,96090419857883,96089987683642,96089555493072,96089123286174,96088691062948,96088258823395,96087826567514,96087394295306,96086962006771,96086529701909,96086097380721,96085665043206,96085232689365,96084800319199,96084367932707,96083935529890,96083503110747,96083070675279,96082638223487,96082205755370,96081773270929,96081340770164,96080908253075,96080475719663,96080043169927,96079610603868,96079178021486,96078745422782,96078312807755]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13440+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13441 := params 0
abbrev ray13441 := rays 0
def bank13441 : Fin 1 → Cell := oneBank p13441 ray13441
theorem signs13441 : ∀ j, Signs p13441 (bank13441 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13442 := params 1
abbrev ray13442 := rays 1
def bank13442 : Fin 1 → Cell := oneBank p13442 ray13442
theorem signs13442 : ∀ j, Signs p13442 (bank13442 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13443 := params 2
abbrev ray13443 := rays 2
def bank13443 : Fin 1 → Cell := oneBank p13443 ray13443
theorem signs13443 : ∀ j, Signs p13443 (bank13443 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13444 := params 3
abbrev ray13444 := rays 3
def bank13444 : Fin 1 → Cell := oneBank p13444 ray13444
theorem signs13444 : ∀ j, Signs p13444 (bank13444 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13445 := params 4
abbrev ray13445 := rays 4
def bank13445 : Fin 1 → Cell := oneBank p13445 ray13445
theorem signs13445 : ∀ j, Signs p13445 (bank13445 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13446 := params 5
abbrev ray13446 := rays 5
def bank13446 : Fin 1 → Cell := oneBank p13446 ray13446
theorem signs13446 : ∀ j, Signs p13446 (bank13446 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13447 := params 6
abbrev ray13447 := rays 6
def bank13447 : Fin 1 → Cell := oneBank p13447 ray13447
theorem signs13447 : ∀ j, Signs p13447 (bank13447 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13448 := params 7
abbrev ray13448 := rays 7
def bank13448 : Fin 1 → Cell := oneBank p13448 ray13448
theorem signs13448 : ∀ j, Signs p13448 (bank13448 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13449 := params 8
abbrev ray13449 := rays 8
def bank13449 : Fin 1 → Cell := oneBank p13449 ray13449
theorem signs13449 : ∀ j, Signs p13449 (bank13449 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13450 := params 9
abbrev ray13450 := rays 9
def bank13450 : Fin 1 → Cell := oneBank p13450 ray13450
theorem signs13450 : ∀ j, Signs p13450 (bank13450 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13451 := params 10
abbrev ray13451 := rays 10
def bank13451 : Fin 1 → Cell := oneBank p13451 ray13451
theorem signs13451 : ∀ j, Signs p13451 (bank13451 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13452 := params 11
abbrev ray13452 := rays 11
def bank13452 : Fin 1 → Cell := oneBank p13452 ray13452
theorem signs13452 : ∀ j, Signs p13452 (bank13452 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13453 := params 12
abbrev ray13453 := rays 12
def bank13453 : Fin 1 → Cell := oneBank p13453 ray13453
theorem signs13453 : ∀ j, Signs p13453 (bank13453 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13454 := params 13
abbrev ray13454 := rays 13
def bank13454 : Fin 1 → Cell := oneBank p13454 ray13454
theorem signs13454 : ∀ j, Signs p13454 (bank13454 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13455 := params 14
abbrev ray13455 := rays 14
def bank13455 : Fin 1 → Cell := oneBank p13455 ray13455
theorem signs13455 : ∀ j, Signs p13455 (bank13455 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13456 := params 15
abbrev ray13456 := rays 15
def bank13456 : Fin 1 → Cell := oneBank p13456 ray13456
theorem signs13456 : ∀ j, Signs p13456 (bank13456 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13457 := params 16
abbrev ray13457 := rays 16
def bank13457 : Fin 1 → Cell := oneBank p13457 ray13457
theorem signs13457 : ∀ j, Signs p13457 (bank13457 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13458 := params 17
abbrev ray13458 := rays 17
def bank13458 : Fin 1 → Cell := oneBank p13458 ray13458
theorem signs13458 : ∀ j, Signs p13458 (bank13458 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13459 := params 18
abbrev ray13459 := rays 18
def bank13459 : Fin 1 → Cell := oneBank p13459 ray13459
theorem signs13459 : ∀ j, Signs p13459 (bank13459 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13460 := params 19
abbrev ray13460 := rays 19
def bank13460 : Fin 1 → Cell := oneBank p13460 ray13460
theorem signs13460 : ∀ j, Signs p13460 (bank13460 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13461 := params 20
abbrev ray13461 := rays 20
def bank13461 : Fin 1 → Cell := oneBank p13461 ray13461
theorem signs13461 : ∀ j, Signs p13461 (bank13461 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13462 := params 21
abbrev ray13462 := rays 21
def bank13462 : Fin 1 → Cell := oneBank p13462 ray13462
theorem signs13462 : ∀ j, Signs p13462 (bank13462 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13463 := params 22
abbrev ray13463 := rays 22
def bank13463 : Fin 1 → Cell := oneBank p13463 ray13463
theorem signs13463 : ∀ j, Signs p13463 (bank13463 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13464 := params 23
abbrev ray13464 := rays 23
def bank13464 : Fin 1 → Cell := oneBank p13464 ray13464
theorem signs13464 : ∀ j, Signs p13464 (bank13464 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13465 := params 24
abbrev ray13465 := rays 24
def bank13465 : Fin 1 → Cell := oneBank p13465 ray13465
theorem signs13465 : ∀ j, Signs p13465 (bank13465 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13466 := params 25
abbrev ray13466 := rays 25
def bank13466 : Fin 1 → Cell := oneBank p13466 ray13466
theorem signs13466 : ∀ j, Signs p13466 (bank13466 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13467 := params 26
abbrev ray13467 := rays 26
def bank13467 : Fin 1 → Cell := oneBank p13467 ray13467
theorem signs13467 : ∀ j, Signs p13467 (bank13467 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13468 := params 27
abbrev ray13468 := rays 27
def bank13468 : Fin 1 → Cell := oneBank p13468 ray13468
theorem signs13468 : ∀ j, Signs p13468 (bank13468 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13469 := params 28
abbrev ray13469 := rays 28
def bank13469 : Fin 1 → Cell := oneBank p13469 ray13469
theorem signs13469 : ∀ j, Signs p13469 (bank13469 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13470 := params 29
abbrev ray13470 := rays 29
def bank13470 : Fin 1 → Cell := oneBank p13470 ray13470
theorem signs13470 : ∀ j, Signs p13470 (bank13470 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13471 := params 30
abbrev ray13471 := rays 30
def bank13471 : Fin 1 → Cell := oneBank p13471 ray13471
theorem signs13471 : ∀ j, Signs p13471 (bank13471 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13472 := params 31
abbrev ray13472 := rays 31
def bank13472 : Fin 1 → Cell := oneBank p13472 ray13472
theorem signs13472 : ∀ j, Signs p13472 (bank13472 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13441_13472
