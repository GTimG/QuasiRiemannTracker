/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14433_14464
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95655503787525,95655055579536,95654607355406,95654159115136,95653710858725,95653262586174,95652814297483,95652365992652,95651917671681,95651469334571,95651020981321,95650572611932,95650124226404,95649675824737,95649227406931,95648778972986,95648330522903,95647882056681,95647433574321,95646985075823,95646536561187,95646088030413,95645639483502,95645190920453,95644742341267,95644293745944,95643845134484,95643396506887,95642947863153,95642499203282,95642050527275,95641601835132,95641153126853]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14432+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14433 := params 0
abbrev ray14433 := rays 0
def bank14433 : Fin 1 → Cell := oneBank p14433 ray14433
theorem signs14433 : ∀ j, Signs p14433 (bank14433 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14434 := params 1
abbrev ray14434 := rays 1
def bank14434 : Fin 1 → Cell := oneBank p14434 ray14434
theorem signs14434 : ∀ j, Signs p14434 (bank14434 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14435 := params 2
abbrev ray14435 := rays 2
def bank14435 : Fin 1 → Cell := oneBank p14435 ray14435
theorem signs14435 : ∀ j, Signs p14435 (bank14435 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14436 := params 3
abbrev ray14436 := rays 3
def bank14436 : Fin 1 → Cell := oneBank p14436 ray14436
theorem signs14436 : ∀ j, Signs p14436 (bank14436 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14437 := params 4
abbrev ray14437 := rays 4
def bank14437 : Fin 1 → Cell := oneBank p14437 ray14437
theorem signs14437 : ∀ j, Signs p14437 (bank14437 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14438 := params 5
abbrev ray14438 := rays 5
def bank14438 : Fin 1 → Cell := oneBank p14438 ray14438
theorem signs14438 : ∀ j, Signs p14438 (bank14438 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14439 := params 6
abbrev ray14439 := rays 6
def bank14439 : Fin 1 → Cell := oneBank p14439 ray14439
theorem signs14439 : ∀ j, Signs p14439 (bank14439 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14440 := params 7
abbrev ray14440 := rays 7
def bank14440 : Fin 1 → Cell := oneBank p14440 ray14440
theorem signs14440 : ∀ j, Signs p14440 (bank14440 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14441 := params 8
abbrev ray14441 := rays 8
def bank14441 : Fin 1 → Cell := oneBank p14441 ray14441
theorem signs14441 : ∀ j, Signs p14441 (bank14441 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14442 := params 9
abbrev ray14442 := rays 9
def bank14442 : Fin 1 → Cell := oneBank p14442 ray14442
theorem signs14442 : ∀ j, Signs p14442 (bank14442 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14443 := params 10
abbrev ray14443 := rays 10
def bank14443 : Fin 1 → Cell := oneBank p14443 ray14443
theorem signs14443 : ∀ j, Signs p14443 (bank14443 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14444 := params 11
abbrev ray14444 := rays 11
def bank14444 : Fin 1 → Cell := oneBank p14444 ray14444
theorem signs14444 : ∀ j, Signs p14444 (bank14444 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14445 := params 12
abbrev ray14445 := rays 12
def bank14445 : Fin 1 → Cell := oneBank p14445 ray14445
theorem signs14445 : ∀ j, Signs p14445 (bank14445 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14446 := params 13
abbrev ray14446 := rays 13
def bank14446 : Fin 1 → Cell := oneBank p14446 ray14446
theorem signs14446 : ∀ j, Signs p14446 (bank14446 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14447 := params 14
abbrev ray14447 := rays 14
def bank14447 : Fin 1 → Cell := oneBank p14447 ray14447
theorem signs14447 : ∀ j, Signs p14447 (bank14447 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14448 := params 15
abbrev ray14448 := rays 15
def bank14448 : Fin 1 → Cell := oneBank p14448 ray14448
theorem signs14448 : ∀ j, Signs p14448 (bank14448 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14449 := params 16
abbrev ray14449 := rays 16
def bank14449 : Fin 1 → Cell := oneBank p14449 ray14449
theorem signs14449 : ∀ j, Signs p14449 (bank14449 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14450 := params 17
abbrev ray14450 := rays 17
def bank14450 : Fin 1 → Cell := oneBank p14450 ray14450
theorem signs14450 : ∀ j, Signs p14450 (bank14450 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14451 := params 18
abbrev ray14451 := rays 18
def bank14451 : Fin 1 → Cell := oneBank p14451 ray14451
theorem signs14451 : ∀ j, Signs p14451 (bank14451 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14452 := params 19
abbrev ray14452 := rays 19
def bank14452 : Fin 1 → Cell := oneBank p14452 ray14452
theorem signs14452 : ∀ j, Signs p14452 (bank14452 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14453 := params 20
abbrev ray14453 := rays 20
def bank14453 : Fin 1 → Cell := oneBank p14453 ray14453
theorem signs14453 : ∀ j, Signs p14453 (bank14453 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14454 := params 21
abbrev ray14454 := rays 21
def bank14454 : Fin 1 → Cell := oneBank p14454 ray14454
theorem signs14454 : ∀ j, Signs p14454 (bank14454 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14455 := params 22
abbrev ray14455 := rays 22
def bank14455 : Fin 1 → Cell := oneBank p14455 ray14455
theorem signs14455 : ∀ j, Signs p14455 (bank14455 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14456 := params 23
abbrev ray14456 := rays 23
def bank14456 : Fin 1 → Cell := oneBank p14456 ray14456
theorem signs14456 : ∀ j, Signs p14456 (bank14456 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14457 := params 24
abbrev ray14457 := rays 24
def bank14457 : Fin 1 → Cell := oneBank p14457 ray14457
theorem signs14457 : ∀ j, Signs p14457 (bank14457 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14458 := params 25
abbrev ray14458 := rays 25
def bank14458 : Fin 1 → Cell := oneBank p14458 ray14458
theorem signs14458 : ∀ j, Signs p14458 (bank14458 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14459 := params 26
abbrev ray14459 := rays 26
def bank14459 : Fin 1 → Cell := oneBank p14459 ray14459
theorem signs14459 : ∀ j, Signs p14459 (bank14459 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14460 := params 27
abbrev ray14460 := rays 27
def bank14460 : Fin 1 → Cell := oneBank p14460 ray14460
theorem signs14460 : ∀ j, Signs p14460 (bank14460 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14461 := params 28
abbrev ray14461 := rays 28
def bank14461 : Fin 1 → Cell := oneBank p14461 ray14461
theorem signs14461 : ∀ j, Signs p14461 (bank14461 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14462 := params 29
abbrev ray14462 := rays 29
def bank14462 : Fin 1 → Cell := oneBank p14462 ray14462
theorem signs14462 : ∀ j, Signs p14462 (bank14462 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14463 := params 30
abbrev ray14463 := rays 30
def bank14463 : Fin 1 → Cell := oneBank p14463 ray14463
theorem signs14463 : ∀ j, Signs p14463 (bank14463 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14464 := params 31
abbrev ray14464 := rays 31
def bank14464 : Fin 1 → Cell := oneBank p14464 ray14464
theorem signs14464 : ∀ j, Signs p14464 (bank14464 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14433_14464
