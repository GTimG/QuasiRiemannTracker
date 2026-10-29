/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07457_07488
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98334994367324,98334681453529,98334368517755,98334055560003,98333742580274,98333429578568,98333116554887,98332803509231,98332490441601,98332177351997,98331864240421,98331551106873,98331237951354,98330924773864,98330611574404,98330298352976,98329985109579,98329671844215,98329358556884,98329045247587,98328731916325,98328418563099,98328105187909,98327791790756,98327478371641,98327164930564,98326851467526,98326537982528,98326224475571,98325910946656,98325597395783,98325283822953,98324970228166]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7456+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7457 := params 0
abbrev ray7457 := rays 0
def bank7457 : Fin 2 → Cell := twoBank p7457 ray7457
theorem signs7457 : ∀ j, Signs p7457 (bank7457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7458 := params 1
abbrev ray7458 := rays 1
def bank7458 : Fin 2 → Cell := twoBank p7458 ray7458
theorem signs7458 : ∀ j, Signs p7458 (bank7458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7459 := params 2
abbrev ray7459 := rays 2
def bank7459 : Fin 2 → Cell := twoBank p7459 ray7459
theorem signs7459 : ∀ j, Signs p7459 (bank7459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7460 := params 3
abbrev ray7460 := rays 3
def bank7460 : Fin 2 → Cell := twoBank p7460 ray7460
theorem signs7460 : ∀ j, Signs p7460 (bank7460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7461 := params 4
abbrev ray7461 := rays 4
def bank7461 : Fin 2 → Cell := twoBank p7461 ray7461
theorem signs7461 : ∀ j, Signs p7461 (bank7461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7462 := params 5
abbrev ray7462 := rays 5
def bank7462 : Fin 2 → Cell := twoBank p7462 ray7462
theorem signs7462 : ∀ j, Signs p7462 (bank7462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7463 := params 6
abbrev ray7463 := rays 6
def bank7463 : Fin 2 → Cell := twoBank p7463 ray7463
theorem signs7463 : ∀ j, Signs p7463 (bank7463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7464 := params 7
abbrev ray7464 := rays 7
def bank7464 : Fin 2 → Cell := twoBank p7464 ray7464
theorem signs7464 : ∀ j, Signs p7464 (bank7464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7465 := params 8
abbrev ray7465 := rays 8
def bank7465 : Fin 2 → Cell := twoBank p7465 ray7465
theorem signs7465 : ∀ j, Signs p7465 (bank7465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7466 := params 9
abbrev ray7466 := rays 9
def bank7466 : Fin 2 → Cell := twoBank p7466 ray7466
theorem signs7466 : ∀ j, Signs p7466 (bank7466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7467 := params 10
abbrev ray7467 := rays 10
def bank7467 : Fin 2 → Cell := twoBank p7467 ray7467
theorem signs7467 : ∀ j, Signs p7467 (bank7467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7468 := params 11
abbrev ray7468 := rays 11
def bank7468 : Fin 2 → Cell := twoBank p7468 ray7468
theorem signs7468 : ∀ j, Signs p7468 (bank7468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7469 := params 12
abbrev ray7469 := rays 12
def bank7469 : Fin 2 → Cell := twoBank p7469 ray7469
theorem signs7469 : ∀ j, Signs p7469 (bank7469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7470 := params 13
abbrev ray7470 := rays 13
def bank7470 : Fin 2 → Cell := twoBank p7470 ray7470
theorem signs7470 : ∀ j, Signs p7470 (bank7470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7471 := params 14
abbrev ray7471 := rays 14
def bank7471 : Fin 2 → Cell := twoBank p7471 ray7471
theorem signs7471 : ∀ j, Signs p7471 (bank7471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7472 := params 15
abbrev ray7472 := rays 15
def bank7472 : Fin 2 → Cell := twoBank p7472 ray7472
theorem signs7472 : ∀ j, Signs p7472 (bank7472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7473 := params 16
abbrev ray7473 := rays 16
def bank7473 : Fin 2 → Cell := twoBank p7473 ray7473
theorem signs7473 : ∀ j, Signs p7473 (bank7473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7474 := params 17
abbrev ray7474 := rays 17
def bank7474 : Fin 2 → Cell := twoBank p7474 ray7474
theorem signs7474 : ∀ j, Signs p7474 (bank7474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7475 := params 18
abbrev ray7475 := rays 18
def bank7475 : Fin 2 → Cell := twoBank p7475 ray7475
theorem signs7475 : ∀ j, Signs p7475 (bank7475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7476 := params 19
abbrev ray7476 := rays 19
def bank7476 : Fin 2 → Cell := twoBank p7476 ray7476
theorem signs7476 : ∀ j, Signs p7476 (bank7476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7477 := params 20
abbrev ray7477 := rays 20
def bank7477 : Fin 2 → Cell := twoBank p7477 ray7477
theorem signs7477 : ∀ j, Signs p7477 (bank7477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7478 := params 21
abbrev ray7478 := rays 21
def bank7478 : Fin 2 → Cell := twoBank p7478 ray7478
theorem signs7478 : ∀ j, Signs p7478 (bank7478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7479 := params 22
abbrev ray7479 := rays 22
def bank7479 : Fin 2 → Cell := twoBank p7479 ray7479
theorem signs7479 : ∀ j, Signs p7479 (bank7479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7480 := params 23
abbrev ray7480 := rays 23
def bank7480 : Fin 2 → Cell := twoBank p7480 ray7480
theorem signs7480 : ∀ j, Signs p7480 (bank7480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7481 := params 24
abbrev ray7481 := rays 24
def bank7481 : Fin 2 → Cell := twoBank p7481 ray7481
theorem signs7481 : ∀ j, Signs p7481 (bank7481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7482 := params 25
abbrev ray7482 := rays 25
def bank7482 : Fin 2 → Cell := twoBank p7482 ray7482
theorem signs7482 : ∀ j, Signs p7482 (bank7482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7483 := params 26
abbrev ray7483 := rays 26
def bank7483 : Fin 2 → Cell := twoBank p7483 ray7483
theorem signs7483 : ∀ j, Signs p7483 (bank7483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7484 := params 27
abbrev ray7484 := rays 27
def bank7484 : Fin 2 → Cell := twoBank p7484 ray7484
theorem signs7484 : ∀ j, Signs p7484 (bank7484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7485 := params 28
abbrev ray7485 := rays 28
def bank7485 : Fin 2 → Cell := twoBank p7485 ray7485
theorem signs7485 : ∀ j, Signs p7485 (bank7485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7486 := params 29
abbrev ray7486 := rays 29
def bank7486 : Fin 2 → Cell := twoBank p7486 ray7486
theorem signs7486 : ∀ j, Signs p7486 (bank7486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7487 := params 30
abbrev ray7487 := rays 30
def bank7487 : Fin 2 → Cell := twoBank p7487 ray7487
theorem signs7487 : ∀ j, Signs p7487 (bank7487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7488 := params 31
abbrev ray7488 := rays 31
def bank7488 : Fin 2 → Cell := twoBank p7488 ray7488
theorem signs7488 : ∀ j, Signs p7488 (bank7488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07457_07488
