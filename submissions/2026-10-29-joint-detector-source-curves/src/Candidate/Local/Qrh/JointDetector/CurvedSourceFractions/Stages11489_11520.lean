/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11489_11520
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96901985919765,96901589599715,96901193260082,96900796900866,96900400522067,96900004123686,96899607705723,96899211268179,96898814811055,96898418334350,96898021838066,96897625322202,96897228786759,96896832231738,96896435657139,96896039062963,96895642449210,96895245815880,96894849162974,96894452490492,96894055798435,96893659086803,96893262355597,96892865604817,96892468834464,96892072044538,96891675235040,96891278405970,96890881557328,96890484689115,96890087801332,96889690893979,96889293967056]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11488+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11489 := params 0
abbrev ray11489 := rays 0
def bank11489 : Fin 2 → Cell := twoBank p11489 ray11489
theorem signs11489 : ∀ j, Signs p11489 (bank11489 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11490 := params 1
abbrev ray11490 := rays 1
def bank11490 : Fin 2 → Cell := twoBank p11490 ray11490
theorem signs11490 : ∀ j, Signs p11490 (bank11490 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11491 := params 2
abbrev ray11491 := rays 2
def bank11491 : Fin 2 → Cell := twoBank p11491 ray11491
theorem signs11491 : ∀ j, Signs p11491 (bank11491 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11492 := params 3
abbrev ray11492 := rays 3
def bank11492 : Fin 2 → Cell := twoBank p11492 ray11492
theorem signs11492 : ∀ j, Signs p11492 (bank11492 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11493 := params 4
abbrev ray11493 := rays 4
def bank11493 : Fin 2 → Cell := twoBank p11493 ray11493
theorem signs11493 : ∀ j, Signs p11493 (bank11493 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11494 := params 5
abbrev ray11494 := rays 5
def bank11494 : Fin 2 → Cell := twoBank p11494 ray11494
theorem signs11494 : ∀ j, Signs p11494 (bank11494 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11495 := params 6
abbrev ray11495 := rays 6
def bank11495 : Fin 2 → Cell := twoBank p11495 ray11495
theorem signs11495 : ∀ j, Signs p11495 (bank11495 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11496 := params 7
abbrev ray11496 := rays 7
def bank11496 : Fin 2 → Cell := twoBank p11496 ray11496
theorem signs11496 : ∀ j, Signs p11496 (bank11496 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11497 := params 8
abbrev ray11497 := rays 8
def bank11497 : Fin 2 → Cell := twoBank p11497 ray11497
theorem signs11497 : ∀ j, Signs p11497 (bank11497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11498 := params 9
abbrev ray11498 := rays 9
def bank11498 : Fin 2 → Cell := twoBank p11498 ray11498
theorem signs11498 : ∀ j, Signs p11498 (bank11498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11499 := params 10
abbrev ray11499 := rays 10
def bank11499 : Fin 2 → Cell := twoBank p11499 ray11499
theorem signs11499 : ∀ j, Signs p11499 (bank11499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11500 := params 11
abbrev ray11500 := rays 11
def bank11500 : Fin 2 → Cell := twoBank p11500 ray11500
theorem signs11500 : ∀ j, Signs p11500 (bank11500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11501 := params 12
abbrev ray11501 := rays 12
def bank11501 : Fin 2 → Cell := twoBank p11501 ray11501
theorem signs11501 : ∀ j, Signs p11501 (bank11501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11502 := params 13
abbrev ray11502 := rays 13
def bank11502 : Fin 2 → Cell := twoBank p11502 ray11502
theorem signs11502 : ∀ j, Signs p11502 (bank11502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11503 := params 14
abbrev ray11503 := rays 14
def bank11503 : Fin 2 → Cell := twoBank p11503 ray11503
theorem signs11503 : ∀ j, Signs p11503 (bank11503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11504 := params 15
abbrev ray11504 := rays 15
def bank11504 : Fin 2 → Cell := twoBank p11504 ray11504
theorem signs11504 : ∀ j, Signs p11504 (bank11504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11505 := params 16
abbrev ray11505 := rays 16
def bank11505 : Fin 2 → Cell := twoBank p11505 ray11505
theorem signs11505 : ∀ j, Signs p11505 (bank11505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11506 := params 17
abbrev ray11506 := rays 17
def bank11506 : Fin 2 → Cell := twoBank p11506 ray11506
theorem signs11506 : ∀ j, Signs p11506 (bank11506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11507 := params 18
abbrev ray11507 := rays 18
def bank11507 : Fin 2 → Cell := twoBank p11507 ray11507
theorem signs11507 : ∀ j, Signs p11507 (bank11507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11508 := params 19
abbrev ray11508 := rays 19
def bank11508 : Fin 2 → Cell := twoBank p11508 ray11508
theorem signs11508 : ∀ j, Signs p11508 (bank11508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11509 := params 20
abbrev ray11509 := rays 20
def bank11509 : Fin 2 → Cell := twoBank p11509 ray11509
theorem signs11509 : ∀ j, Signs p11509 (bank11509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11510 := params 21
abbrev ray11510 := rays 21
def bank11510 : Fin 2 → Cell := twoBank p11510 ray11510
theorem signs11510 : ∀ j, Signs p11510 (bank11510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11511 := params 22
abbrev ray11511 := rays 22
def bank11511 : Fin 2 → Cell := twoBank p11511 ray11511
theorem signs11511 : ∀ j, Signs p11511 (bank11511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11512 := params 23
abbrev ray11512 := rays 23
def bank11512 : Fin 2 → Cell := twoBank p11512 ray11512
theorem signs11512 : ∀ j, Signs p11512 (bank11512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11513 := params 24
abbrev ray11513 := rays 24
def bank11513 : Fin 2 → Cell := twoBank p11513 ray11513
theorem signs11513 : ∀ j, Signs p11513 (bank11513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11514 := params 25
abbrev ray11514 := rays 25
def bank11514 : Fin 2 → Cell := twoBank p11514 ray11514
theorem signs11514 : ∀ j, Signs p11514 (bank11514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11515 := params 26
abbrev ray11515 := rays 26
def bank11515 : Fin 2 → Cell := twoBank p11515 ray11515
theorem signs11515 : ∀ j, Signs p11515 (bank11515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11516 := params 27
abbrev ray11516 := rays 27
def bank11516 : Fin 2 → Cell := twoBank p11516 ray11516
theorem signs11516 : ∀ j, Signs p11516 (bank11516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11517 := params 28
abbrev ray11517 := rays 28
def bank11517 : Fin 2 → Cell := twoBank p11517 ray11517
theorem signs11517 : ∀ j, Signs p11517 (bank11517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11518 := params 29
abbrev ray11518 := rays 29
def bank11518 : Fin 2 → Cell := twoBank p11518 ray11518
theorem signs11518 : ∀ j, Signs p11518 (bank11518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11519 := params 30
abbrev ray11519 := rays 30
def bank11519 : Fin 2 → Cell := twoBank p11519 ray11519
theorem signs11519 : ∀ j, Signs p11519 (bank11519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11520 := params 31
abbrev ray11520 := rays 31
def bank11520 : Fin 2 → Cell := twoBank p11520 ray11520
theorem signs11520 : ∀ j, Signs p11520 (bank11520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11489_11520
