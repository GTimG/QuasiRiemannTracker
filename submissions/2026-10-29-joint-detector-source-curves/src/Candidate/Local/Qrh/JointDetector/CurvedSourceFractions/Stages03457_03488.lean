/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03457_03488
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99401782235452,99401564264646,99401346268045,99401128245651,99400910197465,99400692123488,99400474023721,99400255898166,99400037746823,99399819569694,99399601366780,99399383138083,99399164883603,99398946603342,99398728297301,99398509965481,99398291607883,99398073224509,99397854815359,99397636380435,99397417919739,99397199433271,99396980921032,99396762383024,99396543819248,99396325229705,99396106614396,99395887973323,99395669306487,99395450613889,99395231895530,99395013151411,99394794381534]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3456+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3457 := params 0
abbrev ray3457 := rays 0
def bank3457 : Fin 2 → Cell := twoBank p3457 ray3457
theorem signs3457 : ∀ j, Signs p3457 (bank3457 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3458 := params 1
abbrev ray3458 := rays 1
def bank3458 : Fin 2 → Cell := twoBank p3458 ray3458
theorem signs3458 : ∀ j, Signs p3458 (bank3458 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3459 := params 2
abbrev ray3459 := rays 2
def bank3459 : Fin 2 → Cell := twoBank p3459 ray3459
theorem signs3459 : ∀ j, Signs p3459 (bank3459 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3460 := params 3
abbrev ray3460 := rays 3
def bank3460 : Fin 2 → Cell := twoBank p3460 ray3460
theorem signs3460 : ∀ j, Signs p3460 (bank3460 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3461 := params 4
abbrev ray3461 := rays 4
def bank3461 : Fin 2 → Cell := twoBank p3461 ray3461
theorem signs3461 : ∀ j, Signs p3461 (bank3461 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3462 := params 5
abbrev ray3462 := rays 5
def bank3462 : Fin 2 → Cell := twoBank p3462 ray3462
theorem signs3462 : ∀ j, Signs p3462 (bank3462 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3463 := params 6
abbrev ray3463 := rays 6
def bank3463 : Fin 2 → Cell := twoBank p3463 ray3463
theorem signs3463 : ∀ j, Signs p3463 (bank3463 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3464 := params 7
abbrev ray3464 := rays 7
def bank3464 : Fin 2 → Cell := twoBank p3464 ray3464
theorem signs3464 : ∀ j, Signs p3464 (bank3464 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3465 := params 8
abbrev ray3465 := rays 8
def bank3465 : Fin 2 → Cell := twoBank p3465 ray3465
theorem signs3465 : ∀ j, Signs p3465 (bank3465 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3466 := params 9
abbrev ray3466 := rays 9
def bank3466 : Fin 2 → Cell := twoBank p3466 ray3466
theorem signs3466 : ∀ j, Signs p3466 (bank3466 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3467 := params 10
abbrev ray3467 := rays 10
def bank3467 : Fin 2 → Cell := twoBank p3467 ray3467
theorem signs3467 : ∀ j, Signs p3467 (bank3467 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3468 := params 11
abbrev ray3468 := rays 11
def bank3468 : Fin 2 → Cell := twoBank p3468 ray3468
theorem signs3468 : ∀ j, Signs p3468 (bank3468 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3469 := params 12
abbrev ray3469 := rays 12
def bank3469 : Fin 2 → Cell := twoBank p3469 ray3469
theorem signs3469 : ∀ j, Signs p3469 (bank3469 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3470 := params 13
abbrev ray3470 := rays 13
def bank3470 : Fin 2 → Cell := twoBank p3470 ray3470
theorem signs3470 : ∀ j, Signs p3470 (bank3470 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3471 := params 14
abbrev ray3471 := rays 14
def bank3471 : Fin 2 → Cell := twoBank p3471 ray3471
theorem signs3471 : ∀ j, Signs p3471 (bank3471 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3472 := params 15
abbrev ray3472 := rays 15
def bank3472 : Fin 2 → Cell := twoBank p3472 ray3472
theorem signs3472 : ∀ j, Signs p3472 (bank3472 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3473 := params 16
abbrev ray3473 := rays 16
def bank3473 : Fin 2 → Cell := twoBank p3473 ray3473
theorem signs3473 : ∀ j, Signs p3473 (bank3473 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3474 := params 17
abbrev ray3474 := rays 17
def bank3474 : Fin 2 → Cell := twoBank p3474 ray3474
theorem signs3474 : ∀ j, Signs p3474 (bank3474 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3475 := params 18
abbrev ray3475 := rays 18
def bank3475 : Fin 2 → Cell := twoBank p3475 ray3475
theorem signs3475 : ∀ j, Signs p3475 (bank3475 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3476 := params 19
abbrev ray3476 := rays 19
def bank3476 : Fin 2 → Cell := twoBank p3476 ray3476
theorem signs3476 : ∀ j, Signs p3476 (bank3476 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3477 := params 20
abbrev ray3477 := rays 20
def bank3477 : Fin 2 → Cell := twoBank p3477 ray3477
theorem signs3477 : ∀ j, Signs p3477 (bank3477 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3478 := params 21
abbrev ray3478 := rays 21
def bank3478 : Fin 2 → Cell := twoBank p3478 ray3478
theorem signs3478 : ∀ j, Signs p3478 (bank3478 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3479 := params 22
abbrev ray3479 := rays 22
def bank3479 : Fin 2 → Cell := twoBank p3479 ray3479
theorem signs3479 : ∀ j, Signs p3479 (bank3479 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3480 := params 23
abbrev ray3480 := rays 23
def bank3480 : Fin 2 → Cell := twoBank p3480 ray3480
theorem signs3480 : ∀ j, Signs p3480 (bank3480 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3481 := params 24
abbrev ray3481 := rays 24
def bank3481 : Fin 2 → Cell := twoBank p3481 ray3481
theorem signs3481 : ∀ j, Signs p3481 (bank3481 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3482 := params 25
abbrev ray3482 := rays 25
def bank3482 : Fin 2 → Cell := twoBank p3482 ray3482
theorem signs3482 : ∀ j, Signs p3482 (bank3482 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3483 := params 26
abbrev ray3483 := rays 26
def bank3483 : Fin 2 → Cell := twoBank p3483 ray3483
theorem signs3483 : ∀ j, Signs p3483 (bank3483 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3484 := params 27
abbrev ray3484 := rays 27
def bank3484 : Fin 2 → Cell := twoBank p3484 ray3484
theorem signs3484 : ∀ j, Signs p3484 (bank3484 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3485 := params 28
abbrev ray3485 := rays 28
def bank3485 : Fin 2 → Cell := twoBank p3485 ray3485
theorem signs3485 : ∀ j, Signs p3485 (bank3485 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3486 := params 29
abbrev ray3486 := rays 29
def bank3486 : Fin 2 → Cell := twoBank p3486 ray3486
theorem signs3486 : ∀ j, Signs p3486 (bank3486 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3487 := params 30
abbrev ray3487 := rays 30
def bank3487 : Fin 2 → Cell := twoBank p3487 ray3487
theorem signs3487 : ∀ j, Signs p3487 (bank3487 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3488 := params 31
abbrev ray3488 := rays 31
def bank3488 : Fin 2 → Cell := twoBank p3488 ray3488
theorem signs3488 : ∀ j, Signs p3488 (bank3488 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03457_03488
