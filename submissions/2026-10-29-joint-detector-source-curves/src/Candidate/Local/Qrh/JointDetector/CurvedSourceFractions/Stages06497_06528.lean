/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06497_06528
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98625139781907,98624848324988,98624556845333,98624265342942,98623973817816,98623682269956,98623390699363,98623099106037,98622807489980,98622515851192,98622224189674,98621932505427,98621640798452,98621349068749,98621057316320,98620765541165,98620473743285,98620181922681,98619890079354,98619598213304,98619306324533,98619014413041,98618722478829,98618430521898,98618138542249,98617846539883,98617554514800,98617262467001,98616970396487,98616678303259,98616386187318,98616094048665,98615801887300]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6496+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6497 := params 0
abbrev ray6497 := rays 0
def bank6497 : Fin 2 → Cell := twoBank p6497 ray6497
theorem signs6497 : ∀ j, Signs p6497 (bank6497 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6498 := params 1
abbrev ray6498 := rays 1
def bank6498 : Fin 2 → Cell := twoBank p6498 ray6498
theorem signs6498 : ∀ j, Signs p6498 (bank6498 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6499 := params 2
abbrev ray6499 := rays 2
def bank6499 : Fin 2 → Cell := twoBank p6499 ray6499
theorem signs6499 : ∀ j, Signs p6499 (bank6499 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6500 := params 3
abbrev ray6500 := rays 3
def bank6500 : Fin 2 → Cell := twoBank p6500 ray6500
theorem signs6500 : ∀ j, Signs p6500 (bank6500 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6501 := params 4
abbrev ray6501 := rays 4
def bank6501 : Fin 2 → Cell := twoBank p6501 ray6501
theorem signs6501 : ∀ j, Signs p6501 (bank6501 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6502 := params 5
abbrev ray6502 := rays 5
def bank6502 : Fin 2 → Cell := twoBank p6502 ray6502
theorem signs6502 : ∀ j, Signs p6502 (bank6502 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6503 := params 6
abbrev ray6503 := rays 6
def bank6503 : Fin 2 → Cell := twoBank p6503 ray6503
theorem signs6503 : ∀ j, Signs p6503 (bank6503 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6504 := params 7
abbrev ray6504 := rays 7
def bank6504 : Fin 2 → Cell := twoBank p6504 ray6504
theorem signs6504 : ∀ j, Signs p6504 (bank6504 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6505 := params 8
abbrev ray6505 := rays 8
def bank6505 : Fin 2 → Cell := twoBank p6505 ray6505
theorem signs6505 : ∀ j, Signs p6505 (bank6505 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6506 := params 9
abbrev ray6506 := rays 9
def bank6506 : Fin 2 → Cell := twoBank p6506 ray6506
theorem signs6506 : ∀ j, Signs p6506 (bank6506 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6507 := params 10
abbrev ray6507 := rays 10
def bank6507 : Fin 2 → Cell := twoBank p6507 ray6507
theorem signs6507 : ∀ j, Signs p6507 (bank6507 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6508 := params 11
abbrev ray6508 := rays 11
def bank6508 : Fin 2 → Cell := twoBank p6508 ray6508
theorem signs6508 : ∀ j, Signs p6508 (bank6508 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6509 := params 12
abbrev ray6509 := rays 12
def bank6509 : Fin 2 → Cell := twoBank p6509 ray6509
theorem signs6509 : ∀ j, Signs p6509 (bank6509 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6510 := params 13
abbrev ray6510 := rays 13
def bank6510 : Fin 2 → Cell := twoBank p6510 ray6510
theorem signs6510 : ∀ j, Signs p6510 (bank6510 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6511 := params 14
abbrev ray6511 := rays 14
def bank6511 : Fin 2 → Cell := twoBank p6511 ray6511
theorem signs6511 : ∀ j, Signs p6511 (bank6511 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6512 := params 15
abbrev ray6512 := rays 15
def bank6512 : Fin 2 → Cell := twoBank p6512 ray6512
theorem signs6512 : ∀ j, Signs p6512 (bank6512 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6513 := params 16
abbrev ray6513 := rays 16
def bank6513 : Fin 2 → Cell := twoBank p6513 ray6513
theorem signs6513 : ∀ j, Signs p6513 (bank6513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6514 := params 17
abbrev ray6514 := rays 17
def bank6514 : Fin 2 → Cell := twoBank p6514 ray6514
theorem signs6514 : ∀ j, Signs p6514 (bank6514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6515 := params 18
abbrev ray6515 := rays 18
def bank6515 : Fin 2 → Cell := twoBank p6515 ray6515
theorem signs6515 : ∀ j, Signs p6515 (bank6515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6516 := params 19
abbrev ray6516 := rays 19
def bank6516 : Fin 2 → Cell := twoBank p6516 ray6516
theorem signs6516 : ∀ j, Signs p6516 (bank6516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6517 := params 20
abbrev ray6517 := rays 20
def bank6517 : Fin 2 → Cell := twoBank p6517 ray6517
theorem signs6517 : ∀ j, Signs p6517 (bank6517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6518 := params 21
abbrev ray6518 := rays 21
def bank6518 : Fin 2 → Cell := twoBank p6518 ray6518
theorem signs6518 : ∀ j, Signs p6518 (bank6518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6519 := params 22
abbrev ray6519 := rays 22
def bank6519 : Fin 2 → Cell := twoBank p6519 ray6519
theorem signs6519 : ∀ j, Signs p6519 (bank6519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6520 := params 23
abbrev ray6520 := rays 23
def bank6520 : Fin 2 → Cell := twoBank p6520 ray6520
theorem signs6520 : ∀ j, Signs p6520 (bank6520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6521 := params 24
abbrev ray6521 := rays 24
def bank6521 : Fin 2 → Cell := twoBank p6521 ray6521
theorem signs6521 : ∀ j, Signs p6521 (bank6521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6522 := params 25
abbrev ray6522 := rays 25
def bank6522 : Fin 2 → Cell := twoBank p6522 ray6522
theorem signs6522 : ∀ j, Signs p6522 (bank6522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6523 := params 26
abbrev ray6523 := rays 26
def bank6523 : Fin 2 → Cell := twoBank p6523 ray6523
theorem signs6523 : ∀ j, Signs p6523 (bank6523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6524 := params 27
abbrev ray6524 := rays 27
def bank6524 : Fin 2 → Cell := twoBank p6524 ray6524
theorem signs6524 : ∀ j, Signs p6524 (bank6524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6525 := params 28
abbrev ray6525 := rays 28
def bank6525 : Fin 2 → Cell := twoBank p6525 ray6525
theorem signs6525 : ∀ j, Signs p6525 (bank6525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6526 := params 29
abbrev ray6526 := rays 29
def bank6526 : Fin 2 → Cell := twoBank p6526 ray6526
theorem signs6526 : ∀ j, Signs p6526 (bank6526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6527 := params 30
abbrev ray6527 := rays 30
def bank6527 : Fin 2 → Cell := twoBank p6527 ray6527
theorem signs6527 : ∀ j, Signs p6527 (bank6527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6528 := params 31
abbrev ray6528 := rays 31
def bank6528 : Fin 2 → Cell := twoBank p6528 ray6528
theorem signs6528 : ∀ j, Signs p6528 (bank6528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06497_06528
