/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12513_12544
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96485976459687,96485560317337,96485144155846,96484727975214,96484311775441,96483895556528,96483479318475,96483063061283,96482646784952,96482230489482,96481814174874,96481397841128,96480981488245,96480565116225,96480148725068,96479732314775,96479315885346,96478899436782,96478482969083,96478066482249,96477649976281,96477233451179,96476816906944,96476400343576,96475983761075,96475567159442,96475150538677,96474733898781,96474317239754,96473900561597,96473483864309,96473067147892,96472650412345]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12512+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12513 := params 0
abbrev ray12513 := rays 0
def bank12513 : Fin 2 → Cell := twoBank p12513 ray12513
theorem signs12513 : ∀ j, Signs p12513 (bank12513 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12514 := params 1
abbrev ray12514 := rays 1
def bank12514 : Fin 2 → Cell := twoBank p12514 ray12514
theorem signs12514 : ∀ j, Signs p12514 (bank12514 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12515 := params 2
abbrev ray12515 := rays 2
def bank12515 : Fin 2 → Cell := twoBank p12515 ray12515
theorem signs12515 : ∀ j, Signs p12515 (bank12515 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12516 := params 3
abbrev ray12516 := rays 3
def bank12516 : Fin 2 → Cell := twoBank p12516 ray12516
theorem signs12516 : ∀ j, Signs p12516 (bank12516 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12517 := params 4
abbrev ray12517 := rays 4
def bank12517 : Fin 2 → Cell := twoBank p12517 ray12517
theorem signs12517 : ∀ j, Signs p12517 (bank12517 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12518 := params 5
abbrev ray12518 := rays 5
def bank12518 : Fin 2 → Cell := twoBank p12518 ray12518
theorem signs12518 : ∀ j, Signs p12518 (bank12518 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12519 := params 6
abbrev ray12519 := rays 6
def bank12519 : Fin 2 → Cell := twoBank p12519 ray12519
theorem signs12519 : ∀ j, Signs p12519 (bank12519 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12520 := params 7
abbrev ray12520 := rays 7
def bank12520 : Fin 2 → Cell := twoBank p12520 ray12520
theorem signs12520 : ∀ j, Signs p12520 (bank12520 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12521 := params 8
abbrev ray12521 := rays 8
def bank12521 : Fin 2 → Cell := twoBank p12521 ray12521
theorem signs12521 : ∀ j, Signs p12521 (bank12521 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12522 := params 9
abbrev ray12522 := rays 9
def bank12522 : Fin 2 → Cell := twoBank p12522 ray12522
theorem signs12522 : ∀ j, Signs p12522 (bank12522 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12523 := params 10
abbrev ray12523 := rays 10
def bank12523 : Fin 2 → Cell := twoBank p12523 ray12523
theorem signs12523 : ∀ j, Signs p12523 (bank12523 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12524 := params 11
abbrev ray12524 := rays 11
def bank12524 : Fin 2 → Cell := twoBank p12524 ray12524
theorem signs12524 : ∀ j, Signs p12524 (bank12524 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12525 := params 12
abbrev ray12525 := rays 12
def bank12525 : Fin 2 → Cell := twoBank p12525 ray12525
theorem signs12525 : ∀ j, Signs p12525 (bank12525 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12526 := params 13
abbrev ray12526 := rays 13
def bank12526 : Fin 2 → Cell := twoBank p12526 ray12526
theorem signs12526 : ∀ j, Signs p12526 (bank12526 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12527 := params 14
abbrev ray12527 := rays 14
def bank12527 : Fin 2 → Cell := twoBank p12527 ray12527
theorem signs12527 : ∀ j, Signs p12527 (bank12527 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12528 := params 15
abbrev ray12528 := rays 15
def bank12528 : Fin 2 → Cell := twoBank p12528 ray12528
theorem signs12528 : ∀ j, Signs p12528 (bank12528 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12529 := params 16
abbrev ray12529 := rays 16
def bank12529 : Fin 2 → Cell := twoBank p12529 ray12529
theorem signs12529 : ∀ j, Signs p12529 (bank12529 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12530 := params 17
abbrev ray12530 := rays 17
def bank12530 : Fin 2 → Cell := twoBank p12530 ray12530
theorem signs12530 : ∀ j, Signs p12530 (bank12530 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12531 := params 18
abbrev ray12531 := rays 18
def bank12531 : Fin 2 → Cell := twoBank p12531 ray12531
theorem signs12531 : ∀ j, Signs p12531 (bank12531 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12532 := params 19
abbrev ray12532 := rays 19
def bank12532 : Fin 2 → Cell := twoBank p12532 ray12532
theorem signs12532 : ∀ j, Signs p12532 (bank12532 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12533 := params 20
abbrev ray12533 := rays 20
def bank12533 : Fin 2 → Cell := twoBank p12533 ray12533
theorem signs12533 : ∀ j, Signs p12533 (bank12533 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12534 := params 21
abbrev ray12534 := rays 21
def bank12534 : Fin 2 → Cell := twoBank p12534 ray12534
theorem signs12534 : ∀ j, Signs p12534 (bank12534 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12535 := params 22
abbrev ray12535 := rays 22
def bank12535 : Fin 2 → Cell := twoBank p12535 ray12535
theorem signs12535 : ∀ j, Signs p12535 (bank12535 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12536 := params 23
abbrev ray12536 := rays 23
def bank12536 : Fin 2 → Cell := twoBank p12536 ray12536
theorem signs12536 : ∀ j, Signs p12536 (bank12536 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12537 := params 24
abbrev ray12537 := rays 24
def bank12537 : Fin 2 → Cell := twoBank p12537 ray12537
theorem signs12537 : ∀ j, Signs p12537 (bank12537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12538 := params 25
abbrev ray12538 := rays 25
def bank12538 : Fin 2 → Cell := twoBank p12538 ray12538
theorem signs12538 : ∀ j, Signs p12538 (bank12538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12539 := params 26
abbrev ray12539 := rays 26
def bank12539 : Fin 2 → Cell := twoBank p12539 ray12539
theorem signs12539 : ∀ j, Signs p12539 (bank12539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12540 := params 27
abbrev ray12540 := rays 27
def bank12540 : Fin 2 → Cell := twoBank p12540 ray12540
theorem signs12540 : ∀ j, Signs p12540 (bank12540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12541 := params 28
abbrev ray12541 := rays 28
def bank12541 : Fin 2 → Cell := twoBank p12541 ray12541
theorem signs12541 : ∀ j, Signs p12541 (bank12541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12542 := params 29
abbrev ray12542 := rays 29
def bank12542 : Fin 2 → Cell := twoBank p12542 ray12542
theorem signs12542 : ∀ j, Signs p12542 (bank12542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12543 := params 30
abbrev ray12543 := rays 30
def bank12543 : Fin 2 → Cell := twoBank p12543 ray12543
theorem signs12543 : ∀ j, Signs p12543 (bank12543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12544 := params 31
abbrev ray12544 := rays 31
def bank12544 : Fin 2 → Cell := twoBank p12544 ray12544
theorem signs12544 : ∀ j, Signs p12544 (bank12544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12513_12544
