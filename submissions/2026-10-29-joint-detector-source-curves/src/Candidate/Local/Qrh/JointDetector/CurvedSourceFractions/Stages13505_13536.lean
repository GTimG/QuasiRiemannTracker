/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13505_13536
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96064460509982,96064027356440,96063594186583,96063161000412,96062727797926,96062294579126,96061861344012,96061428092584,96060994824843,96060561540789,96060128240422,96059694923742,96059261590749,96058828241444,96058394875826,96057961493897,96057528095656,96057094681103,96056661250239,96056227803064,96055794339578,96055360859781,96054927363674,96054493851257,96054060322530,96053626777493,96053193216147,96052759638491,96052326044526,96051892434252,96051458807670,96051025164779,96050591505580]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13504+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13505 := params 0
abbrev ray13505 := rays 0
def bank13505 : Fin 1 → Cell := oneBank p13505 ray13505
theorem signs13505 : ∀ j, Signs p13505 (bank13505 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13506 := params 1
abbrev ray13506 := rays 1
def bank13506 : Fin 1 → Cell := oneBank p13506 ray13506
theorem signs13506 : ∀ j, Signs p13506 (bank13506 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13507 := params 2
abbrev ray13507 := rays 2
def bank13507 : Fin 1 → Cell := oneBank p13507 ray13507
theorem signs13507 : ∀ j, Signs p13507 (bank13507 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13508 := params 3
abbrev ray13508 := rays 3
def bank13508 : Fin 1 → Cell := oneBank p13508 ray13508
theorem signs13508 : ∀ j, Signs p13508 (bank13508 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13509 := params 4
abbrev ray13509 := rays 4
def bank13509 : Fin 1 → Cell := oneBank p13509 ray13509
theorem signs13509 : ∀ j, Signs p13509 (bank13509 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13510 := params 5
abbrev ray13510 := rays 5
def bank13510 : Fin 1 → Cell := oneBank p13510 ray13510
theorem signs13510 : ∀ j, Signs p13510 (bank13510 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13511 := params 6
abbrev ray13511 := rays 6
def bank13511 : Fin 1 → Cell := oneBank p13511 ray13511
theorem signs13511 : ∀ j, Signs p13511 (bank13511 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13512 := params 7
abbrev ray13512 := rays 7
def bank13512 : Fin 1 → Cell := oneBank p13512 ray13512
theorem signs13512 : ∀ j, Signs p13512 (bank13512 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13513 := params 8
abbrev ray13513 := rays 8
def bank13513 : Fin 1 → Cell := oneBank p13513 ray13513
theorem signs13513 : ∀ j, Signs p13513 (bank13513 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13514 := params 9
abbrev ray13514 := rays 9
def bank13514 : Fin 1 → Cell := oneBank p13514 ray13514
theorem signs13514 : ∀ j, Signs p13514 (bank13514 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13515 := params 10
abbrev ray13515 := rays 10
def bank13515 : Fin 1 → Cell := oneBank p13515 ray13515
theorem signs13515 : ∀ j, Signs p13515 (bank13515 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13516 := params 11
abbrev ray13516 := rays 11
def bank13516 : Fin 1 → Cell := oneBank p13516 ray13516
theorem signs13516 : ∀ j, Signs p13516 (bank13516 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13517 := params 12
abbrev ray13517 := rays 12
def bank13517 : Fin 1 → Cell := oneBank p13517 ray13517
theorem signs13517 : ∀ j, Signs p13517 (bank13517 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13518 := params 13
abbrev ray13518 := rays 13
def bank13518 : Fin 1 → Cell := oneBank p13518 ray13518
theorem signs13518 : ∀ j, Signs p13518 (bank13518 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13519 := params 14
abbrev ray13519 := rays 14
def bank13519 : Fin 1 → Cell := oneBank p13519 ray13519
theorem signs13519 : ∀ j, Signs p13519 (bank13519 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13520 := params 15
abbrev ray13520 := rays 15
def bank13520 : Fin 1 → Cell := oneBank p13520 ray13520
theorem signs13520 : ∀ j, Signs p13520 (bank13520 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13521 := params 16
abbrev ray13521 := rays 16
def bank13521 : Fin 1 → Cell := oneBank p13521 ray13521
theorem signs13521 : ∀ j, Signs p13521 (bank13521 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13522 := params 17
abbrev ray13522 := rays 17
def bank13522 : Fin 1 → Cell := oneBank p13522 ray13522
theorem signs13522 : ∀ j, Signs p13522 (bank13522 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13523 := params 18
abbrev ray13523 := rays 18
def bank13523 : Fin 1 → Cell := oneBank p13523 ray13523
theorem signs13523 : ∀ j, Signs p13523 (bank13523 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13524 := params 19
abbrev ray13524 := rays 19
def bank13524 : Fin 1 → Cell := oneBank p13524 ray13524
theorem signs13524 : ∀ j, Signs p13524 (bank13524 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13525 := params 20
abbrev ray13525 := rays 20
def bank13525 : Fin 1 → Cell := oneBank p13525 ray13525
theorem signs13525 : ∀ j, Signs p13525 (bank13525 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13526 := params 21
abbrev ray13526 := rays 21
def bank13526 : Fin 1 → Cell := oneBank p13526 ray13526
theorem signs13526 : ∀ j, Signs p13526 (bank13526 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13527 := params 22
abbrev ray13527 := rays 22
def bank13527 : Fin 1 → Cell := oneBank p13527 ray13527
theorem signs13527 : ∀ j, Signs p13527 (bank13527 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13528 := params 23
abbrev ray13528 := rays 23
def bank13528 : Fin 1 → Cell := oneBank p13528 ray13528
theorem signs13528 : ∀ j, Signs p13528 (bank13528 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13529 := params 24
abbrev ray13529 := rays 24
def bank13529 : Fin 1 → Cell := oneBank p13529 ray13529
theorem signs13529 : ∀ j, Signs p13529 (bank13529 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13530 := params 25
abbrev ray13530 := rays 25
def bank13530 : Fin 1 → Cell := oneBank p13530 ray13530
theorem signs13530 : ∀ j, Signs p13530 (bank13530 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13531 := params 26
abbrev ray13531 := rays 26
def bank13531 : Fin 1 → Cell := oneBank p13531 ray13531
theorem signs13531 : ∀ j, Signs p13531 (bank13531 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13532 := params 27
abbrev ray13532 := rays 27
def bank13532 : Fin 1 → Cell := oneBank p13532 ray13532
theorem signs13532 : ∀ j, Signs p13532 (bank13532 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13533 := params 28
abbrev ray13533 := rays 28
def bank13533 : Fin 1 → Cell := oneBank p13533 ray13533
theorem signs13533 : ∀ j, Signs p13533 (bank13533 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13534 := params 29
abbrev ray13534 := rays 29
def bank13534 : Fin 1 → Cell := oneBank p13534 ray13534
theorem signs13534 : ∀ j, Signs p13534 (bank13534 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13535 := params 30
abbrev ray13535 := rays 30
def bank13535 : Fin 1 → Cell := oneBank p13535 ray13535
theorem signs13535 : ∀ j, Signs p13535 (bank13535 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13536 := params 31
abbrev ray13536 := rays 31
def bank13536 : Fin 1 → Cell := oneBank p13536 ray13536
theorem signs13536 : ∀ j, Signs p13536 (bank13536 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13505_13536
