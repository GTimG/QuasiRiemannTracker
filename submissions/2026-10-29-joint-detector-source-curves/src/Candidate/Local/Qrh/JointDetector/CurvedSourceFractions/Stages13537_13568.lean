/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13537_13568
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96050591505580,96050157830073,96049724138259,96049290430137,96048856705708,96048422964972,96047989207929,96047555434579,96047121644923,96046687838960,96046254016691,96045820178117,96045386323237,96044952452052,96044518564562,96044084660767,96043650740667,96043216804263,96042782851554,96042348882541,96041914897225,96041480895605,96041046877682,96040612843455,96040178792926,96039744726094,96039310642959,96038876543522,96038442427783,96038008295742,96037574147400,96037139982756,96036705801811]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13536+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13537 := params 0
abbrev ray13537 := rays 0
def bank13537 : Fin 1 → Cell := oneBank p13537 ray13537
theorem signs13537 : ∀ j, Signs p13537 (bank13537 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13538 := params 1
abbrev ray13538 := rays 1
def bank13538 : Fin 1 → Cell := oneBank p13538 ray13538
theorem signs13538 : ∀ j, Signs p13538 (bank13538 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13539 := params 2
abbrev ray13539 := rays 2
def bank13539 : Fin 1 → Cell := oneBank p13539 ray13539
theorem signs13539 : ∀ j, Signs p13539 (bank13539 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13540 := params 3
abbrev ray13540 := rays 3
def bank13540 : Fin 1 → Cell := oneBank p13540 ray13540
theorem signs13540 : ∀ j, Signs p13540 (bank13540 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13541 := params 4
abbrev ray13541 := rays 4
def bank13541 : Fin 1 → Cell := oneBank p13541 ray13541
theorem signs13541 : ∀ j, Signs p13541 (bank13541 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13542 := params 5
abbrev ray13542 := rays 5
def bank13542 : Fin 1 → Cell := oneBank p13542 ray13542
theorem signs13542 : ∀ j, Signs p13542 (bank13542 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13543 := params 6
abbrev ray13543 := rays 6
def bank13543 : Fin 1 → Cell := oneBank p13543 ray13543
theorem signs13543 : ∀ j, Signs p13543 (bank13543 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13544 := params 7
abbrev ray13544 := rays 7
def bank13544 : Fin 1 → Cell := oneBank p13544 ray13544
theorem signs13544 : ∀ j, Signs p13544 (bank13544 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13545 := params 8
abbrev ray13545 := rays 8
def bank13545 : Fin 1 → Cell := oneBank p13545 ray13545
theorem signs13545 : ∀ j, Signs p13545 (bank13545 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13546 := params 9
abbrev ray13546 := rays 9
def bank13546 : Fin 1 → Cell := oneBank p13546 ray13546
theorem signs13546 : ∀ j, Signs p13546 (bank13546 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13547 := params 10
abbrev ray13547 := rays 10
def bank13547 : Fin 1 → Cell := oneBank p13547 ray13547
theorem signs13547 : ∀ j, Signs p13547 (bank13547 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13548 := params 11
abbrev ray13548 := rays 11
def bank13548 : Fin 1 → Cell := oneBank p13548 ray13548
theorem signs13548 : ∀ j, Signs p13548 (bank13548 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13549 := params 12
abbrev ray13549 := rays 12
def bank13549 : Fin 1 → Cell := oneBank p13549 ray13549
theorem signs13549 : ∀ j, Signs p13549 (bank13549 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13550 := params 13
abbrev ray13550 := rays 13
def bank13550 : Fin 1 → Cell := oneBank p13550 ray13550
theorem signs13550 : ∀ j, Signs p13550 (bank13550 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13551 := params 14
abbrev ray13551 := rays 14
def bank13551 : Fin 1 → Cell := oneBank p13551 ray13551
theorem signs13551 : ∀ j, Signs p13551 (bank13551 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13552 := params 15
abbrev ray13552 := rays 15
def bank13552 : Fin 1 → Cell := oneBank p13552 ray13552
theorem signs13552 : ∀ j, Signs p13552 (bank13552 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13553 := params 16
abbrev ray13553 := rays 16
def bank13553 : Fin 1 → Cell := oneBank p13553 ray13553
theorem signs13553 : ∀ j, Signs p13553 (bank13553 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13554 := params 17
abbrev ray13554 := rays 17
def bank13554 : Fin 1 → Cell := oneBank p13554 ray13554
theorem signs13554 : ∀ j, Signs p13554 (bank13554 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13555 := params 18
abbrev ray13555 := rays 18
def bank13555 : Fin 1 → Cell := oneBank p13555 ray13555
theorem signs13555 : ∀ j, Signs p13555 (bank13555 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13556 := params 19
abbrev ray13556 := rays 19
def bank13556 : Fin 1 → Cell := oneBank p13556 ray13556
theorem signs13556 : ∀ j, Signs p13556 (bank13556 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13557 := params 20
abbrev ray13557 := rays 20
def bank13557 : Fin 1 → Cell := oneBank p13557 ray13557
theorem signs13557 : ∀ j, Signs p13557 (bank13557 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13558 := params 21
abbrev ray13558 := rays 21
def bank13558 : Fin 1 → Cell := oneBank p13558 ray13558
theorem signs13558 : ∀ j, Signs p13558 (bank13558 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13559 := params 22
abbrev ray13559 := rays 22
def bank13559 : Fin 1 → Cell := oneBank p13559 ray13559
theorem signs13559 : ∀ j, Signs p13559 (bank13559 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13560 := params 23
abbrev ray13560 := rays 23
def bank13560 : Fin 1 → Cell := oneBank p13560 ray13560
theorem signs13560 : ∀ j, Signs p13560 (bank13560 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13561 := params 24
abbrev ray13561 := rays 24
def bank13561 : Fin 1 → Cell := oneBank p13561 ray13561
theorem signs13561 : ∀ j, Signs p13561 (bank13561 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13562 := params 25
abbrev ray13562 := rays 25
def bank13562 : Fin 1 → Cell := oneBank p13562 ray13562
theorem signs13562 : ∀ j, Signs p13562 (bank13562 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13563 := params 26
abbrev ray13563 := rays 26
def bank13563 : Fin 1 → Cell := oneBank p13563 ray13563
theorem signs13563 : ∀ j, Signs p13563 (bank13563 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13564 := params 27
abbrev ray13564 := rays 27
def bank13564 : Fin 1 → Cell := oneBank p13564 ray13564
theorem signs13564 : ∀ j, Signs p13564 (bank13564 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13565 := params 28
abbrev ray13565 := rays 28
def bank13565 : Fin 1 → Cell := oneBank p13565 ray13565
theorem signs13565 : ∀ j, Signs p13565 (bank13565 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13566 := params 29
abbrev ray13566 := rays 29
def bank13566 : Fin 1 → Cell := oneBank p13566 ray13566
theorem signs13566 : ∀ j, Signs p13566 (bank13566 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13567 := params 30
abbrev ray13567 := rays 30
def bank13567 : Fin 1 → Cell := oneBank p13567 ray13567
theorem signs13567 : ∀ j, Signs p13567 (bank13567 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13568 := params 31
abbrev ray13568 := rays 31
def bank13568 : Fin 1 → Cell := oneBank p13568 ray13568
theorem signs13568 : ∀ j, Signs p13568 (bank13568 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13537_13568
