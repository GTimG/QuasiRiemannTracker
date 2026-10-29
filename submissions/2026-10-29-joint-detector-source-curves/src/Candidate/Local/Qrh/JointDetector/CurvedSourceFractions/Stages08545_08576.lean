/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08545_08576
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97981702357603,97981365954188,97981029529557,97980693083710,97980356616649,97980020128373,97979683618884,97979347088182,97979010536267,97978673963141,97978337368804,97978000753257,97977664116500,97977327458534,97976990779360,97976654078978,97976317357389,97975980614593,97975643850592,97975307065386,97974970258975,97974633431361,97974296582543,97973959712523,97973622821301,97973285908878,97972948975255,97972612020432,97972275044410,97971938047189,97971601028770,97971263989154,97970926928341]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8544+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8545 := params 0
abbrev ray8545 := rays 0
def bank8545 : Fin 2 → Cell := twoBank p8545 ray8545
theorem signs8545 : ∀ j, Signs p8545 (bank8545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8546 := params 1
abbrev ray8546 := rays 1
def bank8546 : Fin 2 → Cell := twoBank p8546 ray8546
theorem signs8546 : ∀ j, Signs p8546 (bank8546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8547 := params 2
abbrev ray8547 := rays 2
def bank8547 : Fin 2 → Cell := twoBank p8547 ray8547
theorem signs8547 : ∀ j, Signs p8547 (bank8547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8548 := params 3
abbrev ray8548 := rays 3
def bank8548 : Fin 2 → Cell := twoBank p8548 ray8548
theorem signs8548 : ∀ j, Signs p8548 (bank8548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8549 := params 4
abbrev ray8549 := rays 4
def bank8549 : Fin 2 → Cell := twoBank p8549 ray8549
theorem signs8549 : ∀ j, Signs p8549 (bank8549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8550 := params 5
abbrev ray8550 := rays 5
def bank8550 : Fin 2 → Cell := twoBank p8550 ray8550
theorem signs8550 : ∀ j, Signs p8550 (bank8550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8551 := params 6
abbrev ray8551 := rays 6
def bank8551 : Fin 2 → Cell := twoBank p8551 ray8551
theorem signs8551 : ∀ j, Signs p8551 (bank8551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8552 := params 7
abbrev ray8552 := rays 7
def bank8552 : Fin 2 → Cell := twoBank p8552 ray8552
theorem signs8552 : ∀ j, Signs p8552 (bank8552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8553 := params 8
abbrev ray8553 := rays 8
def bank8553 : Fin 2 → Cell := twoBank p8553 ray8553
theorem signs8553 : ∀ j, Signs p8553 (bank8553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8554 := params 9
abbrev ray8554 := rays 9
def bank8554 : Fin 2 → Cell := twoBank p8554 ray8554
theorem signs8554 : ∀ j, Signs p8554 (bank8554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8555 := params 10
abbrev ray8555 := rays 10
def bank8555 : Fin 2 → Cell := twoBank p8555 ray8555
theorem signs8555 : ∀ j, Signs p8555 (bank8555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8556 := params 11
abbrev ray8556 := rays 11
def bank8556 : Fin 2 → Cell := twoBank p8556 ray8556
theorem signs8556 : ∀ j, Signs p8556 (bank8556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8557 := params 12
abbrev ray8557 := rays 12
def bank8557 : Fin 2 → Cell := twoBank p8557 ray8557
theorem signs8557 : ∀ j, Signs p8557 (bank8557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8558 := params 13
abbrev ray8558 := rays 13
def bank8558 : Fin 2 → Cell := twoBank p8558 ray8558
theorem signs8558 : ∀ j, Signs p8558 (bank8558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8559 := params 14
abbrev ray8559 := rays 14
def bank8559 : Fin 2 → Cell := twoBank p8559 ray8559
theorem signs8559 : ∀ j, Signs p8559 (bank8559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8560 := params 15
abbrev ray8560 := rays 15
def bank8560 : Fin 2 → Cell := twoBank p8560 ray8560
theorem signs8560 : ∀ j, Signs p8560 (bank8560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8561 := params 16
abbrev ray8561 := rays 16
def bank8561 : Fin 2 → Cell := twoBank p8561 ray8561
theorem signs8561 : ∀ j, Signs p8561 (bank8561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8562 := params 17
abbrev ray8562 := rays 17
def bank8562 : Fin 2 → Cell := twoBank p8562 ray8562
theorem signs8562 : ∀ j, Signs p8562 (bank8562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8563 := params 18
abbrev ray8563 := rays 18
def bank8563 : Fin 2 → Cell := twoBank p8563 ray8563
theorem signs8563 : ∀ j, Signs p8563 (bank8563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8564 := params 19
abbrev ray8564 := rays 19
def bank8564 : Fin 2 → Cell := twoBank p8564 ray8564
theorem signs8564 : ∀ j, Signs p8564 (bank8564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8565 := params 20
abbrev ray8565 := rays 20
def bank8565 : Fin 2 → Cell := twoBank p8565 ray8565
theorem signs8565 : ∀ j, Signs p8565 (bank8565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8566 := params 21
abbrev ray8566 := rays 21
def bank8566 : Fin 2 → Cell := twoBank p8566 ray8566
theorem signs8566 : ∀ j, Signs p8566 (bank8566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8567 := params 22
abbrev ray8567 := rays 22
def bank8567 : Fin 2 → Cell := twoBank p8567 ray8567
theorem signs8567 : ∀ j, Signs p8567 (bank8567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8568 := params 23
abbrev ray8568 := rays 23
def bank8568 : Fin 2 → Cell := twoBank p8568 ray8568
theorem signs8568 : ∀ j, Signs p8568 (bank8568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8569 := params 24
abbrev ray8569 := rays 24
def bank8569 : Fin 2 → Cell := twoBank p8569 ray8569
theorem signs8569 : ∀ j, Signs p8569 (bank8569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8570 := params 25
abbrev ray8570 := rays 25
def bank8570 : Fin 2 → Cell := twoBank p8570 ray8570
theorem signs8570 : ∀ j, Signs p8570 (bank8570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8571 := params 26
abbrev ray8571 := rays 26
def bank8571 : Fin 2 → Cell := twoBank p8571 ray8571
theorem signs8571 : ∀ j, Signs p8571 (bank8571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8572 := params 27
abbrev ray8572 := rays 27
def bank8572 : Fin 2 → Cell := twoBank p8572 ray8572
theorem signs8572 : ∀ j, Signs p8572 (bank8572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8573 := params 28
abbrev ray8573 := rays 28
def bank8573 : Fin 2 → Cell := twoBank p8573 ray8573
theorem signs8573 : ∀ j, Signs p8573 (bank8573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8574 := params 29
abbrev ray8574 := rays 29
def bank8574 : Fin 2 → Cell := twoBank p8574 ray8574
theorem signs8574 : ∀ j, Signs p8574 (bank8574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8575 := params 30
abbrev ray8575 := rays 30
def bank8575 : Fin 2 → Cell := twoBank p8575 ray8575
theorem signs8575 : ∀ j, Signs p8575 (bank8575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8576 := params 31
abbrev ray8576 := rays 31
def bank8576 : Fin 2 → Cell := twoBank p8576 ray8576
theorem signs8576 : ∀ j, Signs p8576 (bank8576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08545_08576
