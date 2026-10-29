/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05537_05568
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98894323469934,98894054240057,98893784986595,98893515709549,98893246408920,98892977084709,98892707736916,98892438365543,98892168970591,98891899552061,98891630109953,98891360644269,98891091155009,98890821642175,98890552105767,98890282545786,98890012962233,98889743355109,98889473724415,98889204070152,98888934392321,98888664690923,98888394965959,98888125217430,98887855445336,98887585649679,98887315830459,98887045987678,98886776121336,98886506231435,98886236317975,98885966380957,98885696420382]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5536+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5537 := params 0
abbrev ray5537 := rays 0
def bank5537 : Fin 2 → Cell := twoBank p5537 ray5537
theorem signs5537 : ∀ j, Signs p5537 (bank5537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5538 := params 1
abbrev ray5538 := rays 1
def bank5538 : Fin 2 → Cell := twoBank p5538 ray5538
theorem signs5538 : ∀ j, Signs p5538 (bank5538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5539 := params 2
abbrev ray5539 := rays 2
def bank5539 : Fin 2 → Cell := twoBank p5539 ray5539
theorem signs5539 : ∀ j, Signs p5539 (bank5539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5540 := params 3
abbrev ray5540 := rays 3
def bank5540 : Fin 2 → Cell := twoBank p5540 ray5540
theorem signs5540 : ∀ j, Signs p5540 (bank5540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5541 := params 4
abbrev ray5541 := rays 4
def bank5541 : Fin 2 → Cell := twoBank p5541 ray5541
theorem signs5541 : ∀ j, Signs p5541 (bank5541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5542 := params 5
abbrev ray5542 := rays 5
def bank5542 : Fin 2 → Cell := twoBank p5542 ray5542
theorem signs5542 : ∀ j, Signs p5542 (bank5542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5543 := params 6
abbrev ray5543 := rays 6
def bank5543 : Fin 2 → Cell := twoBank p5543 ray5543
theorem signs5543 : ∀ j, Signs p5543 (bank5543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5544 := params 7
abbrev ray5544 := rays 7
def bank5544 : Fin 2 → Cell := twoBank p5544 ray5544
theorem signs5544 : ∀ j, Signs p5544 (bank5544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5545 := params 8
abbrev ray5545 := rays 8
def bank5545 : Fin 2 → Cell := twoBank p5545 ray5545
theorem signs5545 : ∀ j, Signs p5545 (bank5545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5546 := params 9
abbrev ray5546 := rays 9
def bank5546 : Fin 2 → Cell := twoBank p5546 ray5546
theorem signs5546 : ∀ j, Signs p5546 (bank5546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5547 := params 10
abbrev ray5547 := rays 10
def bank5547 : Fin 2 → Cell := twoBank p5547 ray5547
theorem signs5547 : ∀ j, Signs p5547 (bank5547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5548 := params 11
abbrev ray5548 := rays 11
def bank5548 : Fin 2 → Cell := twoBank p5548 ray5548
theorem signs5548 : ∀ j, Signs p5548 (bank5548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5549 := params 12
abbrev ray5549 := rays 12
def bank5549 : Fin 2 → Cell := twoBank p5549 ray5549
theorem signs5549 : ∀ j, Signs p5549 (bank5549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5550 := params 13
abbrev ray5550 := rays 13
def bank5550 : Fin 2 → Cell := twoBank p5550 ray5550
theorem signs5550 : ∀ j, Signs p5550 (bank5550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5551 := params 14
abbrev ray5551 := rays 14
def bank5551 : Fin 2 → Cell := twoBank p5551 ray5551
theorem signs5551 : ∀ j, Signs p5551 (bank5551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5552 := params 15
abbrev ray5552 := rays 15
def bank5552 : Fin 2 → Cell := twoBank p5552 ray5552
theorem signs5552 : ∀ j, Signs p5552 (bank5552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5553 := params 16
abbrev ray5553 := rays 16
def bank5553 : Fin 2 → Cell := twoBank p5553 ray5553
theorem signs5553 : ∀ j, Signs p5553 (bank5553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5554 := params 17
abbrev ray5554 := rays 17
def bank5554 : Fin 2 → Cell := twoBank p5554 ray5554
theorem signs5554 : ∀ j, Signs p5554 (bank5554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5555 := params 18
abbrev ray5555 := rays 18
def bank5555 : Fin 2 → Cell := twoBank p5555 ray5555
theorem signs5555 : ∀ j, Signs p5555 (bank5555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5556 := params 19
abbrev ray5556 := rays 19
def bank5556 : Fin 2 → Cell := twoBank p5556 ray5556
theorem signs5556 : ∀ j, Signs p5556 (bank5556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5557 := params 20
abbrev ray5557 := rays 20
def bank5557 : Fin 2 → Cell := twoBank p5557 ray5557
theorem signs5557 : ∀ j, Signs p5557 (bank5557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5558 := params 21
abbrev ray5558 := rays 21
def bank5558 : Fin 2 → Cell := twoBank p5558 ray5558
theorem signs5558 : ∀ j, Signs p5558 (bank5558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5559 := params 22
abbrev ray5559 := rays 22
def bank5559 : Fin 2 → Cell := twoBank p5559 ray5559
theorem signs5559 : ∀ j, Signs p5559 (bank5559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5560 := params 23
abbrev ray5560 := rays 23
def bank5560 : Fin 2 → Cell := twoBank p5560 ray5560
theorem signs5560 : ∀ j, Signs p5560 (bank5560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5561 := params 24
abbrev ray5561 := rays 24
def bank5561 : Fin 2 → Cell := twoBank p5561 ray5561
theorem signs5561 : ∀ j, Signs p5561 (bank5561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5562 := params 25
abbrev ray5562 := rays 25
def bank5562 : Fin 2 → Cell := twoBank p5562 ray5562
theorem signs5562 : ∀ j, Signs p5562 (bank5562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5563 := params 26
abbrev ray5563 := rays 26
def bank5563 : Fin 2 → Cell := twoBank p5563 ray5563
theorem signs5563 : ∀ j, Signs p5563 (bank5563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5564 := params 27
abbrev ray5564 := rays 27
def bank5564 : Fin 2 → Cell := twoBank p5564 ray5564
theorem signs5564 : ∀ j, Signs p5564 (bank5564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5565 := params 28
abbrev ray5565 := rays 28
def bank5565 : Fin 2 → Cell := twoBank p5565 ray5565
theorem signs5565 : ∀ j, Signs p5565 (bank5565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5566 := params 29
abbrev ray5566 := rays 29
def bank5566 : Fin 2 → Cell := twoBank p5566 ray5566
theorem signs5566 : ∀ j, Signs p5566 (bank5566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5567 := params 30
abbrev ray5567 := rays 30
def bank5567 : Fin 2 → Cell := twoBank p5567 ray5567
theorem signs5567 : ∀ j, Signs p5567 (bank5567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5568 := params 31
abbrev ray5568 := rays 31
def bank5568 : Fin 2 → Cell := twoBank p5568 ray5568
theorem signs5568 : ∀ j, Signs p5568 (bank5568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05537_05568
