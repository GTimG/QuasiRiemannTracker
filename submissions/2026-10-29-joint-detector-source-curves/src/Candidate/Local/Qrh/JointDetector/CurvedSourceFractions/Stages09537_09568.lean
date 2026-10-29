/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09537_09568
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97637665212062,97637308073037,97636950913411,97636593733185,97636236532360,97635879310936,97635522068913,97635164806292,97634807523074,97634450219259,97634092894848,97633735549842,97633378184241,97633020798046,97632663391257,97632305963875,97631948515900,97631591047333,97631233558175,97630876048426,97630518518086,97630160967157,97629803395639,97629445803532,97629088190837,97628730557555,97628372903686,97628015229231,97627657534190,97627299818564,97626942082354,97626584325560,97626226548183]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9536+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9537 := params 0
abbrev ray9537 := rays 0
def bank9537 : Fin 2 → Cell := twoBank p9537 ray9537
theorem signs9537 : ∀ j, Signs p9537 (bank9537 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9538 := params 1
abbrev ray9538 := rays 1
def bank9538 : Fin 2 → Cell := twoBank p9538 ray9538
theorem signs9538 : ∀ j, Signs p9538 (bank9538 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9539 := params 2
abbrev ray9539 := rays 2
def bank9539 : Fin 2 → Cell := twoBank p9539 ray9539
theorem signs9539 : ∀ j, Signs p9539 (bank9539 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9540 := params 3
abbrev ray9540 := rays 3
def bank9540 : Fin 2 → Cell := twoBank p9540 ray9540
theorem signs9540 : ∀ j, Signs p9540 (bank9540 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9541 := params 4
abbrev ray9541 := rays 4
def bank9541 : Fin 2 → Cell := twoBank p9541 ray9541
theorem signs9541 : ∀ j, Signs p9541 (bank9541 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9542 := params 5
abbrev ray9542 := rays 5
def bank9542 : Fin 2 → Cell := twoBank p9542 ray9542
theorem signs9542 : ∀ j, Signs p9542 (bank9542 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9543 := params 6
abbrev ray9543 := rays 6
def bank9543 : Fin 2 → Cell := twoBank p9543 ray9543
theorem signs9543 : ∀ j, Signs p9543 (bank9543 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9544 := params 7
abbrev ray9544 := rays 7
def bank9544 : Fin 2 → Cell := twoBank p9544 ray9544
theorem signs9544 : ∀ j, Signs p9544 (bank9544 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9545 := params 8
abbrev ray9545 := rays 8
def bank9545 : Fin 2 → Cell := twoBank p9545 ray9545
theorem signs9545 : ∀ j, Signs p9545 (bank9545 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9546 := params 9
abbrev ray9546 := rays 9
def bank9546 : Fin 2 → Cell := twoBank p9546 ray9546
theorem signs9546 : ∀ j, Signs p9546 (bank9546 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9547 := params 10
abbrev ray9547 := rays 10
def bank9547 : Fin 2 → Cell := twoBank p9547 ray9547
theorem signs9547 : ∀ j, Signs p9547 (bank9547 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9548 := params 11
abbrev ray9548 := rays 11
def bank9548 : Fin 2 → Cell := twoBank p9548 ray9548
theorem signs9548 : ∀ j, Signs p9548 (bank9548 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9549 := params 12
abbrev ray9549 := rays 12
def bank9549 : Fin 2 → Cell := twoBank p9549 ray9549
theorem signs9549 : ∀ j, Signs p9549 (bank9549 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9550 := params 13
abbrev ray9550 := rays 13
def bank9550 : Fin 2 → Cell := twoBank p9550 ray9550
theorem signs9550 : ∀ j, Signs p9550 (bank9550 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9551 := params 14
abbrev ray9551 := rays 14
def bank9551 : Fin 2 → Cell := twoBank p9551 ray9551
theorem signs9551 : ∀ j, Signs p9551 (bank9551 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9552 := params 15
abbrev ray9552 := rays 15
def bank9552 : Fin 2 → Cell := twoBank p9552 ray9552
theorem signs9552 : ∀ j, Signs p9552 (bank9552 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9553 := params 16
abbrev ray9553 := rays 16
def bank9553 : Fin 2 → Cell := twoBank p9553 ray9553
theorem signs9553 : ∀ j, Signs p9553 (bank9553 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9554 := params 17
abbrev ray9554 := rays 17
def bank9554 : Fin 2 → Cell := twoBank p9554 ray9554
theorem signs9554 : ∀ j, Signs p9554 (bank9554 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9555 := params 18
abbrev ray9555 := rays 18
def bank9555 : Fin 2 → Cell := twoBank p9555 ray9555
theorem signs9555 : ∀ j, Signs p9555 (bank9555 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9556 := params 19
abbrev ray9556 := rays 19
def bank9556 : Fin 2 → Cell := twoBank p9556 ray9556
theorem signs9556 : ∀ j, Signs p9556 (bank9556 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9557 := params 20
abbrev ray9557 := rays 20
def bank9557 : Fin 2 → Cell := twoBank p9557 ray9557
theorem signs9557 : ∀ j, Signs p9557 (bank9557 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9558 := params 21
abbrev ray9558 := rays 21
def bank9558 : Fin 2 → Cell := twoBank p9558 ray9558
theorem signs9558 : ∀ j, Signs p9558 (bank9558 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9559 := params 22
abbrev ray9559 := rays 22
def bank9559 : Fin 2 → Cell := twoBank p9559 ray9559
theorem signs9559 : ∀ j, Signs p9559 (bank9559 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9560 := params 23
abbrev ray9560 := rays 23
def bank9560 : Fin 2 → Cell := twoBank p9560 ray9560
theorem signs9560 : ∀ j, Signs p9560 (bank9560 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9561 := params 24
abbrev ray9561 := rays 24
def bank9561 : Fin 2 → Cell := twoBank p9561 ray9561
theorem signs9561 : ∀ j, Signs p9561 (bank9561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9562 := params 25
abbrev ray9562 := rays 25
def bank9562 : Fin 2 → Cell := twoBank p9562 ray9562
theorem signs9562 : ∀ j, Signs p9562 (bank9562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9563 := params 26
abbrev ray9563 := rays 26
def bank9563 : Fin 2 → Cell := twoBank p9563 ray9563
theorem signs9563 : ∀ j, Signs p9563 (bank9563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9564 := params 27
abbrev ray9564 := rays 27
def bank9564 : Fin 2 → Cell := twoBank p9564 ray9564
theorem signs9564 : ∀ j, Signs p9564 (bank9564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9565 := params 28
abbrev ray9565 := rays 28
def bank9565 : Fin 2 → Cell := twoBank p9565 ray9565
theorem signs9565 : ∀ j, Signs p9565 (bank9565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9566 := params 29
abbrev ray9566 := rays 29
def bank9566 : Fin 2 → Cell := twoBank p9566 ray9566
theorem signs9566 : ∀ j, Signs p9566 (bank9566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9567 := params 30
abbrev ray9567 := rays 30
def bank9567 : Fin 2 → Cell := twoBank p9567 ray9567
theorem signs9567 : ∀ j, Signs p9567 (bank9567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9568 := params 31
abbrev ray9568 := rays 31
def bank9568 : Fin 2 → Cell := twoBank p9568 ray9568
theorem signs9568 : ∀ j, Signs p9568 (bank9568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09537_09568
