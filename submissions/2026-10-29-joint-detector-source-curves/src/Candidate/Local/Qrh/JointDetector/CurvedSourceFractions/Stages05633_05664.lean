/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05633_05664
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98868369987782,98868098498001,98867826984725,98867555447954,98867283887689,98867012303931,98866740696681,98866469065940,98866197411709,98865925733989,98865654032781,98865382308085,98865110559903,98864838788236,98864566993084,98864295174448,98864023332330,98863751466730,98863479577649,98863207665088,98862935729048,98862663769530,98862391786534,98862119780062,98861847750115,98861575696693,98861303619798,98861031519430,98860759395591,98860487248281,98860215077501,98859942883252,98859670665535]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5632+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5633 := params 0
abbrev ray5633 := rays 0
def bank5633 : Fin 2 → Cell := twoBank p5633 ray5633
theorem signs5633 : ∀ j, Signs p5633 (bank5633 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5634 := params 1
abbrev ray5634 := rays 1
def bank5634 : Fin 2 → Cell := twoBank p5634 ray5634
theorem signs5634 : ∀ j, Signs p5634 (bank5634 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5635 := params 2
abbrev ray5635 := rays 2
def bank5635 : Fin 2 → Cell := twoBank p5635 ray5635
theorem signs5635 : ∀ j, Signs p5635 (bank5635 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5636 := params 3
abbrev ray5636 := rays 3
def bank5636 : Fin 2 → Cell := twoBank p5636 ray5636
theorem signs5636 : ∀ j, Signs p5636 (bank5636 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5637 := params 4
abbrev ray5637 := rays 4
def bank5637 : Fin 2 → Cell := twoBank p5637 ray5637
theorem signs5637 : ∀ j, Signs p5637 (bank5637 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5638 := params 5
abbrev ray5638 := rays 5
def bank5638 : Fin 2 → Cell := twoBank p5638 ray5638
theorem signs5638 : ∀ j, Signs p5638 (bank5638 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5639 := params 6
abbrev ray5639 := rays 6
def bank5639 : Fin 2 → Cell := twoBank p5639 ray5639
theorem signs5639 : ∀ j, Signs p5639 (bank5639 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5640 := params 7
abbrev ray5640 := rays 7
def bank5640 : Fin 2 → Cell := twoBank p5640 ray5640
theorem signs5640 : ∀ j, Signs p5640 (bank5640 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5641 := params 8
abbrev ray5641 := rays 8
def bank5641 : Fin 2 → Cell := twoBank p5641 ray5641
theorem signs5641 : ∀ j, Signs p5641 (bank5641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5642 := params 9
abbrev ray5642 := rays 9
def bank5642 : Fin 2 → Cell := twoBank p5642 ray5642
theorem signs5642 : ∀ j, Signs p5642 (bank5642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5643 := params 10
abbrev ray5643 := rays 10
def bank5643 : Fin 2 → Cell := twoBank p5643 ray5643
theorem signs5643 : ∀ j, Signs p5643 (bank5643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5644 := params 11
abbrev ray5644 := rays 11
def bank5644 : Fin 2 → Cell := twoBank p5644 ray5644
theorem signs5644 : ∀ j, Signs p5644 (bank5644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5645 := params 12
abbrev ray5645 := rays 12
def bank5645 : Fin 2 → Cell := twoBank p5645 ray5645
theorem signs5645 : ∀ j, Signs p5645 (bank5645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5646 := params 13
abbrev ray5646 := rays 13
def bank5646 : Fin 2 → Cell := twoBank p5646 ray5646
theorem signs5646 : ∀ j, Signs p5646 (bank5646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5647 := params 14
abbrev ray5647 := rays 14
def bank5647 : Fin 2 → Cell := twoBank p5647 ray5647
theorem signs5647 : ∀ j, Signs p5647 (bank5647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5648 := params 15
abbrev ray5648 := rays 15
def bank5648 : Fin 2 → Cell := twoBank p5648 ray5648
theorem signs5648 : ∀ j, Signs p5648 (bank5648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5649 := params 16
abbrev ray5649 := rays 16
def bank5649 : Fin 2 → Cell := twoBank p5649 ray5649
theorem signs5649 : ∀ j, Signs p5649 (bank5649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5650 := params 17
abbrev ray5650 := rays 17
def bank5650 : Fin 2 → Cell := twoBank p5650 ray5650
theorem signs5650 : ∀ j, Signs p5650 (bank5650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5651 := params 18
abbrev ray5651 := rays 18
def bank5651 : Fin 2 → Cell := twoBank p5651 ray5651
theorem signs5651 : ∀ j, Signs p5651 (bank5651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5652 := params 19
abbrev ray5652 := rays 19
def bank5652 : Fin 2 → Cell := twoBank p5652 ray5652
theorem signs5652 : ∀ j, Signs p5652 (bank5652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5653 := params 20
abbrev ray5653 := rays 20
def bank5653 : Fin 2 → Cell := twoBank p5653 ray5653
theorem signs5653 : ∀ j, Signs p5653 (bank5653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5654 := params 21
abbrev ray5654 := rays 21
def bank5654 : Fin 2 → Cell := twoBank p5654 ray5654
theorem signs5654 : ∀ j, Signs p5654 (bank5654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5655 := params 22
abbrev ray5655 := rays 22
def bank5655 : Fin 2 → Cell := twoBank p5655 ray5655
theorem signs5655 : ∀ j, Signs p5655 (bank5655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5656 := params 23
abbrev ray5656 := rays 23
def bank5656 : Fin 2 → Cell := twoBank p5656 ray5656
theorem signs5656 : ∀ j, Signs p5656 (bank5656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5657 := params 24
abbrev ray5657 := rays 24
def bank5657 : Fin 2 → Cell := twoBank p5657 ray5657
theorem signs5657 : ∀ j, Signs p5657 (bank5657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5658 := params 25
abbrev ray5658 := rays 25
def bank5658 : Fin 2 → Cell := twoBank p5658 ray5658
theorem signs5658 : ∀ j, Signs p5658 (bank5658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5659 := params 26
abbrev ray5659 := rays 26
def bank5659 : Fin 2 → Cell := twoBank p5659 ray5659
theorem signs5659 : ∀ j, Signs p5659 (bank5659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5660 := params 27
abbrev ray5660 := rays 27
def bank5660 : Fin 2 → Cell := twoBank p5660 ray5660
theorem signs5660 : ∀ j, Signs p5660 (bank5660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5661 := params 28
abbrev ray5661 := rays 28
def bank5661 : Fin 2 → Cell := twoBank p5661 ray5661
theorem signs5661 : ∀ j, Signs p5661 (bank5661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5662 := params 29
abbrev ray5662 := rays 29
def bank5662 : Fin 2 → Cell := twoBank p5662 ray5662
theorem signs5662 : ∀ j, Signs p5662 (bank5662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5663 := params 30
abbrev ray5663 := rays 30
def bank5663 : Fin 2 → Cell := twoBank p5663 ray5663
theorem signs5663 : ∀ j, Signs p5663 (bank5663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5664 := params 31
abbrev ray5664 := rays 31
def bank5664 : Fin 2 → Cell := twoBank p5664 ray5664
theorem signs5664 : ∀ j, Signs p5664 (bank5664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05633_05664
