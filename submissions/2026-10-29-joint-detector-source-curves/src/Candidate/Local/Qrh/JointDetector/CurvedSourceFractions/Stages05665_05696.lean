/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05665_05696
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98859670665535,98859398424351,98859126159701,98858853871586,98858581560006,98858309224963,98858036866458,98857764484491,98857492079063,98857219650176,98856947197830,98856674722026,98856402222765,98856129700048,98855857153876,98855584584250,98855311991171,98855039374639,98854766734656,98854494071222,98854221384339,98853948674007,98853675940227,98853403183000,98853130402327,98852857598209,98852584770647,98852311919642,98852039045195,98851766147307,98851493225978,98851220281210,98850947313003]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5664+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5665 := params 0
abbrev ray5665 := rays 0
def bank5665 : Fin 2 → Cell := twoBank p5665 ray5665
theorem signs5665 : ∀ j, Signs p5665 (bank5665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5666 := params 1
abbrev ray5666 := rays 1
def bank5666 : Fin 2 → Cell := twoBank p5666 ray5666
theorem signs5666 : ∀ j, Signs p5666 (bank5666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5667 := params 2
abbrev ray5667 := rays 2
def bank5667 : Fin 2 → Cell := twoBank p5667 ray5667
theorem signs5667 : ∀ j, Signs p5667 (bank5667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5668 := params 3
abbrev ray5668 := rays 3
def bank5668 : Fin 2 → Cell := twoBank p5668 ray5668
theorem signs5668 : ∀ j, Signs p5668 (bank5668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5669 := params 4
abbrev ray5669 := rays 4
def bank5669 : Fin 2 → Cell := twoBank p5669 ray5669
theorem signs5669 : ∀ j, Signs p5669 (bank5669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5670 := params 5
abbrev ray5670 := rays 5
def bank5670 : Fin 2 → Cell := twoBank p5670 ray5670
theorem signs5670 : ∀ j, Signs p5670 (bank5670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5671 := params 6
abbrev ray5671 := rays 6
def bank5671 : Fin 2 → Cell := twoBank p5671 ray5671
theorem signs5671 : ∀ j, Signs p5671 (bank5671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5672 := params 7
abbrev ray5672 := rays 7
def bank5672 : Fin 2 → Cell := twoBank p5672 ray5672
theorem signs5672 : ∀ j, Signs p5672 (bank5672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5673 := params 8
abbrev ray5673 := rays 8
def bank5673 : Fin 2 → Cell := twoBank p5673 ray5673
theorem signs5673 : ∀ j, Signs p5673 (bank5673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5674 := params 9
abbrev ray5674 := rays 9
def bank5674 : Fin 2 → Cell := twoBank p5674 ray5674
theorem signs5674 : ∀ j, Signs p5674 (bank5674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5675 := params 10
abbrev ray5675 := rays 10
def bank5675 : Fin 2 → Cell := twoBank p5675 ray5675
theorem signs5675 : ∀ j, Signs p5675 (bank5675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5676 := params 11
abbrev ray5676 := rays 11
def bank5676 : Fin 2 → Cell := twoBank p5676 ray5676
theorem signs5676 : ∀ j, Signs p5676 (bank5676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5677 := params 12
abbrev ray5677 := rays 12
def bank5677 : Fin 2 → Cell := twoBank p5677 ray5677
theorem signs5677 : ∀ j, Signs p5677 (bank5677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5678 := params 13
abbrev ray5678 := rays 13
def bank5678 : Fin 2 → Cell := twoBank p5678 ray5678
theorem signs5678 : ∀ j, Signs p5678 (bank5678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5679 := params 14
abbrev ray5679 := rays 14
def bank5679 : Fin 2 → Cell := twoBank p5679 ray5679
theorem signs5679 : ∀ j, Signs p5679 (bank5679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5680 := params 15
abbrev ray5680 := rays 15
def bank5680 : Fin 2 → Cell := twoBank p5680 ray5680
theorem signs5680 : ∀ j, Signs p5680 (bank5680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5681 := params 16
abbrev ray5681 := rays 16
def bank5681 : Fin 2 → Cell := twoBank p5681 ray5681
theorem signs5681 : ∀ j, Signs p5681 (bank5681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5682 := params 17
abbrev ray5682 := rays 17
def bank5682 : Fin 2 → Cell := twoBank p5682 ray5682
theorem signs5682 : ∀ j, Signs p5682 (bank5682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5683 := params 18
abbrev ray5683 := rays 18
def bank5683 : Fin 2 → Cell := twoBank p5683 ray5683
theorem signs5683 : ∀ j, Signs p5683 (bank5683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5684 := params 19
abbrev ray5684 := rays 19
def bank5684 : Fin 2 → Cell := twoBank p5684 ray5684
theorem signs5684 : ∀ j, Signs p5684 (bank5684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5685 := params 20
abbrev ray5685 := rays 20
def bank5685 : Fin 2 → Cell := twoBank p5685 ray5685
theorem signs5685 : ∀ j, Signs p5685 (bank5685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5686 := params 21
abbrev ray5686 := rays 21
def bank5686 : Fin 2 → Cell := twoBank p5686 ray5686
theorem signs5686 : ∀ j, Signs p5686 (bank5686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5687 := params 22
abbrev ray5687 := rays 22
def bank5687 : Fin 2 → Cell := twoBank p5687 ray5687
theorem signs5687 : ∀ j, Signs p5687 (bank5687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5688 := params 23
abbrev ray5688 := rays 23
def bank5688 : Fin 2 → Cell := twoBank p5688 ray5688
theorem signs5688 : ∀ j, Signs p5688 (bank5688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5689 := params 24
abbrev ray5689 := rays 24
def bank5689 : Fin 2 → Cell := twoBank p5689 ray5689
theorem signs5689 : ∀ j, Signs p5689 (bank5689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5690 := params 25
abbrev ray5690 := rays 25
def bank5690 : Fin 2 → Cell := twoBank p5690 ray5690
theorem signs5690 : ∀ j, Signs p5690 (bank5690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5691 := params 26
abbrev ray5691 := rays 26
def bank5691 : Fin 2 → Cell := twoBank p5691 ray5691
theorem signs5691 : ∀ j, Signs p5691 (bank5691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5692 := params 27
abbrev ray5692 := rays 27
def bank5692 : Fin 2 → Cell := twoBank p5692 ray5692
theorem signs5692 : ∀ j, Signs p5692 (bank5692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5693 := params 28
abbrev ray5693 := rays 28
def bank5693 : Fin 2 → Cell := twoBank p5693 ray5693
theorem signs5693 : ∀ j, Signs p5693 (bank5693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5694 := params 29
abbrev ray5694 := rays 29
def bank5694 : Fin 2 → Cell := twoBank p5694 ray5694
theorem signs5694 : ∀ j, Signs p5694 (bank5694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5695 := params 30
abbrev ray5695 := rays 30
def bank5695 : Fin 2 → Cell := twoBank p5695 ray5695
theorem signs5695 : ∀ j, Signs p5695 (bank5695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5696 := params 31
abbrev ray5696 := rays 31
def bank5696 : Fin 2 → Cell := twoBank p5696 ray5696
theorem signs5696 : ∀ j, Signs p5696 (bank5696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05665_05696
