/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02657_02688
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99567788619026,99567591682579,99567394719325,99567197729265,99567000712400,99566803668732,99566606598262,99566409500992,99566212376923,99566015226056,99565818048392,99565620843933,99565423612680,99565226354635,99565029069799,99564831758173,99564634419758,99564437054556,99564239662568,99564042243796,99563844798240,99563647325902,99563449826784,99563252300887,99563054748212,99562857168760,99562659562533,99562461929532,99562264269758,99562066583213,99561868869898,99561671129815,99561473362964]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2656+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2657 := params 0
abbrev ray2657 := rays 0
def bank2657 : Fin 2 → Cell := twoBank p2657 ray2657
theorem signs2657 : ∀ j, Signs p2657 (bank2657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2658 := params 1
abbrev ray2658 := rays 1
def bank2658 : Fin 2 → Cell := twoBank p2658 ray2658
theorem signs2658 : ∀ j, Signs p2658 (bank2658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2659 := params 2
abbrev ray2659 := rays 2
def bank2659 : Fin 2 → Cell := twoBank p2659 ray2659
theorem signs2659 : ∀ j, Signs p2659 (bank2659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2660 := params 3
abbrev ray2660 := rays 3
def bank2660 : Fin 2 → Cell := twoBank p2660 ray2660
theorem signs2660 : ∀ j, Signs p2660 (bank2660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2661 := params 4
abbrev ray2661 := rays 4
def bank2661 : Fin 2 → Cell := twoBank p2661 ray2661
theorem signs2661 : ∀ j, Signs p2661 (bank2661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2662 := params 5
abbrev ray2662 := rays 5
def bank2662 : Fin 2 → Cell := twoBank p2662 ray2662
theorem signs2662 : ∀ j, Signs p2662 (bank2662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2663 := params 6
abbrev ray2663 := rays 6
def bank2663 : Fin 2 → Cell := twoBank p2663 ray2663
theorem signs2663 : ∀ j, Signs p2663 (bank2663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2664 := params 7
abbrev ray2664 := rays 7
def bank2664 : Fin 2 → Cell := twoBank p2664 ray2664
theorem signs2664 : ∀ j, Signs p2664 (bank2664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2665 := params 8
abbrev ray2665 := rays 8
def bank2665 : Fin 2 → Cell := twoBank p2665 ray2665
theorem signs2665 : ∀ j, Signs p2665 (bank2665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2666 := params 9
abbrev ray2666 := rays 9
def bank2666 : Fin 2 → Cell := twoBank p2666 ray2666
theorem signs2666 : ∀ j, Signs p2666 (bank2666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2667 := params 10
abbrev ray2667 := rays 10
def bank2667 : Fin 2 → Cell := twoBank p2667 ray2667
theorem signs2667 : ∀ j, Signs p2667 (bank2667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2668 := params 11
abbrev ray2668 := rays 11
def bank2668 : Fin 2 → Cell := twoBank p2668 ray2668
theorem signs2668 : ∀ j, Signs p2668 (bank2668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2669 := params 12
abbrev ray2669 := rays 12
def bank2669 : Fin 2 → Cell := twoBank p2669 ray2669
theorem signs2669 : ∀ j, Signs p2669 (bank2669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2670 := params 13
abbrev ray2670 := rays 13
def bank2670 : Fin 2 → Cell := twoBank p2670 ray2670
theorem signs2670 : ∀ j, Signs p2670 (bank2670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2671 := params 14
abbrev ray2671 := rays 14
def bank2671 : Fin 2 → Cell := twoBank p2671 ray2671
theorem signs2671 : ∀ j, Signs p2671 (bank2671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2672 := params 15
abbrev ray2672 := rays 15
def bank2672 : Fin 2 → Cell := twoBank p2672 ray2672
theorem signs2672 : ∀ j, Signs p2672 (bank2672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2673 := params 16
abbrev ray2673 := rays 16
def bank2673 : Fin 2 → Cell := twoBank p2673 ray2673
theorem signs2673 : ∀ j, Signs p2673 (bank2673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2674 := params 17
abbrev ray2674 := rays 17
def bank2674 : Fin 2 → Cell := twoBank p2674 ray2674
theorem signs2674 : ∀ j, Signs p2674 (bank2674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2675 := params 18
abbrev ray2675 := rays 18
def bank2675 : Fin 2 → Cell := twoBank p2675 ray2675
theorem signs2675 : ∀ j, Signs p2675 (bank2675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2676 := params 19
abbrev ray2676 := rays 19
def bank2676 : Fin 2 → Cell := twoBank p2676 ray2676
theorem signs2676 : ∀ j, Signs p2676 (bank2676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2677 := params 20
abbrev ray2677 := rays 20
def bank2677 : Fin 2 → Cell := twoBank p2677 ray2677
theorem signs2677 : ∀ j, Signs p2677 (bank2677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2678 := params 21
abbrev ray2678 := rays 21
def bank2678 : Fin 2 → Cell := twoBank p2678 ray2678
theorem signs2678 : ∀ j, Signs p2678 (bank2678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2679 := params 22
abbrev ray2679 := rays 22
def bank2679 : Fin 2 → Cell := twoBank p2679 ray2679
theorem signs2679 : ∀ j, Signs p2679 (bank2679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2680 := params 23
abbrev ray2680 := rays 23
def bank2680 : Fin 2 → Cell := twoBank p2680 ray2680
theorem signs2680 : ∀ j, Signs p2680 (bank2680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2681 := params 24
abbrev ray2681 := rays 24
def bank2681 : Fin 2 → Cell := twoBank p2681 ray2681
theorem signs2681 : ∀ j, Signs p2681 (bank2681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2682 := params 25
abbrev ray2682 := rays 25
def bank2682 : Fin 2 → Cell := twoBank p2682 ray2682
theorem signs2682 : ∀ j, Signs p2682 (bank2682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2683 := params 26
abbrev ray2683 := rays 26
def bank2683 : Fin 2 → Cell := twoBank p2683 ray2683
theorem signs2683 : ∀ j, Signs p2683 (bank2683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2684 := params 27
abbrev ray2684 := rays 27
def bank2684 : Fin 2 → Cell := twoBank p2684 ray2684
theorem signs2684 : ∀ j, Signs p2684 (bank2684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2685 := params 28
abbrev ray2685 := rays 28
def bank2685 : Fin 2 → Cell := twoBank p2685 ray2685
theorem signs2685 : ∀ j, Signs p2685 (bank2685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2686 := params 29
abbrev ray2686 := rays 29
def bank2686 : Fin 2 → Cell := twoBank p2686 ray2686
theorem signs2686 : ∀ j, Signs p2686 (bank2686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2687 := params 30
abbrev ray2687 := rays 30
def bank2687 : Fin 2 → Cell := twoBank p2687 ray2687
theorem signs2687 : ∀ j, Signs p2687 (bank2687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2688 := params 31
abbrev ray2688 := rays 31
def bank2688 : Fin 2 → Cell := twoBank p2688 ray2688
theorem signs2688 : ∀ j, Signs p2688 (bank2688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02657_02688
