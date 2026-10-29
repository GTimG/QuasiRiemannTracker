/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04673_04704
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99118021397554,99117772906644,99117524391298,99117275851518,99117027287304,99116778698657,99116530085579,99116281448070,99116032786132,99115784099766,99115535388972,99115286653752,99115037894107,99114789110037,99114540301544,99114291468629,99114042611293,99113793729537,99113544823361,99113295892767,99113046937756,99112797958329,99112548954487,99112299926232,99112050873564,99111801796484,99111552694993,99111303569092,99111054418782,99110805244065,99110556044941,99110306821411,99110057573477]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4672+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4673 := params 0
abbrev ray4673 := rays 0
def bank4673 : Fin 2 → Cell := twoBank p4673 ray4673
theorem signs4673 : ∀ j, Signs p4673 (bank4673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4674 := params 1
abbrev ray4674 := rays 1
def bank4674 : Fin 2 → Cell := twoBank p4674 ray4674
theorem signs4674 : ∀ j, Signs p4674 (bank4674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4675 := params 2
abbrev ray4675 := rays 2
def bank4675 : Fin 2 → Cell := twoBank p4675 ray4675
theorem signs4675 : ∀ j, Signs p4675 (bank4675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4676 := params 3
abbrev ray4676 := rays 3
def bank4676 : Fin 2 → Cell := twoBank p4676 ray4676
theorem signs4676 : ∀ j, Signs p4676 (bank4676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4677 := params 4
abbrev ray4677 := rays 4
def bank4677 : Fin 2 → Cell := twoBank p4677 ray4677
theorem signs4677 : ∀ j, Signs p4677 (bank4677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4678 := params 5
abbrev ray4678 := rays 5
def bank4678 : Fin 2 → Cell := twoBank p4678 ray4678
theorem signs4678 : ∀ j, Signs p4678 (bank4678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4679 := params 6
abbrev ray4679 := rays 6
def bank4679 : Fin 2 → Cell := twoBank p4679 ray4679
theorem signs4679 : ∀ j, Signs p4679 (bank4679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4680 := params 7
abbrev ray4680 := rays 7
def bank4680 : Fin 2 → Cell := twoBank p4680 ray4680
theorem signs4680 : ∀ j, Signs p4680 (bank4680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4681 := params 8
abbrev ray4681 := rays 8
def bank4681 : Fin 2 → Cell := twoBank p4681 ray4681
theorem signs4681 : ∀ j, Signs p4681 (bank4681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4682 := params 9
abbrev ray4682 := rays 9
def bank4682 : Fin 2 → Cell := twoBank p4682 ray4682
theorem signs4682 : ∀ j, Signs p4682 (bank4682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4683 := params 10
abbrev ray4683 := rays 10
def bank4683 : Fin 2 → Cell := twoBank p4683 ray4683
theorem signs4683 : ∀ j, Signs p4683 (bank4683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4684 := params 11
abbrev ray4684 := rays 11
def bank4684 : Fin 2 → Cell := twoBank p4684 ray4684
theorem signs4684 : ∀ j, Signs p4684 (bank4684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4685 := params 12
abbrev ray4685 := rays 12
def bank4685 : Fin 2 → Cell := twoBank p4685 ray4685
theorem signs4685 : ∀ j, Signs p4685 (bank4685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4686 := params 13
abbrev ray4686 := rays 13
def bank4686 : Fin 2 → Cell := twoBank p4686 ray4686
theorem signs4686 : ∀ j, Signs p4686 (bank4686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4687 := params 14
abbrev ray4687 := rays 14
def bank4687 : Fin 2 → Cell := twoBank p4687 ray4687
theorem signs4687 : ∀ j, Signs p4687 (bank4687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4688 := params 15
abbrev ray4688 := rays 15
def bank4688 : Fin 2 → Cell := twoBank p4688 ray4688
theorem signs4688 : ∀ j, Signs p4688 (bank4688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4689 := params 16
abbrev ray4689 := rays 16
def bank4689 : Fin 2 → Cell := twoBank p4689 ray4689
theorem signs4689 : ∀ j, Signs p4689 (bank4689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4690 := params 17
abbrev ray4690 := rays 17
def bank4690 : Fin 2 → Cell := twoBank p4690 ray4690
theorem signs4690 : ∀ j, Signs p4690 (bank4690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4691 := params 18
abbrev ray4691 := rays 18
def bank4691 : Fin 2 → Cell := twoBank p4691 ray4691
theorem signs4691 : ∀ j, Signs p4691 (bank4691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4692 := params 19
abbrev ray4692 := rays 19
def bank4692 : Fin 2 → Cell := twoBank p4692 ray4692
theorem signs4692 : ∀ j, Signs p4692 (bank4692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4693 := params 20
abbrev ray4693 := rays 20
def bank4693 : Fin 2 → Cell := twoBank p4693 ray4693
theorem signs4693 : ∀ j, Signs p4693 (bank4693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4694 := params 21
abbrev ray4694 := rays 21
def bank4694 : Fin 2 → Cell := twoBank p4694 ray4694
theorem signs4694 : ∀ j, Signs p4694 (bank4694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4695 := params 22
abbrev ray4695 := rays 22
def bank4695 : Fin 2 → Cell := twoBank p4695 ray4695
theorem signs4695 : ∀ j, Signs p4695 (bank4695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4696 := params 23
abbrev ray4696 := rays 23
def bank4696 : Fin 2 → Cell := twoBank p4696 ray4696
theorem signs4696 : ∀ j, Signs p4696 (bank4696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4697 := params 24
abbrev ray4697 := rays 24
def bank4697 : Fin 2 → Cell := twoBank p4697 ray4697
theorem signs4697 : ∀ j, Signs p4697 (bank4697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4698 := params 25
abbrev ray4698 := rays 25
def bank4698 : Fin 2 → Cell := twoBank p4698 ray4698
theorem signs4698 : ∀ j, Signs p4698 (bank4698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4699 := params 26
abbrev ray4699 := rays 26
def bank4699 : Fin 2 → Cell := twoBank p4699 ray4699
theorem signs4699 : ∀ j, Signs p4699 (bank4699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4700 := params 27
abbrev ray4700 := rays 27
def bank4700 : Fin 2 → Cell := twoBank p4700 ray4700
theorem signs4700 : ∀ j, Signs p4700 (bank4700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4701 := params 28
abbrev ray4701 := rays 28
def bank4701 : Fin 2 → Cell := twoBank p4701 ray4701
theorem signs4701 : ∀ j, Signs p4701 (bank4701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4702 := params 29
abbrev ray4702 := rays 29
def bank4702 : Fin 2 → Cell := twoBank p4702 ray4702
theorem signs4702 : ∀ j, Signs p4702 (bank4702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4703 := params 30
abbrev ray4703 := rays 30
def bank4703 : Fin 2 → Cell := twoBank p4703 ray4703
theorem signs4703 : ∀ j, Signs p4703 (bank4703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4704 := params 31
abbrev ray4704 := rays 31
def bank4704 : Fin 2 → Cell := twoBank p4704 ray4704
theorem signs4704 : ∀ j, Signs p4704 (bank4704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04673_04704
