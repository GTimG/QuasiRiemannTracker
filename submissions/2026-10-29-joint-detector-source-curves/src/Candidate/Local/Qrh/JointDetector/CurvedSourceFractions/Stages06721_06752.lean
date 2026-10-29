/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06721_06752
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98559287096126,98558990566881,98558694015084,98558397440736,98558100843838,98557804224390,98557507582393,98557210917848,98556914230756,98556617521118,98556320788934,98556024034206,98555727256934,98555430457119,98555133634761,98554836789862,98554539922422,98554243032442,98553946119923,98553649184866,98553352227272,98553055247141,98552758244474,98552461219272,98552164171536,98551867101267,98551570008465,98551272893131,98550975755267,98550678594872,98550381411948,98550084206496,98549786978516]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6720+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6721 := params 0
abbrev ray6721 := rays 0
def bank6721 : Fin 2 → Cell := twoBank p6721 ray6721
theorem signs6721 : ∀ j, Signs p6721 (bank6721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6722 := params 1
abbrev ray6722 := rays 1
def bank6722 : Fin 2 → Cell := twoBank p6722 ray6722
theorem signs6722 : ∀ j, Signs p6722 (bank6722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6723 := params 2
abbrev ray6723 := rays 2
def bank6723 : Fin 2 → Cell := twoBank p6723 ray6723
theorem signs6723 : ∀ j, Signs p6723 (bank6723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6724 := params 3
abbrev ray6724 := rays 3
def bank6724 : Fin 2 → Cell := twoBank p6724 ray6724
theorem signs6724 : ∀ j, Signs p6724 (bank6724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6725 := params 4
abbrev ray6725 := rays 4
def bank6725 : Fin 2 → Cell := twoBank p6725 ray6725
theorem signs6725 : ∀ j, Signs p6725 (bank6725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6726 := params 5
abbrev ray6726 := rays 5
def bank6726 : Fin 2 → Cell := twoBank p6726 ray6726
theorem signs6726 : ∀ j, Signs p6726 (bank6726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6727 := params 6
abbrev ray6727 := rays 6
def bank6727 : Fin 2 → Cell := twoBank p6727 ray6727
theorem signs6727 : ∀ j, Signs p6727 (bank6727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6728 := params 7
abbrev ray6728 := rays 7
def bank6728 : Fin 2 → Cell := twoBank p6728 ray6728
theorem signs6728 : ∀ j, Signs p6728 (bank6728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6729 := params 8
abbrev ray6729 := rays 8
def bank6729 : Fin 2 → Cell := twoBank p6729 ray6729
theorem signs6729 : ∀ j, Signs p6729 (bank6729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6730 := params 9
abbrev ray6730 := rays 9
def bank6730 : Fin 2 → Cell := twoBank p6730 ray6730
theorem signs6730 : ∀ j, Signs p6730 (bank6730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6731 := params 10
abbrev ray6731 := rays 10
def bank6731 : Fin 2 → Cell := twoBank p6731 ray6731
theorem signs6731 : ∀ j, Signs p6731 (bank6731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6732 := params 11
abbrev ray6732 := rays 11
def bank6732 : Fin 2 → Cell := twoBank p6732 ray6732
theorem signs6732 : ∀ j, Signs p6732 (bank6732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6733 := params 12
abbrev ray6733 := rays 12
def bank6733 : Fin 2 → Cell := twoBank p6733 ray6733
theorem signs6733 : ∀ j, Signs p6733 (bank6733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6734 := params 13
abbrev ray6734 := rays 13
def bank6734 : Fin 2 → Cell := twoBank p6734 ray6734
theorem signs6734 : ∀ j, Signs p6734 (bank6734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6735 := params 14
abbrev ray6735 := rays 14
def bank6735 : Fin 2 → Cell := twoBank p6735 ray6735
theorem signs6735 : ∀ j, Signs p6735 (bank6735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6736 := params 15
abbrev ray6736 := rays 15
def bank6736 : Fin 2 → Cell := twoBank p6736 ray6736
theorem signs6736 : ∀ j, Signs p6736 (bank6736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6737 := params 16
abbrev ray6737 := rays 16
def bank6737 : Fin 2 → Cell := twoBank p6737 ray6737
theorem signs6737 : ∀ j, Signs p6737 (bank6737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6738 := params 17
abbrev ray6738 := rays 17
def bank6738 : Fin 2 → Cell := twoBank p6738 ray6738
theorem signs6738 : ∀ j, Signs p6738 (bank6738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6739 := params 18
abbrev ray6739 := rays 18
def bank6739 : Fin 2 → Cell := twoBank p6739 ray6739
theorem signs6739 : ∀ j, Signs p6739 (bank6739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6740 := params 19
abbrev ray6740 := rays 19
def bank6740 : Fin 2 → Cell := twoBank p6740 ray6740
theorem signs6740 : ∀ j, Signs p6740 (bank6740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6741 := params 20
abbrev ray6741 := rays 20
def bank6741 : Fin 2 → Cell := twoBank p6741 ray6741
theorem signs6741 : ∀ j, Signs p6741 (bank6741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6742 := params 21
abbrev ray6742 := rays 21
def bank6742 : Fin 2 → Cell := twoBank p6742 ray6742
theorem signs6742 : ∀ j, Signs p6742 (bank6742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6743 := params 22
abbrev ray6743 := rays 22
def bank6743 : Fin 2 → Cell := twoBank p6743 ray6743
theorem signs6743 : ∀ j, Signs p6743 (bank6743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6744 := params 23
abbrev ray6744 := rays 23
def bank6744 : Fin 2 → Cell := twoBank p6744 ray6744
theorem signs6744 : ∀ j, Signs p6744 (bank6744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6745 := params 24
abbrev ray6745 := rays 24
def bank6745 : Fin 2 → Cell := twoBank p6745 ray6745
theorem signs6745 : ∀ j, Signs p6745 (bank6745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6746 := params 25
abbrev ray6746 := rays 25
def bank6746 : Fin 2 → Cell := twoBank p6746 ray6746
theorem signs6746 : ∀ j, Signs p6746 (bank6746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6747 := params 26
abbrev ray6747 := rays 26
def bank6747 : Fin 2 → Cell := twoBank p6747 ray6747
theorem signs6747 : ∀ j, Signs p6747 (bank6747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6748 := params 27
abbrev ray6748 := rays 27
def bank6748 : Fin 2 → Cell := twoBank p6748 ray6748
theorem signs6748 : ∀ j, Signs p6748 (bank6748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6749 := params 28
abbrev ray6749 := rays 28
def bank6749 : Fin 2 → Cell := twoBank p6749 ray6749
theorem signs6749 : ∀ j, Signs p6749 (bank6749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6750 := params 29
abbrev ray6750 := rays 29
def bank6750 : Fin 2 → Cell := twoBank p6750 ray6750
theorem signs6750 : ∀ j, Signs p6750 (bank6750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6751 := params 30
abbrev ray6751 := rays 30
def bank6751 : Fin 2 → Cell := twoBank p6751 ray6751
theorem signs6751 : ∀ j, Signs p6751 (bank6751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6752 := params 31
abbrev ray6752 := rays 31
def bank6752 : Fin 2 → Cell := twoBank p6752 ray6752
theorem signs6752 : ∀ j, Signs p6752 (bank6752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06721_06752
