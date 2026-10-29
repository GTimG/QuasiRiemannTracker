/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08737_08768
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97916724640188,97916384175219,97916043689158,97915703182006,97915362653764,97915022104433,97914681534013,97914340942505,97914000329909,97913659696226,97913319041457,97912978365602,97912637668662,97912296950638,97911956211530,97911615451339,97911274670065,97910933867710,97910593044273,97910252199756,97909911334159,97909570447483,97909229539728,97908888610895,97908547660985,97908206689998,97907865697935,97907524684797,97907183650584,97906842595297,97906501518936,97906160421502,97905819302996]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8736+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8737 := params 0
abbrev ray8737 := rays 0
def bank8737 : Fin 2 → Cell := twoBank p8737 ray8737
theorem signs8737 : ∀ j, Signs p8737 (bank8737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8738 := params 1
abbrev ray8738 := rays 1
def bank8738 : Fin 2 → Cell := twoBank p8738 ray8738
theorem signs8738 : ∀ j, Signs p8738 (bank8738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8739 := params 2
abbrev ray8739 := rays 2
def bank8739 : Fin 2 → Cell := twoBank p8739 ray8739
theorem signs8739 : ∀ j, Signs p8739 (bank8739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8740 := params 3
abbrev ray8740 := rays 3
def bank8740 : Fin 2 → Cell := twoBank p8740 ray8740
theorem signs8740 : ∀ j, Signs p8740 (bank8740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8741 := params 4
abbrev ray8741 := rays 4
def bank8741 : Fin 2 → Cell := twoBank p8741 ray8741
theorem signs8741 : ∀ j, Signs p8741 (bank8741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8742 := params 5
abbrev ray8742 := rays 5
def bank8742 : Fin 2 → Cell := twoBank p8742 ray8742
theorem signs8742 : ∀ j, Signs p8742 (bank8742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8743 := params 6
abbrev ray8743 := rays 6
def bank8743 : Fin 2 → Cell := twoBank p8743 ray8743
theorem signs8743 : ∀ j, Signs p8743 (bank8743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8744 := params 7
abbrev ray8744 := rays 7
def bank8744 : Fin 2 → Cell := twoBank p8744 ray8744
theorem signs8744 : ∀ j, Signs p8744 (bank8744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8745 := params 8
abbrev ray8745 := rays 8
def bank8745 : Fin 2 → Cell := twoBank p8745 ray8745
theorem signs8745 : ∀ j, Signs p8745 (bank8745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8746 := params 9
abbrev ray8746 := rays 9
def bank8746 : Fin 2 → Cell := twoBank p8746 ray8746
theorem signs8746 : ∀ j, Signs p8746 (bank8746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8747 := params 10
abbrev ray8747 := rays 10
def bank8747 : Fin 2 → Cell := twoBank p8747 ray8747
theorem signs8747 : ∀ j, Signs p8747 (bank8747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8748 := params 11
abbrev ray8748 := rays 11
def bank8748 : Fin 2 → Cell := twoBank p8748 ray8748
theorem signs8748 : ∀ j, Signs p8748 (bank8748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8749 := params 12
abbrev ray8749 := rays 12
def bank8749 : Fin 2 → Cell := twoBank p8749 ray8749
theorem signs8749 : ∀ j, Signs p8749 (bank8749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8750 := params 13
abbrev ray8750 := rays 13
def bank8750 : Fin 2 → Cell := twoBank p8750 ray8750
theorem signs8750 : ∀ j, Signs p8750 (bank8750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8751 := params 14
abbrev ray8751 := rays 14
def bank8751 : Fin 2 → Cell := twoBank p8751 ray8751
theorem signs8751 : ∀ j, Signs p8751 (bank8751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8752 := params 15
abbrev ray8752 := rays 15
def bank8752 : Fin 2 → Cell := twoBank p8752 ray8752
theorem signs8752 : ∀ j, Signs p8752 (bank8752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8753 := params 16
abbrev ray8753 := rays 16
def bank8753 : Fin 2 → Cell := twoBank p8753 ray8753
theorem signs8753 : ∀ j, Signs p8753 (bank8753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8754 := params 17
abbrev ray8754 := rays 17
def bank8754 : Fin 2 → Cell := twoBank p8754 ray8754
theorem signs8754 : ∀ j, Signs p8754 (bank8754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8755 := params 18
abbrev ray8755 := rays 18
def bank8755 : Fin 2 → Cell := twoBank p8755 ray8755
theorem signs8755 : ∀ j, Signs p8755 (bank8755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8756 := params 19
abbrev ray8756 := rays 19
def bank8756 : Fin 2 → Cell := twoBank p8756 ray8756
theorem signs8756 : ∀ j, Signs p8756 (bank8756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8757 := params 20
abbrev ray8757 := rays 20
def bank8757 : Fin 2 → Cell := twoBank p8757 ray8757
theorem signs8757 : ∀ j, Signs p8757 (bank8757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8758 := params 21
abbrev ray8758 := rays 21
def bank8758 : Fin 2 → Cell := twoBank p8758 ray8758
theorem signs8758 : ∀ j, Signs p8758 (bank8758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8759 := params 22
abbrev ray8759 := rays 22
def bank8759 : Fin 2 → Cell := twoBank p8759 ray8759
theorem signs8759 : ∀ j, Signs p8759 (bank8759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8760 := params 23
abbrev ray8760 := rays 23
def bank8760 : Fin 2 → Cell := twoBank p8760 ray8760
theorem signs8760 : ∀ j, Signs p8760 (bank8760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8761 := params 24
abbrev ray8761 := rays 24
def bank8761 : Fin 2 → Cell := twoBank p8761 ray8761
theorem signs8761 : ∀ j, Signs p8761 (bank8761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8762 := params 25
abbrev ray8762 := rays 25
def bank8762 : Fin 2 → Cell := twoBank p8762 ray8762
theorem signs8762 : ∀ j, Signs p8762 (bank8762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8763 := params 26
abbrev ray8763 := rays 26
def bank8763 : Fin 2 → Cell := twoBank p8763 ray8763
theorem signs8763 : ∀ j, Signs p8763 (bank8763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8764 := params 27
abbrev ray8764 := rays 27
def bank8764 : Fin 2 → Cell := twoBank p8764 ray8764
theorem signs8764 : ∀ j, Signs p8764 (bank8764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8765 := params 28
abbrev ray8765 := rays 28
def bank8765 : Fin 2 → Cell := twoBank p8765 ray8765
theorem signs8765 : ∀ j, Signs p8765 (bank8765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8766 := params 29
abbrev ray8766 := rays 29
def bank8766 : Fin 2 → Cell := twoBank p8766 ray8766
theorem signs8766 : ∀ j, Signs p8766 (bank8766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8767 := params 30
abbrev ray8767 := rays 30
def bank8767 : Fin 2 → Cell := twoBank p8767 ray8767
theorem signs8767 : ∀ j, Signs p8767 (bank8767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8768 := params 31
abbrev ray8768 := rays 31
def bank8768 : Fin 2 → Cell := twoBank p8768 ray8768
theorem signs8768 : ∀ j, Signs p8768 (bank8768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08737_08768
