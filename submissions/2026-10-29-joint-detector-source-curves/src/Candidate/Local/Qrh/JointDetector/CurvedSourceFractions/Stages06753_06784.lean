/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06753_06784
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98549786978516,98549489728009,98549192454976,98548895159418,98548597841335,98548300500729,98548003137600,98547705751949,98547408343777,98547110913084,98546813459872,98546515984141,98546218485892,98545920965126,98545623421843,98545325856045,98545028267732,98544730656905,98544433023565,98544135367713,98543837689349,98543539988474,98543242265090,98542944519197,98542646750795,98542348959886,98542051146470,98541753310548,98541455452121,98541157571190,98540859667756,98540561741819,98540263793380]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6752+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6753 := params 0
abbrev ray6753 := rays 0
def bank6753 : Fin 2 → Cell := twoBank p6753 ray6753
theorem signs6753 : ∀ j, Signs p6753 (bank6753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6754 := params 1
abbrev ray6754 := rays 1
def bank6754 : Fin 2 → Cell := twoBank p6754 ray6754
theorem signs6754 : ∀ j, Signs p6754 (bank6754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6755 := params 2
abbrev ray6755 := rays 2
def bank6755 : Fin 2 → Cell := twoBank p6755 ray6755
theorem signs6755 : ∀ j, Signs p6755 (bank6755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6756 := params 3
abbrev ray6756 := rays 3
def bank6756 : Fin 2 → Cell := twoBank p6756 ray6756
theorem signs6756 : ∀ j, Signs p6756 (bank6756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6757 := params 4
abbrev ray6757 := rays 4
def bank6757 : Fin 2 → Cell := twoBank p6757 ray6757
theorem signs6757 : ∀ j, Signs p6757 (bank6757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6758 := params 5
abbrev ray6758 := rays 5
def bank6758 : Fin 2 → Cell := twoBank p6758 ray6758
theorem signs6758 : ∀ j, Signs p6758 (bank6758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6759 := params 6
abbrev ray6759 := rays 6
def bank6759 : Fin 2 → Cell := twoBank p6759 ray6759
theorem signs6759 : ∀ j, Signs p6759 (bank6759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6760 := params 7
abbrev ray6760 := rays 7
def bank6760 : Fin 2 → Cell := twoBank p6760 ray6760
theorem signs6760 : ∀ j, Signs p6760 (bank6760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6761 := params 8
abbrev ray6761 := rays 8
def bank6761 : Fin 2 → Cell := twoBank p6761 ray6761
theorem signs6761 : ∀ j, Signs p6761 (bank6761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6762 := params 9
abbrev ray6762 := rays 9
def bank6762 : Fin 2 → Cell := twoBank p6762 ray6762
theorem signs6762 : ∀ j, Signs p6762 (bank6762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6763 := params 10
abbrev ray6763 := rays 10
def bank6763 : Fin 2 → Cell := twoBank p6763 ray6763
theorem signs6763 : ∀ j, Signs p6763 (bank6763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6764 := params 11
abbrev ray6764 := rays 11
def bank6764 : Fin 2 → Cell := twoBank p6764 ray6764
theorem signs6764 : ∀ j, Signs p6764 (bank6764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6765 := params 12
abbrev ray6765 := rays 12
def bank6765 : Fin 2 → Cell := twoBank p6765 ray6765
theorem signs6765 : ∀ j, Signs p6765 (bank6765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6766 := params 13
abbrev ray6766 := rays 13
def bank6766 : Fin 2 → Cell := twoBank p6766 ray6766
theorem signs6766 : ∀ j, Signs p6766 (bank6766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6767 := params 14
abbrev ray6767 := rays 14
def bank6767 : Fin 2 → Cell := twoBank p6767 ray6767
theorem signs6767 : ∀ j, Signs p6767 (bank6767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6768 := params 15
abbrev ray6768 := rays 15
def bank6768 : Fin 2 → Cell := twoBank p6768 ray6768
theorem signs6768 : ∀ j, Signs p6768 (bank6768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6769 := params 16
abbrev ray6769 := rays 16
def bank6769 : Fin 2 → Cell := twoBank p6769 ray6769
theorem signs6769 : ∀ j, Signs p6769 (bank6769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6770 := params 17
abbrev ray6770 := rays 17
def bank6770 : Fin 2 → Cell := twoBank p6770 ray6770
theorem signs6770 : ∀ j, Signs p6770 (bank6770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6771 := params 18
abbrev ray6771 := rays 18
def bank6771 : Fin 2 → Cell := twoBank p6771 ray6771
theorem signs6771 : ∀ j, Signs p6771 (bank6771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6772 := params 19
abbrev ray6772 := rays 19
def bank6772 : Fin 2 → Cell := twoBank p6772 ray6772
theorem signs6772 : ∀ j, Signs p6772 (bank6772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6773 := params 20
abbrev ray6773 := rays 20
def bank6773 : Fin 2 → Cell := twoBank p6773 ray6773
theorem signs6773 : ∀ j, Signs p6773 (bank6773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6774 := params 21
abbrev ray6774 := rays 21
def bank6774 : Fin 2 → Cell := twoBank p6774 ray6774
theorem signs6774 : ∀ j, Signs p6774 (bank6774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6775 := params 22
abbrev ray6775 := rays 22
def bank6775 : Fin 2 → Cell := twoBank p6775 ray6775
theorem signs6775 : ∀ j, Signs p6775 (bank6775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6776 := params 23
abbrev ray6776 := rays 23
def bank6776 : Fin 2 → Cell := twoBank p6776 ray6776
theorem signs6776 : ∀ j, Signs p6776 (bank6776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6777 := params 24
abbrev ray6777 := rays 24
def bank6777 : Fin 2 → Cell := twoBank p6777 ray6777
theorem signs6777 : ∀ j, Signs p6777 (bank6777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6778 := params 25
abbrev ray6778 := rays 25
def bank6778 : Fin 2 → Cell := twoBank p6778 ray6778
theorem signs6778 : ∀ j, Signs p6778 (bank6778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6779 := params 26
abbrev ray6779 := rays 26
def bank6779 : Fin 2 → Cell := twoBank p6779 ray6779
theorem signs6779 : ∀ j, Signs p6779 (bank6779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6780 := params 27
abbrev ray6780 := rays 27
def bank6780 : Fin 2 → Cell := twoBank p6780 ray6780
theorem signs6780 : ∀ j, Signs p6780 (bank6780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6781 := params 28
abbrev ray6781 := rays 28
def bank6781 : Fin 2 → Cell := twoBank p6781 ray6781
theorem signs6781 : ∀ j, Signs p6781 (bank6781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6782 := params 29
abbrev ray6782 := rays 29
def bank6782 : Fin 2 → Cell := twoBank p6782 ray6782
theorem signs6782 : ∀ j, Signs p6782 (bank6782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6783 := params 30
abbrev ray6783 := rays 30
def bank6783 : Fin 2 → Cell := twoBank p6783 ray6783
theorem signs6783 : ∀ j, Signs p6783 (bank6783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6784 := params 31
abbrev ray6784 := rays 31
def bank6784 : Fin 2 → Cell := twoBank p6784 ray6784
theorem signs6784 : ∀ j, Signs p6784 (bank6784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06753_06784
