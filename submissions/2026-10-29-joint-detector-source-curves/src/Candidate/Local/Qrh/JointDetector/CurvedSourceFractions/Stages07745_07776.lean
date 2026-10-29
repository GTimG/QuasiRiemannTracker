/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07745_07776
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98243969776525,98243650563377,98243331328462,98243012071780,98242692793332,98242373493119,98242054171142,98241734827401,98241415461897,98241096074631,98240776665603,98240457234814,98240137782265,98239818307957,98239498811890,98239179294065,98238859754483,98238540193145,98238220610051,98237901005202,98237581378598,98237261730241,98236942060131,98236622368269,98236302654655,98235982919290,98235663162175,98235343383311,98235023582699,98234703760339,98234383916232,98234064050378,98233744162778]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7744+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7745 := params 0
abbrev ray7745 := rays 0
def bank7745 : Fin 2 → Cell := twoBank p7745 ray7745
theorem signs7745 : ∀ j, Signs p7745 (bank7745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7746 := params 1
abbrev ray7746 := rays 1
def bank7746 : Fin 2 → Cell := twoBank p7746 ray7746
theorem signs7746 : ∀ j, Signs p7746 (bank7746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7747 := params 2
abbrev ray7747 := rays 2
def bank7747 : Fin 2 → Cell := twoBank p7747 ray7747
theorem signs7747 : ∀ j, Signs p7747 (bank7747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7748 := params 3
abbrev ray7748 := rays 3
def bank7748 : Fin 2 → Cell := twoBank p7748 ray7748
theorem signs7748 : ∀ j, Signs p7748 (bank7748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7749 := params 4
abbrev ray7749 := rays 4
def bank7749 : Fin 2 → Cell := twoBank p7749 ray7749
theorem signs7749 : ∀ j, Signs p7749 (bank7749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7750 := params 5
abbrev ray7750 := rays 5
def bank7750 : Fin 2 → Cell := twoBank p7750 ray7750
theorem signs7750 : ∀ j, Signs p7750 (bank7750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7751 := params 6
abbrev ray7751 := rays 6
def bank7751 : Fin 2 → Cell := twoBank p7751 ray7751
theorem signs7751 : ∀ j, Signs p7751 (bank7751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7752 := params 7
abbrev ray7752 := rays 7
def bank7752 : Fin 2 → Cell := twoBank p7752 ray7752
theorem signs7752 : ∀ j, Signs p7752 (bank7752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7753 := params 8
abbrev ray7753 := rays 8
def bank7753 : Fin 2 → Cell := twoBank p7753 ray7753
theorem signs7753 : ∀ j, Signs p7753 (bank7753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7754 := params 9
abbrev ray7754 := rays 9
def bank7754 : Fin 2 → Cell := twoBank p7754 ray7754
theorem signs7754 : ∀ j, Signs p7754 (bank7754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7755 := params 10
abbrev ray7755 := rays 10
def bank7755 : Fin 2 → Cell := twoBank p7755 ray7755
theorem signs7755 : ∀ j, Signs p7755 (bank7755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7756 := params 11
abbrev ray7756 := rays 11
def bank7756 : Fin 2 → Cell := twoBank p7756 ray7756
theorem signs7756 : ∀ j, Signs p7756 (bank7756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7757 := params 12
abbrev ray7757 := rays 12
def bank7757 : Fin 2 → Cell := twoBank p7757 ray7757
theorem signs7757 : ∀ j, Signs p7757 (bank7757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7758 := params 13
abbrev ray7758 := rays 13
def bank7758 : Fin 2 → Cell := twoBank p7758 ray7758
theorem signs7758 : ∀ j, Signs p7758 (bank7758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7759 := params 14
abbrev ray7759 := rays 14
def bank7759 : Fin 2 → Cell := twoBank p7759 ray7759
theorem signs7759 : ∀ j, Signs p7759 (bank7759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7760 := params 15
abbrev ray7760 := rays 15
def bank7760 : Fin 2 → Cell := twoBank p7760 ray7760
theorem signs7760 : ∀ j, Signs p7760 (bank7760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7761 := params 16
abbrev ray7761 := rays 16
def bank7761 : Fin 2 → Cell := twoBank p7761 ray7761
theorem signs7761 : ∀ j, Signs p7761 (bank7761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7762 := params 17
abbrev ray7762 := rays 17
def bank7762 : Fin 2 → Cell := twoBank p7762 ray7762
theorem signs7762 : ∀ j, Signs p7762 (bank7762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7763 := params 18
abbrev ray7763 := rays 18
def bank7763 : Fin 2 → Cell := twoBank p7763 ray7763
theorem signs7763 : ∀ j, Signs p7763 (bank7763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7764 := params 19
abbrev ray7764 := rays 19
def bank7764 : Fin 2 → Cell := twoBank p7764 ray7764
theorem signs7764 : ∀ j, Signs p7764 (bank7764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7765 := params 20
abbrev ray7765 := rays 20
def bank7765 : Fin 2 → Cell := twoBank p7765 ray7765
theorem signs7765 : ∀ j, Signs p7765 (bank7765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7766 := params 21
abbrev ray7766 := rays 21
def bank7766 : Fin 2 → Cell := twoBank p7766 ray7766
theorem signs7766 : ∀ j, Signs p7766 (bank7766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7767 := params 22
abbrev ray7767 := rays 22
def bank7767 : Fin 2 → Cell := twoBank p7767 ray7767
theorem signs7767 : ∀ j, Signs p7767 (bank7767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7768 := params 23
abbrev ray7768 := rays 23
def bank7768 : Fin 2 → Cell := twoBank p7768 ray7768
theorem signs7768 : ∀ j, Signs p7768 (bank7768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7769 := params 24
abbrev ray7769 := rays 24
def bank7769 : Fin 2 → Cell := twoBank p7769 ray7769
theorem signs7769 : ∀ j, Signs p7769 (bank7769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7770 := params 25
abbrev ray7770 := rays 25
def bank7770 : Fin 2 → Cell := twoBank p7770 ray7770
theorem signs7770 : ∀ j, Signs p7770 (bank7770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7771 := params 26
abbrev ray7771 := rays 26
def bank7771 : Fin 2 → Cell := twoBank p7771 ray7771
theorem signs7771 : ∀ j, Signs p7771 (bank7771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7772 := params 27
abbrev ray7772 := rays 27
def bank7772 : Fin 2 → Cell := twoBank p7772 ray7772
theorem signs7772 : ∀ j, Signs p7772 (bank7772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7773 := params 28
abbrev ray7773 := rays 28
def bank7773 : Fin 2 → Cell := twoBank p7773 ray7773
theorem signs7773 : ∀ j, Signs p7773 (bank7773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7774 := params 29
abbrev ray7774 := rays 29
def bank7774 : Fin 2 → Cell := twoBank p7774 ray7774
theorem signs7774 : ∀ j, Signs p7774 (bank7774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7775 := params 30
abbrev ray7775 := rays 30
def bank7775 : Fin 2 → Cell := twoBank p7775 ray7775
theorem signs7775 : ∀ j, Signs p7775 (bank7775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7776 := params 31
abbrev ray7776 := rays 31
def bank7776 : Fin 2 → Cell := twoBank p7776 ray7776
theorem signs7776 : ∀ j, Signs p7776 (bank7776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07745_07776
