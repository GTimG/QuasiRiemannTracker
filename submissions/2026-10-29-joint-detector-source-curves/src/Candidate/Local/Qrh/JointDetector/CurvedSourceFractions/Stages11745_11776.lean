/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11745_11776
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96799890046474,96799488727942,96799087389943,96798686032477,96798284655545,96797883259147,96797481843283,96797080407954,96796678953160,96796277478902,96795875985180,96795474471995,96795072939347,96794671387236,96794269815663,96793868224629,96793466614134,96793064984178,96792663334762,96792261665886,96791859977551,96791458269757,96791056542504,96790654795793,96790253029625,96789851244000,96789449438918,96789047614380,96788645770386,96788243906937,96787842024033,96787440121674,96787038199861]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11744+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11745 := params 0
abbrev ray11745 := rays 0
def bank11745 : Fin 2 → Cell := twoBank p11745 ray11745
theorem signs11745 : ∀ j, Signs p11745 (bank11745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11746 := params 1
abbrev ray11746 := rays 1
def bank11746 : Fin 2 → Cell := twoBank p11746 ray11746
theorem signs11746 : ∀ j, Signs p11746 (bank11746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11747 := params 2
abbrev ray11747 := rays 2
def bank11747 : Fin 2 → Cell := twoBank p11747 ray11747
theorem signs11747 : ∀ j, Signs p11747 (bank11747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11748 := params 3
abbrev ray11748 := rays 3
def bank11748 : Fin 2 → Cell := twoBank p11748 ray11748
theorem signs11748 : ∀ j, Signs p11748 (bank11748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11749 := params 4
abbrev ray11749 := rays 4
def bank11749 : Fin 2 → Cell := twoBank p11749 ray11749
theorem signs11749 : ∀ j, Signs p11749 (bank11749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11750 := params 5
abbrev ray11750 := rays 5
def bank11750 : Fin 2 → Cell := twoBank p11750 ray11750
theorem signs11750 : ∀ j, Signs p11750 (bank11750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11751 := params 6
abbrev ray11751 := rays 6
def bank11751 : Fin 2 → Cell := twoBank p11751 ray11751
theorem signs11751 : ∀ j, Signs p11751 (bank11751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11752 := params 7
abbrev ray11752 := rays 7
def bank11752 : Fin 2 → Cell := twoBank p11752 ray11752
theorem signs11752 : ∀ j, Signs p11752 (bank11752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11753 := params 8
abbrev ray11753 := rays 8
def bank11753 : Fin 2 → Cell := twoBank p11753 ray11753
theorem signs11753 : ∀ j, Signs p11753 (bank11753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11754 := params 9
abbrev ray11754 := rays 9
def bank11754 : Fin 2 → Cell := twoBank p11754 ray11754
theorem signs11754 : ∀ j, Signs p11754 (bank11754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11755 := params 10
abbrev ray11755 := rays 10
def bank11755 : Fin 2 → Cell := twoBank p11755 ray11755
theorem signs11755 : ∀ j, Signs p11755 (bank11755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11756 := params 11
abbrev ray11756 := rays 11
def bank11756 : Fin 2 → Cell := twoBank p11756 ray11756
theorem signs11756 : ∀ j, Signs p11756 (bank11756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11757 := params 12
abbrev ray11757 := rays 12
def bank11757 : Fin 2 → Cell := twoBank p11757 ray11757
theorem signs11757 : ∀ j, Signs p11757 (bank11757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11758 := params 13
abbrev ray11758 := rays 13
def bank11758 : Fin 2 → Cell := twoBank p11758 ray11758
theorem signs11758 : ∀ j, Signs p11758 (bank11758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11759 := params 14
abbrev ray11759 := rays 14
def bank11759 : Fin 2 → Cell := twoBank p11759 ray11759
theorem signs11759 : ∀ j, Signs p11759 (bank11759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11760 := params 15
abbrev ray11760 := rays 15
def bank11760 : Fin 2 → Cell := twoBank p11760 ray11760
theorem signs11760 : ∀ j, Signs p11760 (bank11760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11761 := params 16
abbrev ray11761 := rays 16
def bank11761 : Fin 2 → Cell := twoBank p11761 ray11761
theorem signs11761 : ∀ j, Signs p11761 (bank11761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11762 := params 17
abbrev ray11762 := rays 17
def bank11762 : Fin 2 → Cell := twoBank p11762 ray11762
theorem signs11762 : ∀ j, Signs p11762 (bank11762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11763 := params 18
abbrev ray11763 := rays 18
def bank11763 : Fin 2 → Cell := twoBank p11763 ray11763
theorem signs11763 : ∀ j, Signs p11763 (bank11763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11764 := params 19
abbrev ray11764 := rays 19
def bank11764 : Fin 2 → Cell := twoBank p11764 ray11764
theorem signs11764 : ∀ j, Signs p11764 (bank11764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11765 := params 20
abbrev ray11765 := rays 20
def bank11765 : Fin 2 → Cell := twoBank p11765 ray11765
theorem signs11765 : ∀ j, Signs p11765 (bank11765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11766 := params 21
abbrev ray11766 := rays 21
def bank11766 : Fin 2 → Cell := twoBank p11766 ray11766
theorem signs11766 : ∀ j, Signs p11766 (bank11766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11767 := params 22
abbrev ray11767 := rays 22
def bank11767 : Fin 2 → Cell := twoBank p11767 ray11767
theorem signs11767 : ∀ j, Signs p11767 (bank11767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11768 := params 23
abbrev ray11768 := rays 23
def bank11768 : Fin 2 → Cell := twoBank p11768 ray11768
theorem signs11768 : ∀ j, Signs p11768 (bank11768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11769 := params 24
abbrev ray11769 := rays 24
def bank11769 : Fin 2 → Cell := twoBank p11769 ray11769
theorem signs11769 : ∀ j, Signs p11769 (bank11769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11770 := params 25
abbrev ray11770 := rays 25
def bank11770 : Fin 2 → Cell := twoBank p11770 ray11770
theorem signs11770 : ∀ j, Signs p11770 (bank11770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11771 := params 26
abbrev ray11771 := rays 26
def bank11771 : Fin 2 → Cell := twoBank p11771 ray11771
theorem signs11771 : ∀ j, Signs p11771 (bank11771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11772 := params 27
abbrev ray11772 := rays 27
def bank11772 : Fin 2 → Cell := twoBank p11772 ray11772
theorem signs11772 : ∀ j, Signs p11772 (bank11772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11773 := params 28
abbrev ray11773 := rays 28
def bank11773 : Fin 2 → Cell := twoBank p11773 ray11773
theorem signs11773 : ∀ j, Signs p11773 (bank11773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11774 := params 29
abbrev ray11774 := rays 29
def bank11774 : Fin 2 → Cell := twoBank p11774 ray11774
theorem signs11774 : ∀ j, Signs p11774 (bank11774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11775 := params 30
abbrev ray11775 := rays 30
def bank11775 : Fin 2 → Cell := twoBank p11775 ray11775
theorem signs11775 : ∀ j, Signs p11775 (bank11775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11776 := params 31
abbrev ray11776 := rays 31
def bank11776 : Fin 2 → Cell := twoBank p11776 ray11776
theorem signs11776 : ∀ j, Signs p11776 (bank11776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11745_11776
