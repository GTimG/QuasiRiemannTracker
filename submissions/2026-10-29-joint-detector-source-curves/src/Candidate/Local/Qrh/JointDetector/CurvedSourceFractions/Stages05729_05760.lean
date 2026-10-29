/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05729_05760
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98842199960303,98841926219137,98841652454564,98841378666584,98841104855199,98840831020409,98840557162215,98840283280618,98840009375619,98839735447219,98839461495419,98839187520220,98838913521623,98838639499628,98838365454237,98838091385450,98837817293268,98837543177693,98837269038725,98836994876365,98836720690614,98836446481473,98836172248943,98835897993024,98835623713718,98835349411026,98835075084948,98834800735485,98834526362639,98834251966410,98833977546799,98833703103807,98833428637435]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5728+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5729 := params 0
abbrev ray5729 := rays 0
def bank5729 : Fin 2 → Cell := twoBank p5729 ray5729
theorem signs5729 : ∀ j, Signs p5729 (bank5729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5730 := params 1
abbrev ray5730 := rays 1
def bank5730 : Fin 2 → Cell := twoBank p5730 ray5730
theorem signs5730 : ∀ j, Signs p5730 (bank5730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5731 := params 2
abbrev ray5731 := rays 2
def bank5731 : Fin 2 → Cell := twoBank p5731 ray5731
theorem signs5731 : ∀ j, Signs p5731 (bank5731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5732 := params 3
abbrev ray5732 := rays 3
def bank5732 : Fin 2 → Cell := twoBank p5732 ray5732
theorem signs5732 : ∀ j, Signs p5732 (bank5732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5733 := params 4
abbrev ray5733 := rays 4
def bank5733 : Fin 2 → Cell := twoBank p5733 ray5733
theorem signs5733 : ∀ j, Signs p5733 (bank5733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5734 := params 5
abbrev ray5734 := rays 5
def bank5734 : Fin 2 → Cell := twoBank p5734 ray5734
theorem signs5734 : ∀ j, Signs p5734 (bank5734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5735 := params 6
abbrev ray5735 := rays 6
def bank5735 : Fin 2 → Cell := twoBank p5735 ray5735
theorem signs5735 : ∀ j, Signs p5735 (bank5735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5736 := params 7
abbrev ray5736 := rays 7
def bank5736 : Fin 2 → Cell := twoBank p5736 ray5736
theorem signs5736 : ∀ j, Signs p5736 (bank5736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5737 := params 8
abbrev ray5737 := rays 8
def bank5737 : Fin 2 → Cell := twoBank p5737 ray5737
theorem signs5737 : ∀ j, Signs p5737 (bank5737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5738 := params 9
abbrev ray5738 := rays 9
def bank5738 : Fin 2 → Cell := twoBank p5738 ray5738
theorem signs5738 : ∀ j, Signs p5738 (bank5738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5739 := params 10
abbrev ray5739 := rays 10
def bank5739 : Fin 2 → Cell := twoBank p5739 ray5739
theorem signs5739 : ∀ j, Signs p5739 (bank5739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5740 := params 11
abbrev ray5740 := rays 11
def bank5740 : Fin 2 → Cell := twoBank p5740 ray5740
theorem signs5740 : ∀ j, Signs p5740 (bank5740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5741 := params 12
abbrev ray5741 := rays 12
def bank5741 : Fin 2 → Cell := twoBank p5741 ray5741
theorem signs5741 : ∀ j, Signs p5741 (bank5741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5742 := params 13
abbrev ray5742 := rays 13
def bank5742 : Fin 2 → Cell := twoBank p5742 ray5742
theorem signs5742 : ∀ j, Signs p5742 (bank5742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5743 := params 14
abbrev ray5743 := rays 14
def bank5743 : Fin 2 → Cell := twoBank p5743 ray5743
theorem signs5743 : ∀ j, Signs p5743 (bank5743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5744 := params 15
abbrev ray5744 := rays 15
def bank5744 : Fin 2 → Cell := twoBank p5744 ray5744
theorem signs5744 : ∀ j, Signs p5744 (bank5744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5745 := params 16
abbrev ray5745 := rays 16
def bank5745 : Fin 2 → Cell := twoBank p5745 ray5745
theorem signs5745 : ∀ j, Signs p5745 (bank5745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5746 := params 17
abbrev ray5746 := rays 17
def bank5746 : Fin 2 → Cell := twoBank p5746 ray5746
theorem signs5746 : ∀ j, Signs p5746 (bank5746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5747 := params 18
abbrev ray5747 := rays 18
def bank5747 : Fin 2 → Cell := twoBank p5747 ray5747
theorem signs5747 : ∀ j, Signs p5747 (bank5747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5748 := params 19
abbrev ray5748 := rays 19
def bank5748 : Fin 2 → Cell := twoBank p5748 ray5748
theorem signs5748 : ∀ j, Signs p5748 (bank5748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5749 := params 20
abbrev ray5749 := rays 20
def bank5749 : Fin 2 → Cell := twoBank p5749 ray5749
theorem signs5749 : ∀ j, Signs p5749 (bank5749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5750 := params 21
abbrev ray5750 := rays 21
def bank5750 : Fin 2 → Cell := twoBank p5750 ray5750
theorem signs5750 : ∀ j, Signs p5750 (bank5750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5751 := params 22
abbrev ray5751 := rays 22
def bank5751 : Fin 2 → Cell := twoBank p5751 ray5751
theorem signs5751 : ∀ j, Signs p5751 (bank5751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5752 := params 23
abbrev ray5752 := rays 23
def bank5752 : Fin 2 → Cell := twoBank p5752 ray5752
theorem signs5752 : ∀ j, Signs p5752 (bank5752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5753 := params 24
abbrev ray5753 := rays 24
def bank5753 : Fin 2 → Cell := twoBank p5753 ray5753
theorem signs5753 : ∀ j, Signs p5753 (bank5753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5754 := params 25
abbrev ray5754 := rays 25
def bank5754 : Fin 2 → Cell := twoBank p5754 ray5754
theorem signs5754 : ∀ j, Signs p5754 (bank5754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5755 := params 26
abbrev ray5755 := rays 26
def bank5755 : Fin 2 → Cell := twoBank p5755 ray5755
theorem signs5755 : ∀ j, Signs p5755 (bank5755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5756 := params 27
abbrev ray5756 := rays 27
def bank5756 : Fin 2 → Cell := twoBank p5756 ray5756
theorem signs5756 : ∀ j, Signs p5756 (bank5756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5757 := params 28
abbrev ray5757 := rays 28
def bank5757 : Fin 2 → Cell := twoBank p5757 ray5757
theorem signs5757 : ∀ j, Signs p5757 (bank5757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5758 := params 29
abbrev ray5758 := rays 29
def bank5758 : Fin 2 → Cell := twoBank p5758 ray5758
theorem signs5758 : ∀ j, Signs p5758 (bank5758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5759 := params 30
abbrev ray5759 := rays 30
def bank5759 : Fin 2 → Cell := twoBank p5759 ray5759
theorem signs5759 : ∀ j, Signs p5759 (bank5759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5760 := params 31
abbrev ray5760 := rays 31
def bank5760 : Fin 2 → Cell := twoBank p5760 ray5760
theorem signs5760 : ∀ j, Signs p5760 (bank5760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05729_05760
