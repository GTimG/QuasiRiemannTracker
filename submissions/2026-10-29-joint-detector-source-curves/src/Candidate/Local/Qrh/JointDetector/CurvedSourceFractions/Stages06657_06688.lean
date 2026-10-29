/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06657_06688
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98578218022274,98577922938055,98577627831232,98577332701805,98577037549776,98576742375145,98576447177913,98576151958081,98575856715649,98575561450619,98575266162991,98574970852766,98574675519945,98574380164529,98574084786518,98573789385914,98573493962717,98573198516928,98572903048548,98572607557578,98572312044018,98572016507869,98571720949132,98571425367808,98571129763898,98570834137403,98570538488323,98570242816659,98569947122412,98569651405583,98569355666173,98569059904182,98568764119611]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6656+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6657 := params 0
abbrev ray6657 := rays 0
def bank6657 : Fin 2 → Cell := twoBank p6657 ray6657
theorem signs6657 : ∀ j, Signs p6657 (bank6657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6658 := params 1
abbrev ray6658 := rays 1
def bank6658 : Fin 2 → Cell := twoBank p6658 ray6658
theorem signs6658 : ∀ j, Signs p6658 (bank6658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6659 := params 2
abbrev ray6659 := rays 2
def bank6659 : Fin 2 → Cell := twoBank p6659 ray6659
theorem signs6659 : ∀ j, Signs p6659 (bank6659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6660 := params 3
abbrev ray6660 := rays 3
def bank6660 : Fin 2 → Cell := twoBank p6660 ray6660
theorem signs6660 : ∀ j, Signs p6660 (bank6660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6661 := params 4
abbrev ray6661 := rays 4
def bank6661 : Fin 2 → Cell := twoBank p6661 ray6661
theorem signs6661 : ∀ j, Signs p6661 (bank6661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6662 := params 5
abbrev ray6662 := rays 5
def bank6662 : Fin 2 → Cell := twoBank p6662 ray6662
theorem signs6662 : ∀ j, Signs p6662 (bank6662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6663 := params 6
abbrev ray6663 := rays 6
def bank6663 : Fin 2 → Cell := twoBank p6663 ray6663
theorem signs6663 : ∀ j, Signs p6663 (bank6663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6664 := params 7
abbrev ray6664 := rays 7
def bank6664 : Fin 2 → Cell := twoBank p6664 ray6664
theorem signs6664 : ∀ j, Signs p6664 (bank6664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6665 := params 8
abbrev ray6665 := rays 8
def bank6665 : Fin 2 → Cell := twoBank p6665 ray6665
theorem signs6665 : ∀ j, Signs p6665 (bank6665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6666 := params 9
abbrev ray6666 := rays 9
def bank6666 : Fin 2 → Cell := twoBank p6666 ray6666
theorem signs6666 : ∀ j, Signs p6666 (bank6666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6667 := params 10
abbrev ray6667 := rays 10
def bank6667 : Fin 2 → Cell := twoBank p6667 ray6667
theorem signs6667 : ∀ j, Signs p6667 (bank6667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6668 := params 11
abbrev ray6668 := rays 11
def bank6668 : Fin 2 → Cell := twoBank p6668 ray6668
theorem signs6668 : ∀ j, Signs p6668 (bank6668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6669 := params 12
abbrev ray6669 := rays 12
def bank6669 : Fin 2 → Cell := twoBank p6669 ray6669
theorem signs6669 : ∀ j, Signs p6669 (bank6669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6670 := params 13
abbrev ray6670 := rays 13
def bank6670 : Fin 2 → Cell := twoBank p6670 ray6670
theorem signs6670 : ∀ j, Signs p6670 (bank6670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6671 := params 14
abbrev ray6671 := rays 14
def bank6671 : Fin 2 → Cell := twoBank p6671 ray6671
theorem signs6671 : ∀ j, Signs p6671 (bank6671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6672 := params 15
abbrev ray6672 := rays 15
def bank6672 : Fin 2 → Cell := twoBank p6672 ray6672
theorem signs6672 : ∀ j, Signs p6672 (bank6672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6673 := params 16
abbrev ray6673 := rays 16
def bank6673 : Fin 2 → Cell := twoBank p6673 ray6673
theorem signs6673 : ∀ j, Signs p6673 (bank6673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6674 := params 17
abbrev ray6674 := rays 17
def bank6674 : Fin 2 → Cell := twoBank p6674 ray6674
theorem signs6674 : ∀ j, Signs p6674 (bank6674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6675 := params 18
abbrev ray6675 := rays 18
def bank6675 : Fin 2 → Cell := twoBank p6675 ray6675
theorem signs6675 : ∀ j, Signs p6675 (bank6675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6676 := params 19
abbrev ray6676 := rays 19
def bank6676 : Fin 2 → Cell := twoBank p6676 ray6676
theorem signs6676 : ∀ j, Signs p6676 (bank6676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6677 := params 20
abbrev ray6677 := rays 20
def bank6677 : Fin 2 → Cell := twoBank p6677 ray6677
theorem signs6677 : ∀ j, Signs p6677 (bank6677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6678 := params 21
abbrev ray6678 := rays 21
def bank6678 : Fin 2 → Cell := twoBank p6678 ray6678
theorem signs6678 : ∀ j, Signs p6678 (bank6678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6679 := params 22
abbrev ray6679 := rays 22
def bank6679 : Fin 2 → Cell := twoBank p6679 ray6679
theorem signs6679 : ∀ j, Signs p6679 (bank6679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6680 := params 23
abbrev ray6680 := rays 23
def bank6680 : Fin 2 → Cell := twoBank p6680 ray6680
theorem signs6680 : ∀ j, Signs p6680 (bank6680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6681 := params 24
abbrev ray6681 := rays 24
def bank6681 : Fin 2 → Cell := twoBank p6681 ray6681
theorem signs6681 : ∀ j, Signs p6681 (bank6681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6682 := params 25
abbrev ray6682 := rays 25
def bank6682 : Fin 2 → Cell := twoBank p6682 ray6682
theorem signs6682 : ∀ j, Signs p6682 (bank6682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6683 := params 26
abbrev ray6683 := rays 26
def bank6683 : Fin 2 → Cell := twoBank p6683 ray6683
theorem signs6683 : ∀ j, Signs p6683 (bank6683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6684 := params 27
abbrev ray6684 := rays 27
def bank6684 : Fin 2 → Cell := twoBank p6684 ray6684
theorem signs6684 : ∀ j, Signs p6684 (bank6684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6685 := params 28
abbrev ray6685 := rays 28
def bank6685 : Fin 2 → Cell := twoBank p6685 ray6685
theorem signs6685 : ∀ j, Signs p6685 (bank6685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6686 := params 29
abbrev ray6686 := rays 29
def bank6686 : Fin 2 → Cell := twoBank p6686 ray6686
theorem signs6686 : ∀ j, Signs p6686 (bank6686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6687 := params 30
abbrev ray6687 := rays 30
def bank6687 : Fin 2 → Cell := twoBank p6687 ray6687
theorem signs6687 : ∀ j, Signs p6687 (bank6687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6688 := params 31
abbrev ray6688 := rays 31
def bank6688 : Fin 2 → Cell := twoBank p6688 ray6688
theorem signs6688 : ∀ j, Signs p6688 (bank6688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06657_06688
