/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07649_07680
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98274512780035,98274195659922,98273878517972,98273561354185,98273244168563,98272926961106,98272609731815,98272292480691,98271975207734,98271657912945,98271340596325,98271023257875,98270705897595,98270388515486,98270071111549,98269753685784,98269436238193,98269118768776,98268801277533,98268483764466,98268166229575,98267848672861,98267531094324,98267213493966,98266895871787,98266578227788,98266260561969,98265942874331,98265625164875,98265307433602,98264989680512,98264671905607,98264354108886]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7648+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7649 := params 0
abbrev ray7649 := rays 0
def bank7649 : Fin 2 → Cell := twoBank p7649 ray7649
theorem signs7649 : ∀ j, Signs p7649 (bank7649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7650 := params 1
abbrev ray7650 := rays 1
def bank7650 : Fin 2 → Cell := twoBank p7650 ray7650
theorem signs7650 : ∀ j, Signs p7650 (bank7650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7651 := params 2
abbrev ray7651 := rays 2
def bank7651 : Fin 2 → Cell := twoBank p7651 ray7651
theorem signs7651 : ∀ j, Signs p7651 (bank7651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7652 := params 3
abbrev ray7652 := rays 3
def bank7652 : Fin 2 → Cell := twoBank p7652 ray7652
theorem signs7652 : ∀ j, Signs p7652 (bank7652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7653 := params 4
abbrev ray7653 := rays 4
def bank7653 : Fin 2 → Cell := twoBank p7653 ray7653
theorem signs7653 : ∀ j, Signs p7653 (bank7653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7654 := params 5
abbrev ray7654 := rays 5
def bank7654 : Fin 2 → Cell := twoBank p7654 ray7654
theorem signs7654 : ∀ j, Signs p7654 (bank7654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7655 := params 6
abbrev ray7655 := rays 6
def bank7655 : Fin 2 → Cell := twoBank p7655 ray7655
theorem signs7655 : ∀ j, Signs p7655 (bank7655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7656 := params 7
abbrev ray7656 := rays 7
def bank7656 : Fin 2 → Cell := twoBank p7656 ray7656
theorem signs7656 : ∀ j, Signs p7656 (bank7656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7657 := params 8
abbrev ray7657 := rays 8
def bank7657 : Fin 2 → Cell := twoBank p7657 ray7657
theorem signs7657 : ∀ j, Signs p7657 (bank7657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7658 := params 9
abbrev ray7658 := rays 9
def bank7658 : Fin 2 → Cell := twoBank p7658 ray7658
theorem signs7658 : ∀ j, Signs p7658 (bank7658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7659 := params 10
abbrev ray7659 := rays 10
def bank7659 : Fin 2 → Cell := twoBank p7659 ray7659
theorem signs7659 : ∀ j, Signs p7659 (bank7659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7660 := params 11
abbrev ray7660 := rays 11
def bank7660 : Fin 2 → Cell := twoBank p7660 ray7660
theorem signs7660 : ∀ j, Signs p7660 (bank7660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7661 := params 12
abbrev ray7661 := rays 12
def bank7661 : Fin 2 → Cell := twoBank p7661 ray7661
theorem signs7661 : ∀ j, Signs p7661 (bank7661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7662 := params 13
abbrev ray7662 := rays 13
def bank7662 : Fin 2 → Cell := twoBank p7662 ray7662
theorem signs7662 : ∀ j, Signs p7662 (bank7662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7663 := params 14
abbrev ray7663 := rays 14
def bank7663 : Fin 2 → Cell := twoBank p7663 ray7663
theorem signs7663 : ∀ j, Signs p7663 (bank7663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7664 := params 15
abbrev ray7664 := rays 15
def bank7664 : Fin 2 → Cell := twoBank p7664 ray7664
theorem signs7664 : ∀ j, Signs p7664 (bank7664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7665 := params 16
abbrev ray7665 := rays 16
def bank7665 : Fin 2 → Cell := twoBank p7665 ray7665
theorem signs7665 : ∀ j, Signs p7665 (bank7665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7666 := params 17
abbrev ray7666 := rays 17
def bank7666 : Fin 2 → Cell := twoBank p7666 ray7666
theorem signs7666 : ∀ j, Signs p7666 (bank7666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7667 := params 18
abbrev ray7667 := rays 18
def bank7667 : Fin 2 → Cell := twoBank p7667 ray7667
theorem signs7667 : ∀ j, Signs p7667 (bank7667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7668 := params 19
abbrev ray7668 := rays 19
def bank7668 : Fin 2 → Cell := twoBank p7668 ray7668
theorem signs7668 : ∀ j, Signs p7668 (bank7668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7669 := params 20
abbrev ray7669 := rays 20
def bank7669 : Fin 2 → Cell := twoBank p7669 ray7669
theorem signs7669 : ∀ j, Signs p7669 (bank7669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7670 := params 21
abbrev ray7670 := rays 21
def bank7670 : Fin 2 → Cell := twoBank p7670 ray7670
theorem signs7670 : ∀ j, Signs p7670 (bank7670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7671 := params 22
abbrev ray7671 := rays 22
def bank7671 : Fin 2 → Cell := twoBank p7671 ray7671
theorem signs7671 : ∀ j, Signs p7671 (bank7671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7672 := params 23
abbrev ray7672 := rays 23
def bank7672 : Fin 2 → Cell := twoBank p7672 ray7672
theorem signs7672 : ∀ j, Signs p7672 (bank7672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7673 := params 24
abbrev ray7673 := rays 24
def bank7673 : Fin 2 → Cell := twoBank p7673 ray7673
theorem signs7673 : ∀ j, Signs p7673 (bank7673 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7674 := params 25
abbrev ray7674 := rays 25
def bank7674 : Fin 2 → Cell := twoBank p7674 ray7674
theorem signs7674 : ∀ j, Signs p7674 (bank7674 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7675 := params 26
abbrev ray7675 := rays 26
def bank7675 : Fin 2 → Cell := twoBank p7675 ray7675
theorem signs7675 : ∀ j, Signs p7675 (bank7675 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7676 := params 27
abbrev ray7676 := rays 27
def bank7676 : Fin 2 → Cell := twoBank p7676 ray7676
theorem signs7676 : ∀ j, Signs p7676 (bank7676 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7677 := params 28
abbrev ray7677 := rays 28
def bank7677 : Fin 2 → Cell := twoBank p7677 ray7677
theorem signs7677 : ∀ j, Signs p7677 (bank7677 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7678 := params 29
abbrev ray7678 := rays 29
def bank7678 : Fin 2 → Cell := twoBank p7678 ray7678
theorem signs7678 : ∀ j, Signs p7678 (bank7678 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7679 := params 30
abbrev ray7679 := rays 30
def bank7679 : Fin 2 → Cell := twoBank p7679 ray7679
theorem signs7679 : ∀ j, Signs p7679 (bank7679 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7680 := params 31
abbrev ray7680 := rays 31
def bank7680 : Fin 2 → Cell := twoBank p7680 ray7680
theorem signs7680 : ∀ j, Signs p7680 (bank7680 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07649_07680
