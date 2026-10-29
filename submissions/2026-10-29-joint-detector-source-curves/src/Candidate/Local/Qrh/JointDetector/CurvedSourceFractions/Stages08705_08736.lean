/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08705_08736
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97927608379069,97927268589366,97926928778551,97926588946624,97926249093587,97925909219439,97925569324182,97925229407816,97924889470342,97924549511760,97924209532072,97923869531277,97923529509377,97923189466372,97922849402262,97922509317049,97922169210733,97921829083314,97921488934794,97921148765173,97920808574451,97920468362629,97920128129708,97919787875689,97919447600572,97919107304357,97918766987046,97918426648639,97918086289137,97917745908540,97917405506849,97917065084065,97916724640188]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8704+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8705 := params 0
abbrev ray8705 := rays 0
def bank8705 : Fin 2 → Cell := twoBank p8705 ray8705
theorem signs8705 : ∀ j, Signs p8705 (bank8705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8706 := params 1
abbrev ray8706 := rays 1
def bank8706 : Fin 2 → Cell := twoBank p8706 ray8706
theorem signs8706 : ∀ j, Signs p8706 (bank8706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8707 := params 2
abbrev ray8707 := rays 2
def bank8707 : Fin 2 → Cell := twoBank p8707 ray8707
theorem signs8707 : ∀ j, Signs p8707 (bank8707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8708 := params 3
abbrev ray8708 := rays 3
def bank8708 : Fin 2 → Cell := twoBank p8708 ray8708
theorem signs8708 : ∀ j, Signs p8708 (bank8708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8709 := params 4
abbrev ray8709 := rays 4
def bank8709 : Fin 2 → Cell := twoBank p8709 ray8709
theorem signs8709 : ∀ j, Signs p8709 (bank8709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8710 := params 5
abbrev ray8710 := rays 5
def bank8710 : Fin 2 → Cell := twoBank p8710 ray8710
theorem signs8710 : ∀ j, Signs p8710 (bank8710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8711 := params 6
abbrev ray8711 := rays 6
def bank8711 : Fin 2 → Cell := twoBank p8711 ray8711
theorem signs8711 : ∀ j, Signs p8711 (bank8711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8712 := params 7
abbrev ray8712 := rays 7
def bank8712 : Fin 2 → Cell := twoBank p8712 ray8712
theorem signs8712 : ∀ j, Signs p8712 (bank8712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8713 := params 8
abbrev ray8713 := rays 8
def bank8713 : Fin 2 → Cell := twoBank p8713 ray8713
theorem signs8713 : ∀ j, Signs p8713 (bank8713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8714 := params 9
abbrev ray8714 := rays 9
def bank8714 : Fin 2 → Cell := twoBank p8714 ray8714
theorem signs8714 : ∀ j, Signs p8714 (bank8714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8715 := params 10
abbrev ray8715 := rays 10
def bank8715 : Fin 2 → Cell := twoBank p8715 ray8715
theorem signs8715 : ∀ j, Signs p8715 (bank8715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8716 := params 11
abbrev ray8716 := rays 11
def bank8716 : Fin 2 → Cell := twoBank p8716 ray8716
theorem signs8716 : ∀ j, Signs p8716 (bank8716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8717 := params 12
abbrev ray8717 := rays 12
def bank8717 : Fin 2 → Cell := twoBank p8717 ray8717
theorem signs8717 : ∀ j, Signs p8717 (bank8717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8718 := params 13
abbrev ray8718 := rays 13
def bank8718 : Fin 2 → Cell := twoBank p8718 ray8718
theorem signs8718 : ∀ j, Signs p8718 (bank8718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8719 := params 14
abbrev ray8719 := rays 14
def bank8719 : Fin 2 → Cell := twoBank p8719 ray8719
theorem signs8719 : ∀ j, Signs p8719 (bank8719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8720 := params 15
abbrev ray8720 := rays 15
def bank8720 : Fin 2 → Cell := twoBank p8720 ray8720
theorem signs8720 : ∀ j, Signs p8720 (bank8720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8721 := params 16
abbrev ray8721 := rays 16
def bank8721 : Fin 2 → Cell := twoBank p8721 ray8721
theorem signs8721 : ∀ j, Signs p8721 (bank8721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8722 := params 17
abbrev ray8722 := rays 17
def bank8722 : Fin 2 → Cell := twoBank p8722 ray8722
theorem signs8722 : ∀ j, Signs p8722 (bank8722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8723 := params 18
abbrev ray8723 := rays 18
def bank8723 : Fin 2 → Cell := twoBank p8723 ray8723
theorem signs8723 : ∀ j, Signs p8723 (bank8723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8724 := params 19
abbrev ray8724 := rays 19
def bank8724 : Fin 2 → Cell := twoBank p8724 ray8724
theorem signs8724 : ∀ j, Signs p8724 (bank8724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8725 := params 20
abbrev ray8725 := rays 20
def bank8725 : Fin 2 → Cell := twoBank p8725 ray8725
theorem signs8725 : ∀ j, Signs p8725 (bank8725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8726 := params 21
abbrev ray8726 := rays 21
def bank8726 : Fin 2 → Cell := twoBank p8726 ray8726
theorem signs8726 : ∀ j, Signs p8726 (bank8726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8727 := params 22
abbrev ray8727 := rays 22
def bank8727 : Fin 2 → Cell := twoBank p8727 ray8727
theorem signs8727 : ∀ j, Signs p8727 (bank8727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8728 := params 23
abbrev ray8728 := rays 23
def bank8728 : Fin 2 → Cell := twoBank p8728 ray8728
theorem signs8728 : ∀ j, Signs p8728 (bank8728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8729 := params 24
abbrev ray8729 := rays 24
def bank8729 : Fin 2 → Cell := twoBank p8729 ray8729
theorem signs8729 : ∀ j, Signs p8729 (bank8729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8730 := params 25
abbrev ray8730 := rays 25
def bank8730 : Fin 2 → Cell := twoBank p8730 ray8730
theorem signs8730 : ∀ j, Signs p8730 (bank8730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8731 := params 26
abbrev ray8731 := rays 26
def bank8731 : Fin 2 → Cell := twoBank p8731 ray8731
theorem signs8731 : ∀ j, Signs p8731 (bank8731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8732 := params 27
abbrev ray8732 := rays 27
def bank8732 : Fin 2 → Cell := twoBank p8732 ray8732
theorem signs8732 : ∀ j, Signs p8732 (bank8732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8733 := params 28
abbrev ray8733 := rays 28
def bank8733 : Fin 2 → Cell := twoBank p8733 ray8733
theorem signs8733 : ∀ j, Signs p8733 (bank8733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8734 := params 29
abbrev ray8734 := rays 29
def bank8734 : Fin 2 → Cell := twoBank p8734 ray8734
theorem signs8734 : ∀ j, Signs p8734 (bank8734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8735 := params 30
abbrev ray8735 := rays 30
def bank8735 : Fin 2 → Cell := twoBank p8735 ray8735
theorem signs8735 : ∀ j, Signs p8735 (bank8735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8736 := params 31
abbrev ray8736 := rays 31
def bank8736 : Fin 2 → Cell := twoBank p8736 ray8736
theorem signs8736 : ∀ j, Signs p8736 (bank8736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08705_08736
