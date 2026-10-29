/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05697_05728
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98850947313003,98850674321359,98850401306278,98850128267761,98849855205809,98849582120423,98849309011604,98849035879353,98848762723671,98848489544558,98848216342016,98847943116045,98847669866647,98847396593822,98847123297571,98846849977896,98846576634797,98846303268275,98846029878331,98845756464965,98845483028179,98845209567974,98844936084350,98844662577309,98844389046851,98844115492978,98843841915690,98843568314988,98843294690873,98843021043346,98842747372408,98842473678060,98842199960303]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5696+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5697 := params 0
abbrev ray5697 := rays 0
def bank5697 : Fin 2 → Cell := twoBank p5697 ray5697
theorem signs5697 : ∀ j, Signs p5697 (bank5697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5698 := params 1
abbrev ray5698 := rays 1
def bank5698 : Fin 2 → Cell := twoBank p5698 ray5698
theorem signs5698 : ∀ j, Signs p5698 (bank5698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5699 := params 2
abbrev ray5699 := rays 2
def bank5699 : Fin 2 → Cell := twoBank p5699 ray5699
theorem signs5699 : ∀ j, Signs p5699 (bank5699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5700 := params 3
abbrev ray5700 := rays 3
def bank5700 : Fin 2 → Cell := twoBank p5700 ray5700
theorem signs5700 : ∀ j, Signs p5700 (bank5700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5701 := params 4
abbrev ray5701 := rays 4
def bank5701 : Fin 2 → Cell := twoBank p5701 ray5701
theorem signs5701 : ∀ j, Signs p5701 (bank5701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5702 := params 5
abbrev ray5702 := rays 5
def bank5702 : Fin 2 → Cell := twoBank p5702 ray5702
theorem signs5702 : ∀ j, Signs p5702 (bank5702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5703 := params 6
abbrev ray5703 := rays 6
def bank5703 : Fin 2 → Cell := twoBank p5703 ray5703
theorem signs5703 : ∀ j, Signs p5703 (bank5703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5704 := params 7
abbrev ray5704 := rays 7
def bank5704 : Fin 2 → Cell := twoBank p5704 ray5704
theorem signs5704 : ∀ j, Signs p5704 (bank5704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5705 := params 8
abbrev ray5705 := rays 8
def bank5705 : Fin 2 → Cell := twoBank p5705 ray5705
theorem signs5705 : ∀ j, Signs p5705 (bank5705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5706 := params 9
abbrev ray5706 := rays 9
def bank5706 : Fin 2 → Cell := twoBank p5706 ray5706
theorem signs5706 : ∀ j, Signs p5706 (bank5706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5707 := params 10
abbrev ray5707 := rays 10
def bank5707 : Fin 2 → Cell := twoBank p5707 ray5707
theorem signs5707 : ∀ j, Signs p5707 (bank5707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5708 := params 11
abbrev ray5708 := rays 11
def bank5708 : Fin 2 → Cell := twoBank p5708 ray5708
theorem signs5708 : ∀ j, Signs p5708 (bank5708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5709 := params 12
abbrev ray5709 := rays 12
def bank5709 : Fin 2 → Cell := twoBank p5709 ray5709
theorem signs5709 : ∀ j, Signs p5709 (bank5709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5710 := params 13
abbrev ray5710 := rays 13
def bank5710 : Fin 2 → Cell := twoBank p5710 ray5710
theorem signs5710 : ∀ j, Signs p5710 (bank5710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5711 := params 14
abbrev ray5711 := rays 14
def bank5711 : Fin 2 → Cell := twoBank p5711 ray5711
theorem signs5711 : ∀ j, Signs p5711 (bank5711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5712 := params 15
abbrev ray5712 := rays 15
def bank5712 : Fin 2 → Cell := twoBank p5712 ray5712
theorem signs5712 : ∀ j, Signs p5712 (bank5712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5713 := params 16
abbrev ray5713 := rays 16
def bank5713 : Fin 2 → Cell := twoBank p5713 ray5713
theorem signs5713 : ∀ j, Signs p5713 (bank5713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5714 := params 17
abbrev ray5714 := rays 17
def bank5714 : Fin 2 → Cell := twoBank p5714 ray5714
theorem signs5714 : ∀ j, Signs p5714 (bank5714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5715 := params 18
abbrev ray5715 := rays 18
def bank5715 : Fin 2 → Cell := twoBank p5715 ray5715
theorem signs5715 : ∀ j, Signs p5715 (bank5715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5716 := params 19
abbrev ray5716 := rays 19
def bank5716 : Fin 2 → Cell := twoBank p5716 ray5716
theorem signs5716 : ∀ j, Signs p5716 (bank5716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5717 := params 20
abbrev ray5717 := rays 20
def bank5717 : Fin 2 → Cell := twoBank p5717 ray5717
theorem signs5717 : ∀ j, Signs p5717 (bank5717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5718 := params 21
abbrev ray5718 := rays 21
def bank5718 : Fin 2 → Cell := twoBank p5718 ray5718
theorem signs5718 : ∀ j, Signs p5718 (bank5718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5719 := params 22
abbrev ray5719 := rays 22
def bank5719 : Fin 2 → Cell := twoBank p5719 ray5719
theorem signs5719 : ∀ j, Signs p5719 (bank5719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5720 := params 23
abbrev ray5720 := rays 23
def bank5720 : Fin 2 → Cell := twoBank p5720 ray5720
theorem signs5720 : ∀ j, Signs p5720 (bank5720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5721 := params 24
abbrev ray5721 := rays 24
def bank5721 : Fin 2 → Cell := twoBank p5721 ray5721
theorem signs5721 : ∀ j, Signs p5721 (bank5721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5722 := params 25
abbrev ray5722 := rays 25
def bank5722 : Fin 2 → Cell := twoBank p5722 ray5722
theorem signs5722 : ∀ j, Signs p5722 (bank5722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5723 := params 26
abbrev ray5723 := rays 26
def bank5723 : Fin 2 → Cell := twoBank p5723 ray5723
theorem signs5723 : ∀ j, Signs p5723 (bank5723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5724 := params 27
abbrev ray5724 := rays 27
def bank5724 : Fin 2 → Cell := twoBank p5724 ray5724
theorem signs5724 : ∀ j, Signs p5724 (bank5724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5725 := params 28
abbrev ray5725 := rays 28
def bank5725 : Fin 2 → Cell := twoBank p5725 ray5725
theorem signs5725 : ∀ j, Signs p5725 (bank5725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5726 := params 29
abbrev ray5726 := rays 29
def bank5726 : Fin 2 → Cell := twoBank p5726 ray5726
theorem signs5726 : ∀ j, Signs p5726 (bank5726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5727 := params 30
abbrev ray5727 := rays 30
def bank5727 : Fin 2 → Cell := twoBank p5727 ray5727
theorem signs5727 : ∀ j, Signs p5727 (bank5727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5728 := params 31
abbrev ray5728 := rays 31
def bank5728 : Fin 2 → Cell := twoBank p5728 ray5728
theorem signs5728 : ∀ j, Signs p5728 (bank5728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05697_05728
