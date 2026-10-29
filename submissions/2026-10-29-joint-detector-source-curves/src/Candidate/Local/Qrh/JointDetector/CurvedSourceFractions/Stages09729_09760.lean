/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09729_09760
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97568717458910,97568356375180,97567995270961,97567634146252,97567273001055,97566911835370,97566550649197,97566189442537,97565828215391,97565466967759,97565105699642,97564744411041,97564383101956,97564021772387,97563660422335,97563299051801,97562937660785,97562576249288,97562214817310,97561853364852,97561491891915,97561130398499,97560768884605,97560407350233,97560045795384,97559684220058,97559322624256,97558961007978,97558599371226,97558237713999,97557876036298,97557514338124,97557152619478]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9728+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9729 := params 0
abbrev ray9729 := rays 0
def bank9729 : Fin 2 → Cell := twoBank p9729 ray9729
theorem signs9729 : ∀ j, Signs p9729 (bank9729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9730 := params 1
abbrev ray9730 := rays 1
def bank9730 : Fin 2 → Cell := twoBank p9730 ray9730
theorem signs9730 : ∀ j, Signs p9730 (bank9730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9731 := params 2
abbrev ray9731 := rays 2
def bank9731 : Fin 2 → Cell := twoBank p9731 ray9731
theorem signs9731 : ∀ j, Signs p9731 (bank9731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9732 := params 3
abbrev ray9732 := rays 3
def bank9732 : Fin 2 → Cell := twoBank p9732 ray9732
theorem signs9732 : ∀ j, Signs p9732 (bank9732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9733 := params 4
abbrev ray9733 := rays 4
def bank9733 : Fin 2 → Cell := twoBank p9733 ray9733
theorem signs9733 : ∀ j, Signs p9733 (bank9733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9734 := params 5
abbrev ray9734 := rays 5
def bank9734 : Fin 2 → Cell := twoBank p9734 ray9734
theorem signs9734 : ∀ j, Signs p9734 (bank9734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9735 := params 6
abbrev ray9735 := rays 6
def bank9735 : Fin 2 → Cell := twoBank p9735 ray9735
theorem signs9735 : ∀ j, Signs p9735 (bank9735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9736 := params 7
abbrev ray9736 := rays 7
def bank9736 : Fin 2 → Cell := twoBank p9736 ray9736
theorem signs9736 : ∀ j, Signs p9736 (bank9736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9737 := params 8
abbrev ray9737 := rays 8
def bank9737 : Fin 2 → Cell := twoBank p9737 ray9737
theorem signs9737 : ∀ j, Signs p9737 (bank9737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9738 := params 9
abbrev ray9738 := rays 9
def bank9738 : Fin 2 → Cell := twoBank p9738 ray9738
theorem signs9738 : ∀ j, Signs p9738 (bank9738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9739 := params 10
abbrev ray9739 := rays 10
def bank9739 : Fin 2 → Cell := twoBank p9739 ray9739
theorem signs9739 : ∀ j, Signs p9739 (bank9739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9740 := params 11
abbrev ray9740 := rays 11
def bank9740 : Fin 2 → Cell := twoBank p9740 ray9740
theorem signs9740 : ∀ j, Signs p9740 (bank9740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9741 := params 12
abbrev ray9741 := rays 12
def bank9741 : Fin 2 → Cell := twoBank p9741 ray9741
theorem signs9741 : ∀ j, Signs p9741 (bank9741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9742 := params 13
abbrev ray9742 := rays 13
def bank9742 : Fin 2 → Cell := twoBank p9742 ray9742
theorem signs9742 : ∀ j, Signs p9742 (bank9742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9743 := params 14
abbrev ray9743 := rays 14
def bank9743 : Fin 2 → Cell := twoBank p9743 ray9743
theorem signs9743 : ∀ j, Signs p9743 (bank9743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9744 := params 15
abbrev ray9744 := rays 15
def bank9744 : Fin 2 → Cell := twoBank p9744 ray9744
theorem signs9744 : ∀ j, Signs p9744 (bank9744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9745 := params 16
abbrev ray9745 := rays 16
def bank9745 : Fin 2 → Cell := twoBank p9745 ray9745
theorem signs9745 : ∀ j, Signs p9745 (bank9745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9746 := params 17
abbrev ray9746 := rays 17
def bank9746 : Fin 2 → Cell := twoBank p9746 ray9746
theorem signs9746 : ∀ j, Signs p9746 (bank9746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9747 := params 18
abbrev ray9747 := rays 18
def bank9747 : Fin 2 → Cell := twoBank p9747 ray9747
theorem signs9747 : ∀ j, Signs p9747 (bank9747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9748 := params 19
abbrev ray9748 := rays 19
def bank9748 : Fin 2 → Cell := twoBank p9748 ray9748
theorem signs9748 : ∀ j, Signs p9748 (bank9748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9749 := params 20
abbrev ray9749 := rays 20
def bank9749 : Fin 2 → Cell := twoBank p9749 ray9749
theorem signs9749 : ∀ j, Signs p9749 (bank9749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9750 := params 21
abbrev ray9750 := rays 21
def bank9750 : Fin 2 → Cell := twoBank p9750 ray9750
theorem signs9750 : ∀ j, Signs p9750 (bank9750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9751 := params 22
abbrev ray9751 := rays 22
def bank9751 : Fin 2 → Cell := twoBank p9751 ray9751
theorem signs9751 : ∀ j, Signs p9751 (bank9751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9752 := params 23
abbrev ray9752 := rays 23
def bank9752 : Fin 2 → Cell := twoBank p9752 ray9752
theorem signs9752 : ∀ j, Signs p9752 (bank9752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9753 := params 24
abbrev ray9753 := rays 24
def bank9753 : Fin 2 → Cell := twoBank p9753 ray9753
theorem signs9753 : ∀ j, Signs p9753 (bank9753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9754 := params 25
abbrev ray9754 := rays 25
def bank9754 : Fin 2 → Cell := twoBank p9754 ray9754
theorem signs9754 : ∀ j, Signs p9754 (bank9754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9755 := params 26
abbrev ray9755 := rays 26
def bank9755 : Fin 2 → Cell := twoBank p9755 ray9755
theorem signs9755 : ∀ j, Signs p9755 (bank9755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9756 := params 27
abbrev ray9756 := rays 27
def bank9756 : Fin 2 → Cell := twoBank p9756 ray9756
theorem signs9756 : ∀ j, Signs p9756 (bank9756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9757 := params 28
abbrev ray9757 := rays 28
def bank9757 : Fin 2 → Cell := twoBank p9757 ray9757
theorem signs9757 : ∀ j, Signs p9757 (bank9757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9758 := params 29
abbrev ray9758 := rays 29
def bank9758 : Fin 2 → Cell := twoBank p9758 ray9758
theorem signs9758 : ∀ j, Signs p9758 (bank9758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9759 := params 30
abbrev ray9759 := rays 30
def bank9759 : Fin 2 → Cell := twoBank p9759 ray9759
theorem signs9759 : ∀ j, Signs p9759 (bank9759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9760 := params 31
abbrev ray9760 := rays 31
def bank9760 : Fin 2 → Cell := twoBank p9760 ray9760
theorem signs9760 : ∀ j, Signs p9760 (bank9760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09729_09760
