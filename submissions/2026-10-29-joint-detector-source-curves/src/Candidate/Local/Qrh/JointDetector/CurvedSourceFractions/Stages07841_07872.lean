/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07841_07872
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98213226158161,98212904858628,98212583537397,98212262194468,98211940829842,98211619443520,98211298035502,98210976605789,98210655154382,98210333681282,98210012186489,98209690670004,98209369131828,98209047571961,98208725990404,98208404387158,98208082762224,98207761115602,98207439447293,98207117757298,98206796045617,98206474312251,98206152557201,98205830780467,98205508982051,98205187161953,98204865320173,98204543456713,98204221571573,98203899664753,98203577736255,98203255786079,98202933814226]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7840+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7841 := params 0
abbrev ray7841 := rays 0
def bank7841 : Fin 2 → Cell := twoBank p7841 ray7841
theorem signs7841 : ∀ j, Signs p7841 (bank7841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7842 := params 1
abbrev ray7842 := rays 1
def bank7842 : Fin 2 → Cell := twoBank p7842 ray7842
theorem signs7842 : ∀ j, Signs p7842 (bank7842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7843 := params 2
abbrev ray7843 := rays 2
def bank7843 : Fin 2 → Cell := twoBank p7843 ray7843
theorem signs7843 : ∀ j, Signs p7843 (bank7843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7844 := params 3
abbrev ray7844 := rays 3
def bank7844 : Fin 2 → Cell := twoBank p7844 ray7844
theorem signs7844 : ∀ j, Signs p7844 (bank7844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7845 := params 4
abbrev ray7845 := rays 4
def bank7845 : Fin 2 → Cell := twoBank p7845 ray7845
theorem signs7845 : ∀ j, Signs p7845 (bank7845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7846 := params 5
abbrev ray7846 := rays 5
def bank7846 : Fin 2 → Cell := twoBank p7846 ray7846
theorem signs7846 : ∀ j, Signs p7846 (bank7846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7847 := params 6
abbrev ray7847 := rays 6
def bank7847 : Fin 2 → Cell := twoBank p7847 ray7847
theorem signs7847 : ∀ j, Signs p7847 (bank7847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7848 := params 7
abbrev ray7848 := rays 7
def bank7848 : Fin 2 → Cell := twoBank p7848 ray7848
theorem signs7848 : ∀ j, Signs p7848 (bank7848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7849 := params 8
abbrev ray7849 := rays 8
def bank7849 : Fin 2 → Cell := twoBank p7849 ray7849
theorem signs7849 : ∀ j, Signs p7849 (bank7849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7850 := params 9
abbrev ray7850 := rays 9
def bank7850 : Fin 2 → Cell := twoBank p7850 ray7850
theorem signs7850 : ∀ j, Signs p7850 (bank7850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7851 := params 10
abbrev ray7851 := rays 10
def bank7851 : Fin 2 → Cell := twoBank p7851 ray7851
theorem signs7851 : ∀ j, Signs p7851 (bank7851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7852 := params 11
abbrev ray7852 := rays 11
def bank7852 : Fin 2 → Cell := twoBank p7852 ray7852
theorem signs7852 : ∀ j, Signs p7852 (bank7852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7853 := params 12
abbrev ray7853 := rays 12
def bank7853 : Fin 2 → Cell := twoBank p7853 ray7853
theorem signs7853 : ∀ j, Signs p7853 (bank7853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7854 := params 13
abbrev ray7854 := rays 13
def bank7854 : Fin 2 → Cell := twoBank p7854 ray7854
theorem signs7854 : ∀ j, Signs p7854 (bank7854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7855 := params 14
abbrev ray7855 := rays 14
def bank7855 : Fin 2 → Cell := twoBank p7855 ray7855
theorem signs7855 : ∀ j, Signs p7855 (bank7855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7856 := params 15
abbrev ray7856 := rays 15
def bank7856 : Fin 2 → Cell := twoBank p7856 ray7856
theorem signs7856 : ∀ j, Signs p7856 (bank7856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7857 := params 16
abbrev ray7857 := rays 16
def bank7857 : Fin 2 → Cell := twoBank p7857 ray7857
theorem signs7857 : ∀ j, Signs p7857 (bank7857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7858 := params 17
abbrev ray7858 := rays 17
def bank7858 : Fin 2 → Cell := twoBank p7858 ray7858
theorem signs7858 : ∀ j, Signs p7858 (bank7858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7859 := params 18
abbrev ray7859 := rays 18
def bank7859 : Fin 2 → Cell := twoBank p7859 ray7859
theorem signs7859 : ∀ j, Signs p7859 (bank7859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7860 := params 19
abbrev ray7860 := rays 19
def bank7860 : Fin 2 → Cell := twoBank p7860 ray7860
theorem signs7860 : ∀ j, Signs p7860 (bank7860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7861 := params 20
abbrev ray7861 := rays 20
def bank7861 : Fin 2 → Cell := twoBank p7861 ray7861
theorem signs7861 : ∀ j, Signs p7861 (bank7861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7862 := params 21
abbrev ray7862 := rays 21
def bank7862 : Fin 2 → Cell := twoBank p7862 ray7862
theorem signs7862 : ∀ j, Signs p7862 (bank7862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7863 := params 22
abbrev ray7863 := rays 22
def bank7863 : Fin 2 → Cell := twoBank p7863 ray7863
theorem signs7863 : ∀ j, Signs p7863 (bank7863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7864 := params 23
abbrev ray7864 := rays 23
def bank7864 : Fin 2 → Cell := twoBank p7864 ray7864
theorem signs7864 : ∀ j, Signs p7864 (bank7864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7865 := params 24
abbrev ray7865 := rays 24
def bank7865 : Fin 2 → Cell := twoBank p7865 ray7865
theorem signs7865 : ∀ j, Signs p7865 (bank7865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7866 := params 25
abbrev ray7866 := rays 25
def bank7866 : Fin 2 → Cell := twoBank p7866 ray7866
theorem signs7866 : ∀ j, Signs p7866 (bank7866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7867 := params 26
abbrev ray7867 := rays 26
def bank7867 : Fin 2 → Cell := twoBank p7867 ray7867
theorem signs7867 : ∀ j, Signs p7867 (bank7867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7868 := params 27
abbrev ray7868 := rays 27
def bank7868 : Fin 2 → Cell := twoBank p7868 ray7868
theorem signs7868 : ∀ j, Signs p7868 (bank7868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7869 := params 28
abbrev ray7869 := rays 28
def bank7869 : Fin 2 → Cell := twoBank p7869 ray7869
theorem signs7869 : ∀ j, Signs p7869 (bank7869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7870 := params 29
abbrev ray7870 := rays 29
def bank7870 : Fin 2 → Cell := twoBank p7870 ray7870
theorem signs7870 : ∀ j, Signs p7870 (bank7870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7871 := params 30
abbrev ray7871 := rays 30
def bank7871 : Fin 2 → Cell := twoBank p7871 ray7871
theorem signs7871 : ∀ j, Signs p7871 (bank7871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7872 := params 31
abbrev ray7872 := rays 31
def bank7872 : Fin 2 → Cell := twoBank p7872 ray7872
theorem signs7872 : ∀ j, Signs p7872 (bank7872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07841_07872
