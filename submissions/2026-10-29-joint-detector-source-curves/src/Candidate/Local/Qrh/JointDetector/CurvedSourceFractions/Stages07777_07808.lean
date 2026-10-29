/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07777_07808
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98233744162778,98233424253433,98233104322344,98232784369512,98232464394937,98232144398620,98231824380561,98231504340762,98231184279223,98230864195944,98230544090927,98230223964172,98229903815680,98229583645452,98229263453488,98228943239789,98228623004356,98228302747189,98227982468289,98227662167657,98227341845294,98227021501200,98226701135376,98226380747823,98226060338542,98225739907533,98225419454797,98225098980335,98224778484147,98224457966234,98224137426597,98223816865237,98223496282154]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7776+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7777 := params 0
abbrev ray7777 := rays 0
def bank7777 : Fin 2 → Cell := twoBank p7777 ray7777
theorem signs7777 : ∀ j, Signs p7777 (bank7777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7778 := params 1
abbrev ray7778 := rays 1
def bank7778 : Fin 2 → Cell := twoBank p7778 ray7778
theorem signs7778 : ∀ j, Signs p7778 (bank7778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7779 := params 2
abbrev ray7779 := rays 2
def bank7779 : Fin 2 → Cell := twoBank p7779 ray7779
theorem signs7779 : ∀ j, Signs p7779 (bank7779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7780 := params 3
abbrev ray7780 := rays 3
def bank7780 : Fin 2 → Cell := twoBank p7780 ray7780
theorem signs7780 : ∀ j, Signs p7780 (bank7780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7781 := params 4
abbrev ray7781 := rays 4
def bank7781 : Fin 2 → Cell := twoBank p7781 ray7781
theorem signs7781 : ∀ j, Signs p7781 (bank7781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7782 := params 5
abbrev ray7782 := rays 5
def bank7782 : Fin 2 → Cell := twoBank p7782 ray7782
theorem signs7782 : ∀ j, Signs p7782 (bank7782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7783 := params 6
abbrev ray7783 := rays 6
def bank7783 : Fin 2 → Cell := twoBank p7783 ray7783
theorem signs7783 : ∀ j, Signs p7783 (bank7783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7784 := params 7
abbrev ray7784 := rays 7
def bank7784 : Fin 2 → Cell := twoBank p7784 ray7784
theorem signs7784 : ∀ j, Signs p7784 (bank7784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7785 := params 8
abbrev ray7785 := rays 8
def bank7785 : Fin 2 → Cell := twoBank p7785 ray7785
theorem signs7785 : ∀ j, Signs p7785 (bank7785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7786 := params 9
abbrev ray7786 := rays 9
def bank7786 : Fin 2 → Cell := twoBank p7786 ray7786
theorem signs7786 : ∀ j, Signs p7786 (bank7786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7787 := params 10
abbrev ray7787 := rays 10
def bank7787 : Fin 2 → Cell := twoBank p7787 ray7787
theorem signs7787 : ∀ j, Signs p7787 (bank7787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7788 := params 11
abbrev ray7788 := rays 11
def bank7788 : Fin 2 → Cell := twoBank p7788 ray7788
theorem signs7788 : ∀ j, Signs p7788 (bank7788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7789 := params 12
abbrev ray7789 := rays 12
def bank7789 : Fin 2 → Cell := twoBank p7789 ray7789
theorem signs7789 : ∀ j, Signs p7789 (bank7789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7790 := params 13
abbrev ray7790 := rays 13
def bank7790 : Fin 2 → Cell := twoBank p7790 ray7790
theorem signs7790 : ∀ j, Signs p7790 (bank7790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7791 := params 14
abbrev ray7791 := rays 14
def bank7791 : Fin 2 → Cell := twoBank p7791 ray7791
theorem signs7791 : ∀ j, Signs p7791 (bank7791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7792 := params 15
abbrev ray7792 := rays 15
def bank7792 : Fin 2 → Cell := twoBank p7792 ray7792
theorem signs7792 : ∀ j, Signs p7792 (bank7792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7793 := params 16
abbrev ray7793 := rays 16
def bank7793 : Fin 2 → Cell := twoBank p7793 ray7793
theorem signs7793 : ∀ j, Signs p7793 (bank7793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7794 := params 17
abbrev ray7794 := rays 17
def bank7794 : Fin 2 → Cell := twoBank p7794 ray7794
theorem signs7794 : ∀ j, Signs p7794 (bank7794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7795 := params 18
abbrev ray7795 := rays 18
def bank7795 : Fin 2 → Cell := twoBank p7795 ray7795
theorem signs7795 : ∀ j, Signs p7795 (bank7795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7796 := params 19
abbrev ray7796 := rays 19
def bank7796 : Fin 2 → Cell := twoBank p7796 ray7796
theorem signs7796 : ∀ j, Signs p7796 (bank7796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7797 := params 20
abbrev ray7797 := rays 20
def bank7797 : Fin 2 → Cell := twoBank p7797 ray7797
theorem signs7797 : ∀ j, Signs p7797 (bank7797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7798 := params 21
abbrev ray7798 := rays 21
def bank7798 : Fin 2 → Cell := twoBank p7798 ray7798
theorem signs7798 : ∀ j, Signs p7798 (bank7798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7799 := params 22
abbrev ray7799 := rays 22
def bank7799 : Fin 2 → Cell := twoBank p7799 ray7799
theorem signs7799 : ∀ j, Signs p7799 (bank7799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7800 := params 23
abbrev ray7800 := rays 23
def bank7800 : Fin 2 → Cell := twoBank p7800 ray7800
theorem signs7800 : ∀ j, Signs p7800 (bank7800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7801 := params 24
abbrev ray7801 := rays 24
def bank7801 : Fin 2 → Cell := twoBank p7801 ray7801
theorem signs7801 : ∀ j, Signs p7801 (bank7801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7802 := params 25
abbrev ray7802 := rays 25
def bank7802 : Fin 2 → Cell := twoBank p7802 ray7802
theorem signs7802 : ∀ j, Signs p7802 (bank7802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7803 := params 26
abbrev ray7803 := rays 26
def bank7803 : Fin 2 → Cell := twoBank p7803 ray7803
theorem signs7803 : ∀ j, Signs p7803 (bank7803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7804 := params 27
abbrev ray7804 := rays 27
def bank7804 : Fin 2 → Cell := twoBank p7804 ray7804
theorem signs7804 : ∀ j, Signs p7804 (bank7804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7805 := params 28
abbrev ray7805 := rays 28
def bank7805 : Fin 2 → Cell := twoBank p7805 ray7805
theorem signs7805 : ∀ j, Signs p7805 (bank7805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7806 := params 29
abbrev ray7806 := rays 29
def bank7806 : Fin 2 → Cell := twoBank p7806 ray7806
theorem signs7806 : ∀ j, Signs p7806 (bank7806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7807 := params 30
abbrev ray7807 := rays 30
def bank7807 : Fin 2 → Cell := twoBank p7807 ray7807
theorem signs7807 : ∀ j, Signs p7807 (bank7807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7808 := params 31
abbrev ray7808 := rays 31
def bank7808 : Fin 2 → Cell := twoBank p7808 ray7808
theorem signs7808 : ∀ j, Signs p7808 (bank7808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07777_07808
