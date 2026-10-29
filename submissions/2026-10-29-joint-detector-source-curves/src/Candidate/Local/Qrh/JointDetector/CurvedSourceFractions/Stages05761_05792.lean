/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05761_05792
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98833428637435,98833154147684,98832879634554,98832605098047,98832330538164,98832055954905,98831781348271,98831506718264,98831232064884,98830957388132,98830682688009,98830407964516,98830133217654,98829858447424,98829583653826,98829308836862,98829033996532,98828759132838,98828484245780,98828209335359,98827934401576,98827659444432,98827384463928,98827109460065,98826834432844,98826559382265,98826284308330,98826009211039,98825734090394,98825458946395,98825183779043,98824908588339,98824633374284]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5760+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5761 := params 0
abbrev ray5761 := rays 0
def bank5761 : Fin 2 → Cell := twoBank p5761 ray5761
theorem signs5761 : ∀ j, Signs p5761 (bank5761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5762 := params 1
abbrev ray5762 := rays 1
def bank5762 : Fin 2 → Cell := twoBank p5762 ray5762
theorem signs5762 : ∀ j, Signs p5762 (bank5762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5763 := params 2
abbrev ray5763 := rays 2
def bank5763 : Fin 2 → Cell := twoBank p5763 ray5763
theorem signs5763 : ∀ j, Signs p5763 (bank5763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5764 := params 3
abbrev ray5764 := rays 3
def bank5764 : Fin 2 → Cell := twoBank p5764 ray5764
theorem signs5764 : ∀ j, Signs p5764 (bank5764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5765 := params 4
abbrev ray5765 := rays 4
def bank5765 : Fin 2 → Cell := twoBank p5765 ray5765
theorem signs5765 : ∀ j, Signs p5765 (bank5765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5766 := params 5
abbrev ray5766 := rays 5
def bank5766 : Fin 2 → Cell := twoBank p5766 ray5766
theorem signs5766 : ∀ j, Signs p5766 (bank5766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5767 := params 6
abbrev ray5767 := rays 6
def bank5767 : Fin 2 → Cell := twoBank p5767 ray5767
theorem signs5767 : ∀ j, Signs p5767 (bank5767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5768 := params 7
abbrev ray5768 := rays 7
def bank5768 : Fin 2 → Cell := twoBank p5768 ray5768
theorem signs5768 : ∀ j, Signs p5768 (bank5768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5769 := params 8
abbrev ray5769 := rays 8
def bank5769 : Fin 2 → Cell := twoBank p5769 ray5769
theorem signs5769 : ∀ j, Signs p5769 (bank5769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5770 := params 9
abbrev ray5770 := rays 9
def bank5770 : Fin 2 → Cell := twoBank p5770 ray5770
theorem signs5770 : ∀ j, Signs p5770 (bank5770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5771 := params 10
abbrev ray5771 := rays 10
def bank5771 : Fin 2 → Cell := twoBank p5771 ray5771
theorem signs5771 : ∀ j, Signs p5771 (bank5771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5772 := params 11
abbrev ray5772 := rays 11
def bank5772 : Fin 2 → Cell := twoBank p5772 ray5772
theorem signs5772 : ∀ j, Signs p5772 (bank5772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5773 := params 12
abbrev ray5773 := rays 12
def bank5773 : Fin 2 → Cell := twoBank p5773 ray5773
theorem signs5773 : ∀ j, Signs p5773 (bank5773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5774 := params 13
abbrev ray5774 := rays 13
def bank5774 : Fin 2 → Cell := twoBank p5774 ray5774
theorem signs5774 : ∀ j, Signs p5774 (bank5774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5775 := params 14
abbrev ray5775 := rays 14
def bank5775 : Fin 2 → Cell := twoBank p5775 ray5775
theorem signs5775 : ∀ j, Signs p5775 (bank5775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5776 := params 15
abbrev ray5776 := rays 15
def bank5776 : Fin 2 → Cell := twoBank p5776 ray5776
theorem signs5776 : ∀ j, Signs p5776 (bank5776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5777 := params 16
abbrev ray5777 := rays 16
def bank5777 : Fin 2 → Cell := twoBank p5777 ray5777
theorem signs5777 : ∀ j, Signs p5777 (bank5777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5778 := params 17
abbrev ray5778 := rays 17
def bank5778 : Fin 2 → Cell := twoBank p5778 ray5778
theorem signs5778 : ∀ j, Signs p5778 (bank5778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5779 := params 18
abbrev ray5779 := rays 18
def bank5779 : Fin 2 → Cell := twoBank p5779 ray5779
theorem signs5779 : ∀ j, Signs p5779 (bank5779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5780 := params 19
abbrev ray5780 := rays 19
def bank5780 : Fin 2 → Cell := twoBank p5780 ray5780
theorem signs5780 : ∀ j, Signs p5780 (bank5780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5781 := params 20
abbrev ray5781 := rays 20
def bank5781 : Fin 2 → Cell := twoBank p5781 ray5781
theorem signs5781 : ∀ j, Signs p5781 (bank5781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5782 := params 21
abbrev ray5782 := rays 21
def bank5782 : Fin 2 → Cell := twoBank p5782 ray5782
theorem signs5782 : ∀ j, Signs p5782 (bank5782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5783 := params 22
abbrev ray5783 := rays 22
def bank5783 : Fin 2 → Cell := twoBank p5783 ray5783
theorem signs5783 : ∀ j, Signs p5783 (bank5783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5784 := params 23
abbrev ray5784 := rays 23
def bank5784 : Fin 2 → Cell := twoBank p5784 ray5784
theorem signs5784 : ∀ j, Signs p5784 (bank5784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5785 := params 24
abbrev ray5785 := rays 24
def bank5785 : Fin 2 → Cell := twoBank p5785 ray5785
theorem signs5785 : ∀ j, Signs p5785 (bank5785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5786 := params 25
abbrev ray5786 := rays 25
def bank5786 : Fin 2 → Cell := twoBank p5786 ray5786
theorem signs5786 : ∀ j, Signs p5786 (bank5786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5787 := params 26
abbrev ray5787 := rays 26
def bank5787 : Fin 2 → Cell := twoBank p5787 ray5787
theorem signs5787 : ∀ j, Signs p5787 (bank5787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5788 := params 27
abbrev ray5788 := rays 27
def bank5788 : Fin 2 → Cell := twoBank p5788 ray5788
theorem signs5788 : ∀ j, Signs p5788 (bank5788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5789 := params 28
abbrev ray5789 := rays 28
def bank5789 : Fin 2 → Cell := twoBank p5789 ray5789
theorem signs5789 : ∀ j, Signs p5789 (bank5789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5790 := params 29
abbrev ray5790 := rays 29
def bank5790 : Fin 2 → Cell := twoBank p5790 ray5790
theorem signs5790 : ∀ j, Signs p5790 (bank5790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5791 := params 30
abbrev ray5791 := rays 30
def bank5791 : Fin 2 → Cell := twoBank p5791 ray5791
theorem signs5791 : ∀ j, Signs p5791 (bank5791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5792 := params 31
abbrev ray5792 := rays 31
def bank5792 : Fin 2 → Cell := twoBank p5792 ray5792
theorem signs5792 : ∀ j, Signs p5792 (bank5792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05761_05792
