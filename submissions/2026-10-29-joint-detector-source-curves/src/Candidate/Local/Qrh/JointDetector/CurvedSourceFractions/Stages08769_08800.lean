/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08769_08800
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97905819302996,97905478163419,97905137002771,97904795821052,97904454618264,97904113394407,97903772149481,97903430883488,97903089596428,97902748288301,97902406959108,97902065608850,97901724237528,97901382845142,97901041431693,97900699997181,97900358541607,97900017064972,97899675567276,97899334048520,97898992508705,97898650947831,97898309365899,97897967762909,97897626138862,97897284493759,97896942827600,97896601140386,97896259432118,97895917702797,97895575952422,97895234180995,97894892388516]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8768+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8769 := params 0
abbrev ray8769 := rays 0
def bank8769 : Fin 2 → Cell := twoBank p8769 ray8769
theorem signs8769 : ∀ j, Signs p8769 (bank8769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8770 := params 1
abbrev ray8770 := rays 1
def bank8770 : Fin 2 → Cell := twoBank p8770 ray8770
theorem signs8770 : ∀ j, Signs p8770 (bank8770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8771 := params 2
abbrev ray8771 := rays 2
def bank8771 : Fin 2 → Cell := twoBank p8771 ray8771
theorem signs8771 : ∀ j, Signs p8771 (bank8771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8772 := params 3
abbrev ray8772 := rays 3
def bank8772 : Fin 2 → Cell := twoBank p8772 ray8772
theorem signs8772 : ∀ j, Signs p8772 (bank8772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8773 := params 4
abbrev ray8773 := rays 4
def bank8773 : Fin 2 → Cell := twoBank p8773 ray8773
theorem signs8773 : ∀ j, Signs p8773 (bank8773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8774 := params 5
abbrev ray8774 := rays 5
def bank8774 : Fin 2 → Cell := twoBank p8774 ray8774
theorem signs8774 : ∀ j, Signs p8774 (bank8774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8775 := params 6
abbrev ray8775 := rays 6
def bank8775 : Fin 2 → Cell := twoBank p8775 ray8775
theorem signs8775 : ∀ j, Signs p8775 (bank8775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8776 := params 7
abbrev ray8776 := rays 7
def bank8776 : Fin 2 → Cell := twoBank p8776 ray8776
theorem signs8776 : ∀ j, Signs p8776 (bank8776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8777 := params 8
abbrev ray8777 := rays 8
def bank8777 : Fin 2 → Cell := twoBank p8777 ray8777
theorem signs8777 : ∀ j, Signs p8777 (bank8777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8778 := params 9
abbrev ray8778 := rays 9
def bank8778 : Fin 2 → Cell := twoBank p8778 ray8778
theorem signs8778 : ∀ j, Signs p8778 (bank8778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8779 := params 10
abbrev ray8779 := rays 10
def bank8779 : Fin 2 → Cell := twoBank p8779 ray8779
theorem signs8779 : ∀ j, Signs p8779 (bank8779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8780 := params 11
abbrev ray8780 := rays 11
def bank8780 : Fin 2 → Cell := twoBank p8780 ray8780
theorem signs8780 : ∀ j, Signs p8780 (bank8780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8781 := params 12
abbrev ray8781 := rays 12
def bank8781 : Fin 2 → Cell := twoBank p8781 ray8781
theorem signs8781 : ∀ j, Signs p8781 (bank8781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8782 := params 13
abbrev ray8782 := rays 13
def bank8782 : Fin 2 → Cell := twoBank p8782 ray8782
theorem signs8782 : ∀ j, Signs p8782 (bank8782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8783 := params 14
abbrev ray8783 := rays 14
def bank8783 : Fin 2 → Cell := twoBank p8783 ray8783
theorem signs8783 : ∀ j, Signs p8783 (bank8783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8784 := params 15
abbrev ray8784 := rays 15
def bank8784 : Fin 2 → Cell := twoBank p8784 ray8784
theorem signs8784 : ∀ j, Signs p8784 (bank8784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8785 := params 16
abbrev ray8785 := rays 16
def bank8785 : Fin 2 → Cell := twoBank p8785 ray8785
theorem signs8785 : ∀ j, Signs p8785 (bank8785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8786 := params 17
abbrev ray8786 := rays 17
def bank8786 : Fin 2 → Cell := twoBank p8786 ray8786
theorem signs8786 : ∀ j, Signs p8786 (bank8786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8787 := params 18
abbrev ray8787 := rays 18
def bank8787 : Fin 2 → Cell := twoBank p8787 ray8787
theorem signs8787 : ∀ j, Signs p8787 (bank8787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8788 := params 19
abbrev ray8788 := rays 19
def bank8788 : Fin 2 → Cell := twoBank p8788 ray8788
theorem signs8788 : ∀ j, Signs p8788 (bank8788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8789 := params 20
abbrev ray8789 := rays 20
def bank8789 : Fin 2 → Cell := twoBank p8789 ray8789
theorem signs8789 : ∀ j, Signs p8789 (bank8789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8790 := params 21
abbrev ray8790 := rays 21
def bank8790 : Fin 2 → Cell := twoBank p8790 ray8790
theorem signs8790 : ∀ j, Signs p8790 (bank8790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8791 := params 22
abbrev ray8791 := rays 22
def bank8791 : Fin 2 → Cell := twoBank p8791 ray8791
theorem signs8791 : ∀ j, Signs p8791 (bank8791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8792 := params 23
abbrev ray8792 := rays 23
def bank8792 : Fin 2 → Cell := twoBank p8792 ray8792
theorem signs8792 : ∀ j, Signs p8792 (bank8792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8793 := params 24
abbrev ray8793 := rays 24
def bank8793 : Fin 2 → Cell := twoBank p8793 ray8793
theorem signs8793 : ∀ j, Signs p8793 (bank8793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8794 := params 25
abbrev ray8794 := rays 25
def bank8794 : Fin 2 → Cell := twoBank p8794 ray8794
theorem signs8794 : ∀ j, Signs p8794 (bank8794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8795 := params 26
abbrev ray8795 := rays 26
def bank8795 : Fin 2 → Cell := twoBank p8795 ray8795
theorem signs8795 : ∀ j, Signs p8795 (bank8795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8796 := params 27
abbrev ray8796 := rays 27
def bank8796 : Fin 2 → Cell := twoBank p8796 ray8796
theorem signs8796 : ∀ j, Signs p8796 (bank8796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8797 := params 28
abbrev ray8797 := rays 28
def bank8797 : Fin 2 → Cell := twoBank p8797 ray8797
theorem signs8797 : ∀ j, Signs p8797 (bank8797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8798 := params 29
abbrev ray8798 := rays 29
def bank8798 : Fin 2 → Cell := twoBank p8798 ray8798
theorem signs8798 : ∀ j, Signs p8798 (bank8798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8799 := params 30
abbrev ray8799 := rays 30
def bank8799 : Fin 2 → Cell := twoBank p8799 ray8799
theorem signs8799 : ∀ j, Signs p8799 (bank8799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8800 := params 31
abbrev ray8800 := rays 31
def bank8800 : Fin 2 → Cell := twoBank p8800 ray8800
theorem signs8800 : ∀ j, Signs p8800 (bank8800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08769_08800
