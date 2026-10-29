/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04769_04800
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99094054991256,99093804159231,99093553302870,99093302422173,99093051517141,99092800587776,99092549634078,99092298656049,99092047653689,99091796626999,99091545575981,99091294500635,99091043400963,99090792276965,99090541128643,99090289955998,99090038759030,99089787537741,99089536292132,99089285022203,99089033727956,99088782409392,99088531066511,99088279699315,99088028307805,99087776891982,99087525451847,99087273987401,99087022498644,99086770985578,99086519448204,99086267886523,99086016300536]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4768+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4769 := params 0
abbrev ray4769 := rays 0
def bank4769 : Fin 2 → Cell := twoBank p4769 ray4769
theorem signs4769 : ∀ j, Signs p4769 (bank4769 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4770 := params 1
abbrev ray4770 := rays 1
def bank4770 : Fin 2 → Cell := twoBank p4770 ray4770
theorem signs4770 : ∀ j, Signs p4770 (bank4770 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4771 := params 2
abbrev ray4771 := rays 2
def bank4771 : Fin 2 → Cell := twoBank p4771 ray4771
theorem signs4771 : ∀ j, Signs p4771 (bank4771 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4772 := params 3
abbrev ray4772 := rays 3
def bank4772 : Fin 2 → Cell := twoBank p4772 ray4772
theorem signs4772 : ∀ j, Signs p4772 (bank4772 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4773 := params 4
abbrev ray4773 := rays 4
def bank4773 : Fin 2 → Cell := twoBank p4773 ray4773
theorem signs4773 : ∀ j, Signs p4773 (bank4773 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4774 := params 5
abbrev ray4774 := rays 5
def bank4774 : Fin 2 → Cell := twoBank p4774 ray4774
theorem signs4774 : ∀ j, Signs p4774 (bank4774 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4775 := params 6
abbrev ray4775 := rays 6
def bank4775 : Fin 2 → Cell := twoBank p4775 ray4775
theorem signs4775 : ∀ j, Signs p4775 (bank4775 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4776 := params 7
abbrev ray4776 := rays 7
def bank4776 : Fin 2 → Cell := twoBank p4776 ray4776
theorem signs4776 : ∀ j, Signs p4776 (bank4776 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4777 := params 8
abbrev ray4777 := rays 8
def bank4777 : Fin 2 → Cell := twoBank p4777 ray4777
theorem signs4777 : ∀ j, Signs p4777 (bank4777 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4778 := params 9
abbrev ray4778 := rays 9
def bank4778 : Fin 2 → Cell := twoBank p4778 ray4778
theorem signs4778 : ∀ j, Signs p4778 (bank4778 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4779 := params 10
abbrev ray4779 := rays 10
def bank4779 : Fin 2 → Cell := twoBank p4779 ray4779
theorem signs4779 : ∀ j, Signs p4779 (bank4779 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4780 := params 11
abbrev ray4780 := rays 11
def bank4780 : Fin 2 → Cell := twoBank p4780 ray4780
theorem signs4780 : ∀ j, Signs p4780 (bank4780 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4781 := params 12
abbrev ray4781 := rays 12
def bank4781 : Fin 2 → Cell := twoBank p4781 ray4781
theorem signs4781 : ∀ j, Signs p4781 (bank4781 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4782 := params 13
abbrev ray4782 := rays 13
def bank4782 : Fin 2 → Cell := twoBank p4782 ray4782
theorem signs4782 : ∀ j, Signs p4782 (bank4782 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4783 := params 14
abbrev ray4783 := rays 14
def bank4783 : Fin 2 → Cell := twoBank p4783 ray4783
theorem signs4783 : ∀ j, Signs p4783 (bank4783 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4784 := params 15
abbrev ray4784 := rays 15
def bank4784 : Fin 2 → Cell := twoBank p4784 ray4784
theorem signs4784 : ∀ j, Signs p4784 (bank4784 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4785 := params 16
abbrev ray4785 := rays 16
def bank4785 : Fin 2 → Cell := twoBank p4785 ray4785
theorem signs4785 : ∀ j, Signs p4785 (bank4785 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4786 := params 17
abbrev ray4786 := rays 17
def bank4786 : Fin 2 → Cell := twoBank p4786 ray4786
theorem signs4786 : ∀ j, Signs p4786 (bank4786 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4787 := params 18
abbrev ray4787 := rays 18
def bank4787 : Fin 2 → Cell := twoBank p4787 ray4787
theorem signs4787 : ∀ j, Signs p4787 (bank4787 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4788 := params 19
abbrev ray4788 := rays 19
def bank4788 : Fin 2 → Cell := twoBank p4788 ray4788
theorem signs4788 : ∀ j, Signs p4788 (bank4788 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4789 := params 20
abbrev ray4789 := rays 20
def bank4789 : Fin 2 → Cell := twoBank p4789 ray4789
theorem signs4789 : ∀ j, Signs p4789 (bank4789 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4790 := params 21
abbrev ray4790 := rays 21
def bank4790 : Fin 2 → Cell := twoBank p4790 ray4790
theorem signs4790 : ∀ j, Signs p4790 (bank4790 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4791 := params 22
abbrev ray4791 := rays 22
def bank4791 : Fin 2 → Cell := twoBank p4791 ray4791
theorem signs4791 : ∀ j, Signs p4791 (bank4791 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4792 := params 23
abbrev ray4792 := rays 23
def bank4792 : Fin 2 → Cell := twoBank p4792 ray4792
theorem signs4792 : ∀ j, Signs p4792 (bank4792 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4793 := params 24
abbrev ray4793 := rays 24
def bank4793 : Fin 2 → Cell := twoBank p4793 ray4793
theorem signs4793 : ∀ j, Signs p4793 (bank4793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4794 := params 25
abbrev ray4794 := rays 25
def bank4794 : Fin 2 → Cell := twoBank p4794 ray4794
theorem signs4794 : ∀ j, Signs p4794 (bank4794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4795 := params 26
abbrev ray4795 := rays 26
def bank4795 : Fin 2 → Cell := twoBank p4795 ray4795
theorem signs4795 : ∀ j, Signs p4795 (bank4795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4796 := params 27
abbrev ray4796 := rays 27
def bank4796 : Fin 2 → Cell := twoBank p4796 ray4796
theorem signs4796 : ∀ j, Signs p4796 (bank4796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4797 := params 28
abbrev ray4797 := rays 28
def bank4797 : Fin 2 → Cell := twoBank p4797 ray4797
theorem signs4797 : ∀ j, Signs p4797 (bank4797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4798 := params 29
abbrev ray4798 := rays 29
def bank4798 : Fin 2 → Cell := twoBank p4798 ray4798
theorem signs4798 : ∀ j, Signs p4798 (bank4798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4799 := params 30
abbrev ray4799 := rays 30
def bank4799 : Fin 2 → Cell := twoBank p4799 ray4799
theorem signs4799 : ∀ j, Signs p4799 (bank4799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4800 := params 31
abbrev ray4800 := rays 31
def bank4800 : Fin 2 → Cell := twoBank p4800 ray4800
theorem signs4800 : ∀ j, Signs p4800 (bank4800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04769_04800
