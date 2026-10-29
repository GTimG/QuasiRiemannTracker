/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04641_04672
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99125960198443,99125712490022,99125464757132,99125216999774,99124969217949,99124721411659,99124473580904,99124225725685,99123977846004,99123729941861,99123482013257,99123234060194,99122986082672,99122738080693,99122490054257,99122242003366,99121993928021,99121745828222,99121497703971,99121249555269,99121001382117,99120753184516,99120504962467,99120256715970,99120008445027,99119760149639,99119511829807,99119263485533,99119015116817,99118766723660,99118518306063,99118269864027,99118021397554]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4640+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4641 := params 0
abbrev ray4641 := rays 0
def bank4641 : Fin 2 → Cell := twoBank p4641 ray4641
theorem signs4641 : ∀ j, Signs p4641 (bank4641 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4642 := params 1
abbrev ray4642 := rays 1
def bank4642 : Fin 2 → Cell := twoBank p4642 ray4642
theorem signs4642 : ∀ j, Signs p4642 (bank4642 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4643 := params 2
abbrev ray4643 := rays 2
def bank4643 : Fin 2 → Cell := twoBank p4643 ray4643
theorem signs4643 : ∀ j, Signs p4643 (bank4643 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4644 := params 3
abbrev ray4644 := rays 3
def bank4644 : Fin 2 → Cell := twoBank p4644 ray4644
theorem signs4644 : ∀ j, Signs p4644 (bank4644 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4645 := params 4
abbrev ray4645 := rays 4
def bank4645 : Fin 2 → Cell := twoBank p4645 ray4645
theorem signs4645 : ∀ j, Signs p4645 (bank4645 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4646 := params 5
abbrev ray4646 := rays 5
def bank4646 : Fin 2 → Cell := twoBank p4646 ray4646
theorem signs4646 : ∀ j, Signs p4646 (bank4646 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4647 := params 6
abbrev ray4647 := rays 6
def bank4647 : Fin 2 → Cell := twoBank p4647 ray4647
theorem signs4647 : ∀ j, Signs p4647 (bank4647 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4648 := params 7
abbrev ray4648 := rays 7
def bank4648 : Fin 2 → Cell := twoBank p4648 ray4648
theorem signs4648 : ∀ j, Signs p4648 (bank4648 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4649 := params 8
abbrev ray4649 := rays 8
def bank4649 : Fin 2 → Cell := twoBank p4649 ray4649
theorem signs4649 : ∀ j, Signs p4649 (bank4649 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4650 := params 9
abbrev ray4650 := rays 9
def bank4650 : Fin 2 → Cell := twoBank p4650 ray4650
theorem signs4650 : ∀ j, Signs p4650 (bank4650 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4651 := params 10
abbrev ray4651 := rays 10
def bank4651 : Fin 2 → Cell := twoBank p4651 ray4651
theorem signs4651 : ∀ j, Signs p4651 (bank4651 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4652 := params 11
abbrev ray4652 := rays 11
def bank4652 : Fin 2 → Cell := twoBank p4652 ray4652
theorem signs4652 : ∀ j, Signs p4652 (bank4652 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4653 := params 12
abbrev ray4653 := rays 12
def bank4653 : Fin 2 → Cell := twoBank p4653 ray4653
theorem signs4653 : ∀ j, Signs p4653 (bank4653 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4654 := params 13
abbrev ray4654 := rays 13
def bank4654 : Fin 2 → Cell := twoBank p4654 ray4654
theorem signs4654 : ∀ j, Signs p4654 (bank4654 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4655 := params 14
abbrev ray4655 := rays 14
def bank4655 : Fin 2 → Cell := twoBank p4655 ray4655
theorem signs4655 : ∀ j, Signs p4655 (bank4655 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4656 := params 15
abbrev ray4656 := rays 15
def bank4656 : Fin 2 → Cell := twoBank p4656 ray4656
theorem signs4656 : ∀ j, Signs p4656 (bank4656 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4657 := params 16
abbrev ray4657 := rays 16
def bank4657 : Fin 2 → Cell := twoBank p4657 ray4657
theorem signs4657 : ∀ j, Signs p4657 (bank4657 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4658 := params 17
abbrev ray4658 := rays 17
def bank4658 : Fin 2 → Cell := twoBank p4658 ray4658
theorem signs4658 : ∀ j, Signs p4658 (bank4658 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4659 := params 18
abbrev ray4659 := rays 18
def bank4659 : Fin 2 → Cell := twoBank p4659 ray4659
theorem signs4659 : ∀ j, Signs p4659 (bank4659 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4660 := params 19
abbrev ray4660 := rays 19
def bank4660 : Fin 2 → Cell := twoBank p4660 ray4660
theorem signs4660 : ∀ j, Signs p4660 (bank4660 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4661 := params 20
abbrev ray4661 := rays 20
def bank4661 : Fin 2 → Cell := twoBank p4661 ray4661
theorem signs4661 : ∀ j, Signs p4661 (bank4661 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4662 := params 21
abbrev ray4662 := rays 21
def bank4662 : Fin 2 → Cell := twoBank p4662 ray4662
theorem signs4662 : ∀ j, Signs p4662 (bank4662 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4663 := params 22
abbrev ray4663 := rays 22
def bank4663 : Fin 2 → Cell := twoBank p4663 ray4663
theorem signs4663 : ∀ j, Signs p4663 (bank4663 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4664 := params 23
abbrev ray4664 := rays 23
def bank4664 : Fin 2 → Cell := twoBank p4664 ray4664
theorem signs4664 : ∀ j, Signs p4664 (bank4664 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4665 := params 24
abbrev ray4665 := rays 24
def bank4665 : Fin 2 → Cell := twoBank p4665 ray4665
theorem signs4665 : ∀ j, Signs p4665 (bank4665 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4666 := params 25
abbrev ray4666 := rays 25
def bank4666 : Fin 2 → Cell := twoBank p4666 ray4666
theorem signs4666 : ∀ j, Signs p4666 (bank4666 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4667 := params 26
abbrev ray4667 := rays 26
def bank4667 : Fin 2 → Cell := twoBank p4667 ray4667
theorem signs4667 : ∀ j, Signs p4667 (bank4667 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4668 := params 27
abbrev ray4668 := rays 27
def bank4668 : Fin 2 → Cell := twoBank p4668 ray4668
theorem signs4668 : ∀ j, Signs p4668 (bank4668 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4669 := params 28
abbrev ray4669 := rays 28
def bank4669 : Fin 2 → Cell := twoBank p4669 ray4669
theorem signs4669 : ∀ j, Signs p4669 (bank4669 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4670 := params 29
abbrev ray4670 := rays 29
def bank4670 : Fin 2 → Cell := twoBank p4670 ray4670
theorem signs4670 : ∀ j, Signs p4670 (bank4670 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4671 := params 30
abbrev ray4671 := rays 30
def bank4671 : Fin 2 → Cell := twoBank p4671 ray4671
theorem signs4671 : ∀ j, Signs p4671 (bank4671 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4672 := params 31
abbrev ray4672 := rays 31
def bank4672 : Fin 2 → Cell := twoBank p4672 ray4672
theorem signs4672 : ∀ j, Signs p4672 (bank4672 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04641_04672
