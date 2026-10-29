/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15649_15680
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95098598411674,95098130667391,95097662907099,95097195130797,95096727338486,95096259530165,95095791705835,95095323865496,95094856009148,95094388136790,95093920248423,95093452344047,95092984423662,95092516487269,95092048534867,95091580566456,95091112582036,95090644581608,95090176565171,95089708532726,95089240484272,95088772419810,95088304339339,95087836242860,95087368130373,95086900001878,95086431857375,95085963696864,95085495520345,95085027327818,95084559119283,95084090894740,95083622654190]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15648+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15649 := params 0
abbrev ray15649 := rays 0
def bank15649 : Fin 1 → Cell := oneBank p15649 ray15649
theorem signs15649 : ∀ j, Signs p15649 (bank15649 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15650 := params 1
abbrev ray15650 := rays 1
def bank15650 : Fin 1 → Cell := oneBank p15650 ray15650
theorem signs15650 : ∀ j, Signs p15650 (bank15650 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15651 := params 2
abbrev ray15651 := rays 2
def bank15651 : Fin 1 → Cell := oneBank p15651 ray15651
theorem signs15651 : ∀ j, Signs p15651 (bank15651 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15652 := params 3
abbrev ray15652 := rays 3
def bank15652 : Fin 1 → Cell := oneBank p15652 ray15652
theorem signs15652 : ∀ j, Signs p15652 (bank15652 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15653 := params 4
abbrev ray15653 := rays 4
def bank15653 : Fin 1 → Cell := oneBank p15653 ray15653
theorem signs15653 : ∀ j, Signs p15653 (bank15653 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15654 := params 5
abbrev ray15654 := rays 5
def bank15654 : Fin 1 → Cell := oneBank p15654 ray15654
theorem signs15654 : ∀ j, Signs p15654 (bank15654 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15655 := params 6
abbrev ray15655 := rays 6
def bank15655 : Fin 1 → Cell := oneBank p15655 ray15655
theorem signs15655 : ∀ j, Signs p15655 (bank15655 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15656 := params 7
abbrev ray15656 := rays 7
def bank15656 : Fin 1 → Cell := oneBank p15656 ray15656
theorem signs15656 : ∀ j, Signs p15656 (bank15656 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15657 := params 8
abbrev ray15657 := rays 8
def bank15657 : Fin 1 → Cell := oneBank p15657 ray15657
theorem signs15657 : ∀ j, Signs p15657 (bank15657 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15658 := params 9
abbrev ray15658 := rays 9
def bank15658 : Fin 1 → Cell := oneBank p15658 ray15658
theorem signs15658 : ∀ j, Signs p15658 (bank15658 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15659 := params 10
abbrev ray15659 := rays 10
def bank15659 : Fin 1 → Cell := oneBank p15659 ray15659
theorem signs15659 : ∀ j, Signs p15659 (bank15659 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15660 := params 11
abbrev ray15660 := rays 11
def bank15660 : Fin 1 → Cell := oneBank p15660 ray15660
theorem signs15660 : ∀ j, Signs p15660 (bank15660 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15661 := params 12
abbrev ray15661 := rays 12
def bank15661 : Fin 1 → Cell := oneBank p15661 ray15661
theorem signs15661 : ∀ j, Signs p15661 (bank15661 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15662 := params 13
abbrev ray15662 := rays 13
def bank15662 : Fin 1 → Cell := oneBank p15662 ray15662
theorem signs15662 : ∀ j, Signs p15662 (bank15662 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15663 := params 14
abbrev ray15663 := rays 14
def bank15663 : Fin 1 → Cell := oneBank p15663 ray15663
theorem signs15663 : ∀ j, Signs p15663 (bank15663 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15664 := params 15
abbrev ray15664 := rays 15
def bank15664 : Fin 1 → Cell := oneBank p15664 ray15664
theorem signs15664 : ∀ j, Signs p15664 (bank15664 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15665 := params 16
abbrev ray15665 := rays 16
def bank15665 : Fin 1 → Cell := oneBank p15665 ray15665
theorem signs15665 : ∀ j, Signs p15665 (bank15665 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15666 := params 17
abbrev ray15666 := rays 17
def bank15666 : Fin 1 → Cell := oneBank p15666 ray15666
theorem signs15666 : ∀ j, Signs p15666 (bank15666 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15667 := params 18
abbrev ray15667 := rays 18
def bank15667 : Fin 1 → Cell := oneBank p15667 ray15667
theorem signs15667 : ∀ j, Signs p15667 (bank15667 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15668 := params 19
abbrev ray15668 := rays 19
def bank15668 : Fin 1 → Cell := oneBank p15668 ray15668
theorem signs15668 : ∀ j, Signs p15668 (bank15668 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15669 := params 20
abbrev ray15669 := rays 20
def bank15669 : Fin 1 → Cell := oneBank p15669 ray15669
theorem signs15669 : ∀ j, Signs p15669 (bank15669 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15670 := params 21
abbrev ray15670 := rays 21
def bank15670 : Fin 1 → Cell := oneBank p15670 ray15670
theorem signs15670 : ∀ j, Signs p15670 (bank15670 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15671 := params 22
abbrev ray15671 := rays 22
def bank15671 : Fin 1 → Cell := oneBank p15671 ray15671
theorem signs15671 : ∀ j, Signs p15671 (bank15671 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15672 := params 23
abbrev ray15672 := rays 23
def bank15672 : Fin 1 → Cell := oneBank p15672 ray15672
theorem signs15672 : ∀ j, Signs p15672 (bank15672 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15673 := params 24
abbrev ray15673 := rays 24
def bank15673 : Fin 1 → Cell := oneBank p15673 ray15673
theorem signs15673 : ∀ j, Signs p15673 (bank15673 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15674 := params 25
abbrev ray15674 := rays 25
def bank15674 : Fin 1 → Cell := oneBank p15674 ray15674
theorem signs15674 : ∀ j, Signs p15674 (bank15674 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15675 := params 26
abbrev ray15675 := rays 26
def bank15675 : Fin 1 → Cell := oneBank p15675 ray15675
theorem signs15675 : ∀ j, Signs p15675 (bank15675 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15676 := params 27
abbrev ray15676 := rays 27
def bank15676 : Fin 1 → Cell := oneBank p15676 ray15676
theorem signs15676 : ∀ j, Signs p15676 (bank15676 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15677 := params 28
abbrev ray15677 := rays 28
def bank15677 : Fin 1 → Cell := oneBank p15677 ray15677
theorem signs15677 : ∀ j, Signs p15677 (bank15677 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15678 := params 29
abbrev ray15678 := rays 29
def bank15678 : Fin 1 → Cell := oneBank p15678 ray15678
theorem signs15678 : ∀ j, Signs p15678 (bank15678 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15679 := params 30
abbrev ray15679 := rays 30
def bank15679 : Fin 1 → Cell := oneBank p15679 ray15679
theorem signs15679 : ∀ j, Signs p15679 (bank15679 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15680 := params 31
abbrev ray15680 := rays 31
def bank15680 : Fin 1 → Cell := oneBank p15680 ray15680
theorem signs15680 : ∀ j, Signs p15680 (bank15680 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15649_15680
