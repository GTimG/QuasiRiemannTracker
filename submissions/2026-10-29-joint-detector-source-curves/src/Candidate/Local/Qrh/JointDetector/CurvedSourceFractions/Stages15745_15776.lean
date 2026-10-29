/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15745_15776
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95053621965625,95053152684699,95052683387769,95052214074835,95051744745898,95051275400957,95050806040012,95050336663064,95049867270112,95049397861157,95048928436198,95048458995236,95047989538270,95047520065301,95047050576329,95046581071354,95046111550376,95045642013395,95045172460411,95044702891424,95044233306434,95043763705441,95043294088445,95042824455446,95042354806445,95041885141441,95041415460434,95040945763425,95040476050413,95040006321399,95039536576383,95039066815364,95038597038343]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15744+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15745 := params 0
abbrev ray15745 := rays 0
def bank15745 : Fin 1 → Cell := oneBank p15745 ray15745
theorem signs15745 : ∀ j, Signs p15745 (bank15745 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15746 := params 1
abbrev ray15746 := rays 1
def bank15746 : Fin 1 → Cell := oneBank p15746 ray15746
theorem signs15746 : ∀ j, Signs p15746 (bank15746 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15747 := params 2
abbrev ray15747 := rays 2
def bank15747 : Fin 1 → Cell := oneBank p15747 ray15747
theorem signs15747 : ∀ j, Signs p15747 (bank15747 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15748 := params 3
abbrev ray15748 := rays 3
def bank15748 : Fin 1 → Cell := oneBank p15748 ray15748
theorem signs15748 : ∀ j, Signs p15748 (bank15748 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15749 := params 4
abbrev ray15749 := rays 4
def bank15749 : Fin 1 → Cell := oneBank p15749 ray15749
theorem signs15749 : ∀ j, Signs p15749 (bank15749 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15750 := params 5
abbrev ray15750 := rays 5
def bank15750 : Fin 1 → Cell := oneBank p15750 ray15750
theorem signs15750 : ∀ j, Signs p15750 (bank15750 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15751 := params 6
abbrev ray15751 := rays 6
def bank15751 : Fin 1 → Cell := oneBank p15751 ray15751
theorem signs15751 : ∀ j, Signs p15751 (bank15751 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15752 := params 7
abbrev ray15752 := rays 7
def bank15752 : Fin 1 → Cell := oneBank p15752 ray15752
theorem signs15752 : ∀ j, Signs p15752 (bank15752 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15753 := params 8
abbrev ray15753 := rays 8
def bank15753 : Fin 1 → Cell := oneBank p15753 ray15753
theorem signs15753 : ∀ j, Signs p15753 (bank15753 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15754 := params 9
abbrev ray15754 := rays 9
def bank15754 : Fin 1 → Cell := oneBank p15754 ray15754
theorem signs15754 : ∀ j, Signs p15754 (bank15754 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15755 := params 10
abbrev ray15755 := rays 10
def bank15755 : Fin 1 → Cell := oneBank p15755 ray15755
theorem signs15755 : ∀ j, Signs p15755 (bank15755 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15756 := params 11
abbrev ray15756 := rays 11
def bank15756 : Fin 1 → Cell := oneBank p15756 ray15756
theorem signs15756 : ∀ j, Signs p15756 (bank15756 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15757 := params 12
abbrev ray15757 := rays 12
def bank15757 : Fin 1 → Cell := oneBank p15757 ray15757
theorem signs15757 : ∀ j, Signs p15757 (bank15757 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15758 := params 13
abbrev ray15758 := rays 13
def bank15758 : Fin 1 → Cell := oneBank p15758 ray15758
theorem signs15758 : ∀ j, Signs p15758 (bank15758 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15759 := params 14
abbrev ray15759 := rays 14
def bank15759 : Fin 1 → Cell := oneBank p15759 ray15759
theorem signs15759 : ∀ j, Signs p15759 (bank15759 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15760 := params 15
abbrev ray15760 := rays 15
def bank15760 : Fin 1 → Cell := oneBank p15760 ray15760
theorem signs15760 : ∀ j, Signs p15760 (bank15760 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15761 := params 16
abbrev ray15761 := rays 16
def bank15761 : Fin 1 → Cell := oneBank p15761 ray15761
theorem signs15761 : ∀ j, Signs p15761 (bank15761 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15762 := params 17
abbrev ray15762 := rays 17
def bank15762 : Fin 1 → Cell := oneBank p15762 ray15762
theorem signs15762 : ∀ j, Signs p15762 (bank15762 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15763 := params 18
abbrev ray15763 := rays 18
def bank15763 : Fin 1 → Cell := oneBank p15763 ray15763
theorem signs15763 : ∀ j, Signs p15763 (bank15763 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15764 := params 19
abbrev ray15764 := rays 19
def bank15764 : Fin 1 → Cell := oneBank p15764 ray15764
theorem signs15764 : ∀ j, Signs p15764 (bank15764 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15765 := params 20
abbrev ray15765 := rays 20
def bank15765 : Fin 1 → Cell := oneBank p15765 ray15765
theorem signs15765 : ∀ j, Signs p15765 (bank15765 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15766 := params 21
abbrev ray15766 := rays 21
def bank15766 : Fin 1 → Cell := oneBank p15766 ray15766
theorem signs15766 : ∀ j, Signs p15766 (bank15766 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15767 := params 22
abbrev ray15767 := rays 22
def bank15767 : Fin 1 → Cell := oneBank p15767 ray15767
theorem signs15767 : ∀ j, Signs p15767 (bank15767 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15768 := params 23
abbrev ray15768 := rays 23
def bank15768 : Fin 1 → Cell := oneBank p15768 ray15768
theorem signs15768 : ∀ j, Signs p15768 (bank15768 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15769 := params 24
abbrev ray15769 := rays 24
def bank15769 : Fin 1 → Cell := oneBank p15769 ray15769
theorem signs15769 : ∀ j, Signs p15769 (bank15769 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15770 := params 25
abbrev ray15770 := rays 25
def bank15770 : Fin 1 → Cell := oneBank p15770 ray15770
theorem signs15770 : ∀ j, Signs p15770 (bank15770 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15771 := params 26
abbrev ray15771 := rays 26
def bank15771 : Fin 1 → Cell := oneBank p15771 ray15771
theorem signs15771 : ∀ j, Signs p15771 (bank15771 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15772 := params 27
abbrev ray15772 := rays 27
def bank15772 : Fin 1 → Cell := oneBank p15772 ray15772
theorem signs15772 : ∀ j, Signs p15772 (bank15772 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15773 := params 28
abbrev ray15773 := rays 28
def bank15773 : Fin 1 → Cell := oneBank p15773 ray15773
theorem signs15773 : ∀ j, Signs p15773 (bank15773 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15774 := params 29
abbrev ray15774 := rays 29
def bank15774 : Fin 1 → Cell := oneBank p15774 ray15774
theorem signs15774 : ∀ j, Signs p15774 (bank15774 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15775 := params 30
abbrev ray15775 := rays 30
def bank15775 : Fin 1 → Cell := oneBank p15775 ray15775
theorem signs15775 : ∀ j, Signs p15775 (bank15775 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15776 := params 31
abbrev ray15776 := rays 31
def bank15776 : Fin 1 → Cell := oneBank p15776 ray15776
theorem signs15776 : ∀ j, Signs p15776 (bank15776 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15745_15776
