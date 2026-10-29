/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02721_02752
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99555130698538,99554932049109,99554733372958,99554534670086,99554335940495,99554137184185,99553938401158,99553739591415,99553540754958,99553341891788,99553143001906,99552944085314,99552745142013,99552546172004,99552347175288,99552148151867,99551949101742,99551750024915,99551550921387,99551351791159,99551152634232,99550953450608,99550754240288,99550555003273,99550355739565,99550156449165,99549957132074,99549757788294,99549558417826,99549359020671,99549159596831,99548960146307,99548760669100]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2720+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2721 := params 0
abbrev ray2721 := rays 0
def bank2721 : Fin 2 → Cell := twoBank p2721 ray2721
theorem signs2721 : ∀ j, Signs p2721 (bank2721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2722 := params 1
abbrev ray2722 := rays 1
def bank2722 : Fin 2 → Cell := twoBank p2722 ray2722
theorem signs2722 : ∀ j, Signs p2722 (bank2722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2723 := params 2
abbrev ray2723 := rays 2
def bank2723 : Fin 2 → Cell := twoBank p2723 ray2723
theorem signs2723 : ∀ j, Signs p2723 (bank2723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2724 := params 3
abbrev ray2724 := rays 3
def bank2724 : Fin 2 → Cell := twoBank p2724 ray2724
theorem signs2724 : ∀ j, Signs p2724 (bank2724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2725 := params 4
abbrev ray2725 := rays 4
def bank2725 : Fin 2 → Cell := twoBank p2725 ray2725
theorem signs2725 : ∀ j, Signs p2725 (bank2725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2726 := params 5
abbrev ray2726 := rays 5
def bank2726 : Fin 2 → Cell := twoBank p2726 ray2726
theorem signs2726 : ∀ j, Signs p2726 (bank2726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2727 := params 6
abbrev ray2727 := rays 6
def bank2727 : Fin 2 → Cell := twoBank p2727 ray2727
theorem signs2727 : ∀ j, Signs p2727 (bank2727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2728 := params 7
abbrev ray2728 := rays 7
def bank2728 : Fin 2 → Cell := twoBank p2728 ray2728
theorem signs2728 : ∀ j, Signs p2728 (bank2728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2729 := params 8
abbrev ray2729 := rays 8
def bank2729 : Fin 2 → Cell := twoBank p2729 ray2729
theorem signs2729 : ∀ j, Signs p2729 (bank2729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2730 := params 9
abbrev ray2730 := rays 9
def bank2730 : Fin 2 → Cell := twoBank p2730 ray2730
theorem signs2730 : ∀ j, Signs p2730 (bank2730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2731 := params 10
abbrev ray2731 := rays 10
def bank2731 : Fin 2 → Cell := twoBank p2731 ray2731
theorem signs2731 : ∀ j, Signs p2731 (bank2731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2732 := params 11
abbrev ray2732 := rays 11
def bank2732 : Fin 2 → Cell := twoBank p2732 ray2732
theorem signs2732 : ∀ j, Signs p2732 (bank2732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2733 := params 12
abbrev ray2733 := rays 12
def bank2733 : Fin 2 → Cell := twoBank p2733 ray2733
theorem signs2733 : ∀ j, Signs p2733 (bank2733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2734 := params 13
abbrev ray2734 := rays 13
def bank2734 : Fin 2 → Cell := twoBank p2734 ray2734
theorem signs2734 : ∀ j, Signs p2734 (bank2734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2735 := params 14
abbrev ray2735 := rays 14
def bank2735 : Fin 2 → Cell := twoBank p2735 ray2735
theorem signs2735 : ∀ j, Signs p2735 (bank2735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2736 := params 15
abbrev ray2736 := rays 15
def bank2736 : Fin 2 → Cell := twoBank p2736 ray2736
theorem signs2736 : ∀ j, Signs p2736 (bank2736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2737 := params 16
abbrev ray2737 := rays 16
def bank2737 : Fin 2 → Cell := twoBank p2737 ray2737
theorem signs2737 : ∀ j, Signs p2737 (bank2737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2738 := params 17
abbrev ray2738 := rays 17
def bank2738 : Fin 2 → Cell := twoBank p2738 ray2738
theorem signs2738 : ∀ j, Signs p2738 (bank2738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2739 := params 18
abbrev ray2739 := rays 18
def bank2739 : Fin 2 → Cell := twoBank p2739 ray2739
theorem signs2739 : ∀ j, Signs p2739 (bank2739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2740 := params 19
abbrev ray2740 := rays 19
def bank2740 : Fin 2 → Cell := twoBank p2740 ray2740
theorem signs2740 : ∀ j, Signs p2740 (bank2740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2741 := params 20
abbrev ray2741 := rays 20
def bank2741 : Fin 2 → Cell := twoBank p2741 ray2741
theorem signs2741 : ∀ j, Signs p2741 (bank2741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2742 := params 21
abbrev ray2742 := rays 21
def bank2742 : Fin 2 → Cell := twoBank p2742 ray2742
theorem signs2742 : ∀ j, Signs p2742 (bank2742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2743 := params 22
abbrev ray2743 := rays 22
def bank2743 : Fin 2 → Cell := twoBank p2743 ray2743
theorem signs2743 : ∀ j, Signs p2743 (bank2743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2744 := params 23
abbrev ray2744 := rays 23
def bank2744 : Fin 2 → Cell := twoBank p2744 ray2744
theorem signs2744 : ∀ j, Signs p2744 (bank2744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2745 := params 24
abbrev ray2745 := rays 24
def bank2745 : Fin 2 → Cell := twoBank p2745 ray2745
theorem signs2745 : ∀ j, Signs p2745 (bank2745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2746 := params 25
abbrev ray2746 := rays 25
def bank2746 : Fin 2 → Cell := twoBank p2746 ray2746
theorem signs2746 : ∀ j, Signs p2746 (bank2746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2747 := params 26
abbrev ray2747 := rays 26
def bank2747 : Fin 2 → Cell := twoBank p2747 ray2747
theorem signs2747 : ∀ j, Signs p2747 (bank2747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2748 := params 27
abbrev ray2748 := rays 27
def bank2748 : Fin 2 → Cell := twoBank p2748 ray2748
theorem signs2748 : ∀ j, Signs p2748 (bank2748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2749 := params 28
abbrev ray2749 := rays 28
def bank2749 : Fin 2 → Cell := twoBank p2749 ray2749
theorem signs2749 : ∀ j, Signs p2749 (bank2749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2750 := params 29
abbrev ray2750 := rays 29
def bank2750 : Fin 2 → Cell := twoBank p2750 ray2750
theorem signs2750 : ∀ j, Signs p2750 (bank2750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2751 := params 30
abbrev ray2751 := rays 30
def bank2751 : Fin 2 → Cell := twoBank p2751 ray2751
theorem signs2751 : ∀ j, Signs p2751 (bank2751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2752 := params 31
abbrev ray2752 := rays 31
def bank2752 : Fin 2 → Cell := twoBank p2752 ray2752
theorem signs2752 : ∀ j, Signs p2752 (bank2752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02721_02752
