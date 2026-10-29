/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages03681_03712
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99352314739800,99352091020801,99351867276273,99351643506218,99351419710636,99351195889529,99350972042898,99350748170744,99350524273068,99350300349872,99350076401157,99349852426923,99349628427172,99349404401906,99349180351125,99348956274831,99348732173024,99348508045706,99348283892878,99348059714541,99347835510697,99347611281346,99347387026490,99347162746130,99346938440267,99346714108902,99346489752036,99346265369671,99346040961807,99345816528446,99345592069589,99345367585238,99345143075393]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (3680+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p3681 := params 0
abbrev ray3681 := rays 0
def bank3681 : Fin 2 → Cell := twoBank p3681 ray3681
theorem signs3681 : ∀ j, Signs p3681 (bank3681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3682 := params 1
abbrev ray3682 := rays 1
def bank3682 : Fin 2 → Cell := twoBank p3682 ray3682
theorem signs3682 : ∀ j, Signs p3682 (bank3682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3683 := params 2
abbrev ray3683 := rays 2
def bank3683 : Fin 2 → Cell := twoBank p3683 ray3683
theorem signs3683 : ∀ j, Signs p3683 (bank3683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3684 := params 3
abbrev ray3684 := rays 3
def bank3684 : Fin 2 → Cell := twoBank p3684 ray3684
theorem signs3684 : ∀ j, Signs p3684 (bank3684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3685 := params 4
abbrev ray3685 := rays 4
def bank3685 : Fin 2 → Cell := twoBank p3685 ray3685
theorem signs3685 : ∀ j, Signs p3685 (bank3685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3686 := params 5
abbrev ray3686 := rays 5
def bank3686 : Fin 2 → Cell := twoBank p3686 ray3686
theorem signs3686 : ∀ j, Signs p3686 (bank3686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3687 := params 6
abbrev ray3687 := rays 6
def bank3687 : Fin 2 → Cell := twoBank p3687 ray3687
theorem signs3687 : ∀ j, Signs p3687 (bank3687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3688 := params 7
abbrev ray3688 := rays 7
def bank3688 : Fin 2 → Cell := twoBank p3688 ray3688
theorem signs3688 : ∀ j, Signs p3688 (bank3688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3689 := params 8
abbrev ray3689 := rays 8
def bank3689 : Fin 2 → Cell := twoBank p3689 ray3689
theorem signs3689 : ∀ j, Signs p3689 (bank3689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3690 := params 9
abbrev ray3690 := rays 9
def bank3690 : Fin 2 → Cell := twoBank p3690 ray3690
theorem signs3690 : ∀ j, Signs p3690 (bank3690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3691 := params 10
abbrev ray3691 := rays 10
def bank3691 : Fin 2 → Cell := twoBank p3691 ray3691
theorem signs3691 : ∀ j, Signs p3691 (bank3691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3692 := params 11
abbrev ray3692 := rays 11
def bank3692 : Fin 2 → Cell := twoBank p3692 ray3692
theorem signs3692 : ∀ j, Signs p3692 (bank3692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3693 := params 12
abbrev ray3693 := rays 12
def bank3693 : Fin 2 → Cell := twoBank p3693 ray3693
theorem signs3693 : ∀ j, Signs p3693 (bank3693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3694 := params 13
abbrev ray3694 := rays 13
def bank3694 : Fin 2 → Cell := twoBank p3694 ray3694
theorem signs3694 : ∀ j, Signs p3694 (bank3694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3695 := params 14
abbrev ray3695 := rays 14
def bank3695 : Fin 2 → Cell := twoBank p3695 ray3695
theorem signs3695 : ∀ j, Signs p3695 (bank3695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3696 := params 15
abbrev ray3696 := rays 15
def bank3696 : Fin 2 → Cell := twoBank p3696 ray3696
theorem signs3696 : ∀ j, Signs p3696 (bank3696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3697 := params 16
abbrev ray3697 := rays 16
def bank3697 : Fin 2 → Cell := twoBank p3697 ray3697
theorem signs3697 : ∀ j, Signs p3697 (bank3697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3698 := params 17
abbrev ray3698 := rays 17
def bank3698 : Fin 2 → Cell := twoBank p3698 ray3698
theorem signs3698 : ∀ j, Signs p3698 (bank3698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3699 := params 18
abbrev ray3699 := rays 18
def bank3699 : Fin 2 → Cell := twoBank p3699 ray3699
theorem signs3699 : ∀ j, Signs p3699 (bank3699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3700 := params 19
abbrev ray3700 := rays 19
def bank3700 : Fin 2 → Cell := twoBank p3700 ray3700
theorem signs3700 : ∀ j, Signs p3700 (bank3700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3701 := params 20
abbrev ray3701 := rays 20
def bank3701 : Fin 2 → Cell := twoBank p3701 ray3701
theorem signs3701 : ∀ j, Signs p3701 (bank3701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3702 := params 21
abbrev ray3702 := rays 21
def bank3702 : Fin 2 → Cell := twoBank p3702 ray3702
theorem signs3702 : ∀ j, Signs p3702 (bank3702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3703 := params 22
abbrev ray3703 := rays 22
def bank3703 : Fin 2 → Cell := twoBank p3703 ray3703
theorem signs3703 : ∀ j, Signs p3703 (bank3703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3704 := params 23
abbrev ray3704 := rays 23
def bank3704 : Fin 2 → Cell := twoBank p3704 ray3704
theorem signs3704 : ∀ j, Signs p3704 (bank3704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3705 := params 24
abbrev ray3705 := rays 24
def bank3705 : Fin 2 → Cell := twoBank p3705 ray3705
theorem signs3705 : ∀ j, Signs p3705 (bank3705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3706 := params 25
abbrev ray3706 := rays 25
def bank3706 : Fin 2 → Cell := twoBank p3706 ray3706
theorem signs3706 : ∀ j, Signs p3706 (bank3706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3707 := params 26
abbrev ray3707 := rays 26
def bank3707 : Fin 2 → Cell := twoBank p3707 ray3707
theorem signs3707 : ∀ j, Signs p3707 (bank3707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3708 := params 27
abbrev ray3708 := rays 27
def bank3708 : Fin 2 → Cell := twoBank p3708 ray3708
theorem signs3708 : ∀ j, Signs p3708 (bank3708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3709 := params 28
abbrev ray3709 := rays 28
def bank3709 : Fin 2 → Cell := twoBank p3709 ray3709
theorem signs3709 : ∀ j, Signs p3709 (bank3709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3710 := params 29
abbrev ray3710 := rays 29
def bank3710 : Fin 2 → Cell := twoBank p3710 ray3710
theorem signs3710 : ∀ j, Signs p3710 (bank3710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3711 := params 30
abbrev ray3711 := rays 30
def bank3711 : Fin 2 → Cell := twoBank p3711 ray3711
theorem signs3711 : ∀ j, Signs p3711 (bank3711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p3712 := params 31
abbrev ray3712 := rays 31
def bank3712 : Fin 2 → Cell := twoBank p3712 ray3712
theorem signs3712 : ∀ j, Signs p3712 (bank3712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages03681_03712
