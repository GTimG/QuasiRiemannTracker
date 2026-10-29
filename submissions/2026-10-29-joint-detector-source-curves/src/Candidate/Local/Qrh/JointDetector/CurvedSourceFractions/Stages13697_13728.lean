/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13697_13728
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95980996135402,95980559853405,95980123555134,95979687240590,95979250909773,95978814562683,95978378199320,95977941819685,95977505423778,95977069011599,95976632583148,95976196138425,95975759677431,95975323200166,95974886706630,95974450196823,95974013670745,95973577128397,95973140569779,95972703994891,95972267403733,95971830796305,95971394172608,95970957532642,95970520876407,95970084203903,95969647515131,95969210810091,95968774088782,95968337351206,95967900597362,95967463827250,95967027040871]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13696+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13697 := params 0
abbrev ray13697 := rays 0
def bank13697 : Fin 1 → Cell := oneBank p13697 ray13697
theorem signs13697 : ∀ j, Signs p13697 (bank13697 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13698 := params 1
abbrev ray13698 := rays 1
def bank13698 : Fin 1 → Cell := oneBank p13698 ray13698
theorem signs13698 : ∀ j, Signs p13698 (bank13698 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13699 := params 2
abbrev ray13699 := rays 2
def bank13699 : Fin 1 → Cell := oneBank p13699 ray13699
theorem signs13699 : ∀ j, Signs p13699 (bank13699 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13700 := params 3
abbrev ray13700 := rays 3
def bank13700 : Fin 1 → Cell := oneBank p13700 ray13700
theorem signs13700 : ∀ j, Signs p13700 (bank13700 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13701 := params 4
abbrev ray13701 := rays 4
def bank13701 : Fin 1 → Cell := oneBank p13701 ray13701
theorem signs13701 : ∀ j, Signs p13701 (bank13701 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13702 := params 5
abbrev ray13702 := rays 5
def bank13702 : Fin 1 → Cell := oneBank p13702 ray13702
theorem signs13702 : ∀ j, Signs p13702 (bank13702 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13703 := params 6
abbrev ray13703 := rays 6
def bank13703 : Fin 1 → Cell := oneBank p13703 ray13703
theorem signs13703 : ∀ j, Signs p13703 (bank13703 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13704 := params 7
abbrev ray13704 := rays 7
def bank13704 : Fin 1 → Cell := oneBank p13704 ray13704
theorem signs13704 : ∀ j, Signs p13704 (bank13704 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13705 := params 8
abbrev ray13705 := rays 8
def bank13705 : Fin 1 → Cell := oneBank p13705 ray13705
theorem signs13705 : ∀ j, Signs p13705 (bank13705 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13706 := params 9
abbrev ray13706 := rays 9
def bank13706 : Fin 1 → Cell := oneBank p13706 ray13706
theorem signs13706 : ∀ j, Signs p13706 (bank13706 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13707 := params 10
abbrev ray13707 := rays 10
def bank13707 : Fin 1 → Cell := oneBank p13707 ray13707
theorem signs13707 : ∀ j, Signs p13707 (bank13707 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13708 := params 11
abbrev ray13708 := rays 11
def bank13708 : Fin 1 → Cell := oneBank p13708 ray13708
theorem signs13708 : ∀ j, Signs p13708 (bank13708 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13709 := params 12
abbrev ray13709 := rays 12
def bank13709 : Fin 1 → Cell := oneBank p13709 ray13709
theorem signs13709 : ∀ j, Signs p13709 (bank13709 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13710 := params 13
abbrev ray13710 := rays 13
def bank13710 : Fin 1 → Cell := oneBank p13710 ray13710
theorem signs13710 : ∀ j, Signs p13710 (bank13710 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13711 := params 14
abbrev ray13711 := rays 14
def bank13711 : Fin 1 → Cell := oneBank p13711 ray13711
theorem signs13711 : ∀ j, Signs p13711 (bank13711 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13712 := params 15
abbrev ray13712 := rays 15
def bank13712 : Fin 1 → Cell := oneBank p13712 ray13712
theorem signs13712 : ∀ j, Signs p13712 (bank13712 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13713 := params 16
abbrev ray13713 := rays 16
def bank13713 : Fin 1 → Cell := oneBank p13713 ray13713
theorem signs13713 : ∀ j, Signs p13713 (bank13713 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13714 := params 17
abbrev ray13714 := rays 17
def bank13714 : Fin 1 → Cell := oneBank p13714 ray13714
theorem signs13714 : ∀ j, Signs p13714 (bank13714 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13715 := params 18
abbrev ray13715 := rays 18
def bank13715 : Fin 1 → Cell := oneBank p13715 ray13715
theorem signs13715 : ∀ j, Signs p13715 (bank13715 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13716 := params 19
abbrev ray13716 := rays 19
def bank13716 : Fin 1 → Cell := oneBank p13716 ray13716
theorem signs13716 : ∀ j, Signs p13716 (bank13716 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13717 := params 20
abbrev ray13717 := rays 20
def bank13717 : Fin 1 → Cell := oneBank p13717 ray13717
theorem signs13717 : ∀ j, Signs p13717 (bank13717 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13718 := params 21
abbrev ray13718 := rays 21
def bank13718 : Fin 1 → Cell := oneBank p13718 ray13718
theorem signs13718 : ∀ j, Signs p13718 (bank13718 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13719 := params 22
abbrev ray13719 := rays 22
def bank13719 : Fin 1 → Cell := oneBank p13719 ray13719
theorem signs13719 : ∀ j, Signs p13719 (bank13719 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13720 := params 23
abbrev ray13720 := rays 23
def bank13720 : Fin 1 → Cell := oneBank p13720 ray13720
theorem signs13720 : ∀ j, Signs p13720 (bank13720 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13721 := params 24
abbrev ray13721 := rays 24
def bank13721 : Fin 1 → Cell := oneBank p13721 ray13721
theorem signs13721 : ∀ j, Signs p13721 (bank13721 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13722 := params 25
abbrev ray13722 := rays 25
def bank13722 : Fin 1 → Cell := oneBank p13722 ray13722
theorem signs13722 : ∀ j, Signs p13722 (bank13722 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13723 := params 26
abbrev ray13723 := rays 26
def bank13723 : Fin 1 → Cell := oneBank p13723 ray13723
theorem signs13723 : ∀ j, Signs p13723 (bank13723 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13724 := params 27
abbrev ray13724 := rays 27
def bank13724 : Fin 1 → Cell := oneBank p13724 ray13724
theorem signs13724 : ∀ j, Signs p13724 (bank13724 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13725 := params 28
abbrev ray13725 := rays 28
def bank13725 : Fin 1 → Cell := oneBank p13725 ray13725
theorem signs13725 : ∀ j, Signs p13725 (bank13725 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13726 := params 29
abbrev ray13726 := rays 29
def bank13726 : Fin 1 → Cell := oneBank p13726 ray13726
theorem signs13726 : ∀ j, Signs p13726 (bank13726 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13727 := params 30
abbrev ray13727 := rays 30
def bank13727 : Fin 1 → Cell := oneBank p13727 ray13727
theorem signs13727 : ∀ j, Signs p13727 (bank13727 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13728 := params 31
abbrev ray13728 := rays 31
def bank13728 : Fin 1 → Cell := oneBank p13728 ray13728
theorem signs13728 : ∀ j, Signs p13728 (bank13728 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13697_13728
