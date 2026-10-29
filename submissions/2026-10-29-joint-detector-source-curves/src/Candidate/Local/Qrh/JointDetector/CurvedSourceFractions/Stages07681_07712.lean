/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07681_07712
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98264354108886,98264036290351,98263718450002,98263400587840,98263082703866,98262764798081,98262446870485,98262128921079,98261810949864,98261492956840,98261174942008,98260856905369,98260538846924,98260220766673,98259902664617,98259584540757,98259266395093,98258948227627,98258630038358,98258311827288,98257993594418,98257675339748,98257357063279,98257038765011,98256720444945,98256402103082,98256083739423,98255765353969,98255446946720,98255128517677,98254810066840,98254491594211,98254173099790]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7680+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7681 := params 0
abbrev ray7681 := rays 0
def bank7681 : Fin 2 → Cell := twoBank p7681 ray7681
theorem signs7681 : ∀ j, Signs p7681 (bank7681 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7682 := params 1
abbrev ray7682 := rays 1
def bank7682 : Fin 2 → Cell := twoBank p7682 ray7682
theorem signs7682 : ∀ j, Signs p7682 (bank7682 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7683 := params 2
abbrev ray7683 := rays 2
def bank7683 : Fin 2 → Cell := twoBank p7683 ray7683
theorem signs7683 : ∀ j, Signs p7683 (bank7683 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7684 := params 3
abbrev ray7684 := rays 3
def bank7684 : Fin 2 → Cell := twoBank p7684 ray7684
theorem signs7684 : ∀ j, Signs p7684 (bank7684 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7685 := params 4
abbrev ray7685 := rays 4
def bank7685 : Fin 2 → Cell := twoBank p7685 ray7685
theorem signs7685 : ∀ j, Signs p7685 (bank7685 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7686 := params 5
abbrev ray7686 := rays 5
def bank7686 : Fin 2 → Cell := twoBank p7686 ray7686
theorem signs7686 : ∀ j, Signs p7686 (bank7686 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7687 := params 6
abbrev ray7687 := rays 6
def bank7687 : Fin 2 → Cell := twoBank p7687 ray7687
theorem signs7687 : ∀ j, Signs p7687 (bank7687 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7688 := params 7
abbrev ray7688 := rays 7
def bank7688 : Fin 2 → Cell := twoBank p7688 ray7688
theorem signs7688 : ∀ j, Signs p7688 (bank7688 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7689 := params 8
abbrev ray7689 := rays 8
def bank7689 : Fin 2 → Cell := twoBank p7689 ray7689
theorem signs7689 : ∀ j, Signs p7689 (bank7689 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7690 := params 9
abbrev ray7690 := rays 9
def bank7690 : Fin 2 → Cell := twoBank p7690 ray7690
theorem signs7690 : ∀ j, Signs p7690 (bank7690 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7691 := params 10
abbrev ray7691 := rays 10
def bank7691 : Fin 2 → Cell := twoBank p7691 ray7691
theorem signs7691 : ∀ j, Signs p7691 (bank7691 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7692 := params 11
abbrev ray7692 := rays 11
def bank7692 : Fin 2 → Cell := twoBank p7692 ray7692
theorem signs7692 : ∀ j, Signs p7692 (bank7692 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7693 := params 12
abbrev ray7693 := rays 12
def bank7693 : Fin 2 → Cell := twoBank p7693 ray7693
theorem signs7693 : ∀ j, Signs p7693 (bank7693 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7694 := params 13
abbrev ray7694 := rays 13
def bank7694 : Fin 2 → Cell := twoBank p7694 ray7694
theorem signs7694 : ∀ j, Signs p7694 (bank7694 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7695 := params 14
abbrev ray7695 := rays 14
def bank7695 : Fin 2 → Cell := twoBank p7695 ray7695
theorem signs7695 : ∀ j, Signs p7695 (bank7695 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7696 := params 15
abbrev ray7696 := rays 15
def bank7696 : Fin 2 → Cell := twoBank p7696 ray7696
theorem signs7696 : ∀ j, Signs p7696 (bank7696 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7697 := params 16
abbrev ray7697 := rays 16
def bank7697 : Fin 2 → Cell := twoBank p7697 ray7697
theorem signs7697 : ∀ j, Signs p7697 (bank7697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7698 := params 17
abbrev ray7698 := rays 17
def bank7698 : Fin 2 → Cell := twoBank p7698 ray7698
theorem signs7698 : ∀ j, Signs p7698 (bank7698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7699 := params 18
abbrev ray7699 := rays 18
def bank7699 : Fin 2 → Cell := twoBank p7699 ray7699
theorem signs7699 : ∀ j, Signs p7699 (bank7699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7700 := params 19
abbrev ray7700 := rays 19
def bank7700 : Fin 2 → Cell := twoBank p7700 ray7700
theorem signs7700 : ∀ j, Signs p7700 (bank7700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7701 := params 20
abbrev ray7701 := rays 20
def bank7701 : Fin 2 → Cell := twoBank p7701 ray7701
theorem signs7701 : ∀ j, Signs p7701 (bank7701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7702 := params 21
abbrev ray7702 := rays 21
def bank7702 : Fin 2 → Cell := twoBank p7702 ray7702
theorem signs7702 : ∀ j, Signs p7702 (bank7702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7703 := params 22
abbrev ray7703 := rays 22
def bank7703 : Fin 2 → Cell := twoBank p7703 ray7703
theorem signs7703 : ∀ j, Signs p7703 (bank7703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7704 := params 23
abbrev ray7704 := rays 23
def bank7704 : Fin 2 → Cell := twoBank p7704 ray7704
theorem signs7704 : ∀ j, Signs p7704 (bank7704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7705 := params 24
abbrev ray7705 := rays 24
def bank7705 : Fin 2 → Cell := twoBank p7705 ray7705
theorem signs7705 : ∀ j, Signs p7705 (bank7705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7706 := params 25
abbrev ray7706 := rays 25
def bank7706 : Fin 2 → Cell := twoBank p7706 ray7706
theorem signs7706 : ∀ j, Signs p7706 (bank7706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7707 := params 26
abbrev ray7707 := rays 26
def bank7707 : Fin 2 → Cell := twoBank p7707 ray7707
theorem signs7707 : ∀ j, Signs p7707 (bank7707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7708 := params 27
abbrev ray7708 := rays 27
def bank7708 : Fin 2 → Cell := twoBank p7708 ray7708
theorem signs7708 : ∀ j, Signs p7708 (bank7708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7709 := params 28
abbrev ray7709 := rays 28
def bank7709 : Fin 2 → Cell := twoBank p7709 ray7709
theorem signs7709 : ∀ j, Signs p7709 (bank7709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7710 := params 29
abbrev ray7710 := rays 29
def bank7710 : Fin 2 → Cell := twoBank p7710 ray7710
theorem signs7710 : ∀ j, Signs p7710 (bank7710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7711 := params 30
abbrev ray7711 := rays 30
def bank7711 : Fin 2 → Cell := twoBank p7711 ray7711
theorem signs7711 : ∀ j, Signs p7711 (bank7711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7712 := params 31
abbrev ray7712 := rays 31
def bank7712 : Fin 2 → Cell := twoBank p7712 ray7712
theorem signs7712 : ∀ j, Signs p7712 (bank7712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07681_07712
