/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09697_09728
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97580261316249,97579900888493,97579540440229,97579179971458,97578819482180,97578458972396,97578098442106,97577737891311,97577377320011,97577016728207,97576656115899,97576295483088,97575934829775,97575574155960,97575213461644,97574852746828,97574492011512,97574131255696,97573770479381,97573409682568,97573048865257,97572688027449,97572327169144,97571966290343,97571605391047,97571244471256,97570883530971,97570522570192,97570161588920,97569800587155,97569439564898,97569078522149,97568717458910]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9696+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9697 := params 0
abbrev ray9697 := rays 0
def bank9697 : Fin 2 → Cell := twoBank p9697 ray9697
theorem signs9697 : ∀ j, Signs p9697 (bank9697 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9698 := params 1
abbrev ray9698 := rays 1
def bank9698 : Fin 2 → Cell := twoBank p9698 ray9698
theorem signs9698 : ∀ j, Signs p9698 (bank9698 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9699 := params 2
abbrev ray9699 := rays 2
def bank9699 : Fin 2 → Cell := twoBank p9699 ray9699
theorem signs9699 : ∀ j, Signs p9699 (bank9699 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9700 := params 3
abbrev ray9700 := rays 3
def bank9700 : Fin 2 → Cell := twoBank p9700 ray9700
theorem signs9700 : ∀ j, Signs p9700 (bank9700 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9701 := params 4
abbrev ray9701 := rays 4
def bank9701 : Fin 2 → Cell := twoBank p9701 ray9701
theorem signs9701 : ∀ j, Signs p9701 (bank9701 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9702 := params 5
abbrev ray9702 := rays 5
def bank9702 : Fin 2 → Cell := twoBank p9702 ray9702
theorem signs9702 : ∀ j, Signs p9702 (bank9702 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9703 := params 6
abbrev ray9703 := rays 6
def bank9703 : Fin 2 → Cell := twoBank p9703 ray9703
theorem signs9703 : ∀ j, Signs p9703 (bank9703 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9704 := params 7
abbrev ray9704 := rays 7
def bank9704 : Fin 2 → Cell := twoBank p9704 ray9704
theorem signs9704 : ∀ j, Signs p9704 (bank9704 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9705 := params 8
abbrev ray9705 := rays 8
def bank9705 : Fin 2 → Cell := twoBank p9705 ray9705
theorem signs9705 : ∀ j, Signs p9705 (bank9705 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9706 := params 9
abbrev ray9706 := rays 9
def bank9706 : Fin 2 → Cell := twoBank p9706 ray9706
theorem signs9706 : ∀ j, Signs p9706 (bank9706 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9707 := params 10
abbrev ray9707 := rays 10
def bank9707 : Fin 2 → Cell := twoBank p9707 ray9707
theorem signs9707 : ∀ j, Signs p9707 (bank9707 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9708 := params 11
abbrev ray9708 := rays 11
def bank9708 : Fin 2 → Cell := twoBank p9708 ray9708
theorem signs9708 : ∀ j, Signs p9708 (bank9708 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9709 := params 12
abbrev ray9709 := rays 12
def bank9709 : Fin 2 → Cell := twoBank p9709 ray9709
theorem signs9709 : ∀ j, Signs p9709 (bank9709 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9710 := params 13
abbrev ray9710 := rays 13
def bank9710 : Fin 2 → Cell := twoBank p9710 ray9710
theorem signs9710 : ∀ j, Signs p9710 (bank9710 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9711 := params 14
abbrev ray9711 := rays 14
def bank9711 : Fin 2 → Cell := twoBank p9711 ray9711
theorem signs9711 : ∀ j, Signs p9711 (bank9711 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9712 := params 15
abbrev ray9712 := rays 15
def bank9712 : Fin 2 → Cell := twoBank p9712 ray9712
theorem signs9712 : ∀ j, Signs p9712 (bank9712 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9713 := params 16
abbrev ray9713 := rays 16
def bank9713 : Fin 2 → Cell := twoBank p9713 ray9713
theorem signs9713 : ∀ j, Signs p9713 (bank9713 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9714 := params 17
abbrev ray9714 := rays 17
def bank9714 : Fin 2 → Cell := twoBank p9714 ray9714
theorem signs9714 : ∀ j, Signs p9714 (bank9714 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9715 := params 18
abbrev ray9715 := rays 18
def bank9715 : Fin 2 → Cell := twoBank p9715 ray9715
theorem signs9715 : ∀ j, Signs p9715 (bank9715 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9716 := params 19
abbrev ray9716 := rays 19
def bank9716 : Fin 2 → Cell := twoBank p9716 ray9716
theorem signs9716 : ∀ j, Signs p9716 (bank9716 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9717 := params 20
abbrev ray9717 := rays 20
def bank9717 : Fin 2 → Cell := twoBank p9717 ray9717
theorem signs9717 : ∀ j, Signs p9717 (bank9717 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9718 := params 21
abbrev ray9718 := rays 21
def bank9718 : Fin 2 → Cell := twoBank p9718 ray9718
theorem signs9718 : ∀ j, Signs p9718 (bank9718 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9719 := params 22
abbrev ray9719 := rays 22
def bank9719 : Fin 2 → Cell := twoBank p9719 ray9719
theorem signs9719 : ∀ j, Signs p9719 (bank9719 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9720 := params 23
abbrev ray9720 := rays 23
def bank9720 : Fin 2 → Cell := twoBank p9720 ray9720
theorem signs9720 : ∀ j, Signs p9720 (bank9720 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9721 := params 24
abbrev ray9721 := rays 24
def bank9721 : Fin 2 → Cell := twoBank p9721 ray9721
theorem signs9721 : ∀ j, Signs p9721 (bank9721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9722 := params 25
abbrev ray9722 := rays 25
def bank9722 : Fin 2 → Cell := twoBank p9722 ray9722
theorem signs9722 : ∀ j, Signs p9722 (bank9722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9723 := params 26
abbrev ray9723 := rays 26
def bank9723 : Fin 2 → Cell := twoBank p9723 ray9723
theorem signs9723 : ∀ j, Signs p9723 (bank9723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9724 := params 27
abbrev ray9724 := rays 27
def bank9724 : Fin 2 → Cell := twoBank p9724 ray9724
theorem signs9724 : ∀ j, Signs p9724 (bank9724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9725 := params 28
abbrev ray9725 := rays 28
def bank9725 : Fin 2 → Cell := twoBank p9725 ray9725
theorem signs9725 : ∀ j, Signs p9725 (bank9725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9726 := params 29
abbrev ray9726 := rays 29
def bank9726 : Fin 2 → Cell := twoBank p9726 ray9726
theorem signs9726 : ∀ j, Signs p9726 (bank9726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9727 := params 30
abbrev ray9727 := rays 30
def bank9727 : Fin 2 → Cell := twoBank p9727 ray9727
theorem signs9727 : ∀ j, Signs p9727 (bank9727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9728 := params 31
abbrev ray9728 := rays 31
def bank9728 : Fin 2 → Cell := twoBank p9728 ray9728
theorem signs9728 : ∀ j, Signs p9728 (bank9728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09697_09728
