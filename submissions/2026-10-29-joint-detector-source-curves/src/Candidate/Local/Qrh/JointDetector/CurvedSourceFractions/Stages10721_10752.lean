/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10721_10752
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97200541001348,97200159862004,97199778702705,97199397523452,97199016324245,97198635105084,97198253865970,97197872606904,97197491327886,97197110028916,97196728709995,97196347371124,97195966012303,97195584633532,97195203234812,97194821816144,97194440377528,97194058918964,97193677440453,97193295941996,97192914423593,97192532885244,97192151326950,97191769748712,97191388150530,97191006532405,97190624894337,97190243236326,97189861558373,97189479860479,97189098142644,97188716404869,97188334647154]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10720+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10721 := params 0
abbrev ray10721 := rays 0
def bank10721 : Fin 2 → Cell := twoBank p10721 ray10721
theorem signs10721 : ∀ j, Signs p10721 (bank10721 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10722 := params 1
abbrev ray10722 := rays 1
def bank10722 : Fin 2 → Cell := twoBank p10722 ray10722
theorem signs10722 : ∀ j, Signs p10722 (bank10722 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10723 := params 2
abbrev ray10723 := rays 2
def bank10723 : Fin 2 → Cell := twoBank p10723 ray10723
theorem signs10723 : ∀ j, Signs p10723 (bank10723 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10724 := params 3
abbrev ray10724 := rays 3
def bank10724 : Fin 2 → Cell := twoBank p10724 ray10724
theorem signs10724 : ∀ j, Signs p10724 (bank10724 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10725 := params 4
abbrev ray10725 := rays 4
def bank10725 : Fin 2 → Cell := twoBank p10725 ray10725
theorem signs10725 : ∀ j, Signs p10725 (bank10725 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10726 := params 5
abbrev ray10726 := rays 5
def bank10726 : Fin 2 → Cell := twoBank p10726 ray10726
theorem signs10726 : ∀ j, Signs p10726 (bank10726 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10727 := params 6
abbrev ray10727 := rays 6
def bank10727 : Fin 2 → Cell := twoBank p10727 ray10727
theorem signs10727 : ∀ j, Signs p10727 (bank10727 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10728 := params 7
abbrev ray10728 := rays 7
def bank10728 : Fin 2 → Cell := twoBank p10728 ray10728
theorem signs10728 : ∀ j, Signs p10728 (bank10728 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10729 := params 8
abbrev ray10729 := rays 8
def bank10729 : Fin 2 → Cell := twoBank p10729 ray10729
theorem signs10729 : ∀ j, Signs p10729 (bank10729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10730 := params 9
abbrev ray10730 := rays 9
def bank10730 : Fin 2 → Cell := twoBank p10730 ray10730
theorem signs10730 : ∀ j, Signs p10730 (bank10730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10731 := params 10
abbrev ray10731 := rays 10
def bank10731 : Fin 2 → Cell := twoBank p10731 ray10731
theorem signs10731 : ∀ j, Signs p10731 (bank10731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10732 := params 11
abbrev ray10732 := rays 11
def bank10732 : Fin 2 → Cell := twoBank p10732 ray10732
theorem signs10732 : ∀ j, Signs p10732 (bank10732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10733 := params 12
abbrev ray10733 := rays 12
def bank10733 : Fin 2 → Cell := twoBank p10733 ray10733
theorem signs10733 : ∀ j, Signs p10733 (bank10733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10734 := params 13
abbrev ray10734 := rays 13
def bank10734 : Fin 2 → Cell := twoBank p10734 ray10734
theorem signs10734 : ∀ j, Signs p10734 (bank10734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10735 := params 14
abbrev ray10735 := rays 14
def bank10735 : Fin 2 → Cell := twoBank p10735 ray10735
theorem signs10735 : ∀ j, Signs p10735 (bank10735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10736 := params 15
abbrev ray10736 := rays 15
def bank10736 : Fin 2 → Cell := twoBank p10736 ray10736
theorem signs10736 : ∀ j, Signs p10736 (bank10736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10737 := params 16
abbrev ray10737 := rays 16
def bank10737 : Fin 2 → Cell := twoBank p10737 ray10737
theorem signs10737 : ∀ j, Signs p10737 (bank10737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10738 := params 17
abbrev ray10738 := rays 17
def bank10738 : Fin 2 → Cell := twoBank p10738 ray10738
theorem signs10738 : ∀ j, Signs p10738 (bank10738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10739 := params 18
abbrev ray10739 := rays 18
def bank10739 : Fin 2 → Cell := twoBank p10739 ray10739
theorem signs10739 : ∀ j, Signs p10739 (bank10739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10740 := params 19
abbrev ray10740 := rays 19
def bank10740 : Fin 2 → Cell := twoBank p10740 ray10740
theorem signs10740 : ∀ j, Signs p10740 (bank10740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10741 := params 20
abbrev ray10741 := rays 20
def bank10741 : Fin 2 → Cell := twoBank p10741 ray10741
theorem signs10741 : ∀ j, Signs p10741 (bank10741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10742 := params 21
abbrev ray10742 := rays 21
def bank10742 : Fin 2 → Cell := twoBank p10742 ray10742
theorem signs10742 : ∀ j, Signs p10742 (bank10742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10743 := params 22
abbrev ray10743 := rays 22
def bank10743 : Fin 2 → Cell := twoBank p10743 ray10743
theorem signs10743 : ∀ j, Signs p10743 (bank10743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10744 := params 23
abbrev ray10744 := rays 23
def bank10744 : Fin 2 → Cell := twoBank p10744 ray10744
theorem signs10744 : ∀ j, Signs p10744 (bank10744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10745 := params 24
abbrev ray10745 := rays 24
def bank10745 : Fin 2 → Cell := twoBank p10745 ray10745
theorem signs10745 : ∀ j, Signs p10745 (bank10745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10746 := params 25
abbrev ray10746 := rays 25
def bank10746 : Fin 2 → Cell := twoBank p10746 ray10746
theorem signs10746 : ∀ j, Signs p10746 (bank10746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10747 := params 26
abbrev ray10747 := rays 26
def bank10747 : Fin 2 → Cell := twoBank p10747 ray10747
theorem signs10747 : ∀ j, Signs p10747 (bank10747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10748 := params 27
abbrev ray10748 := rays 27
def bank10748 : Fin 2 → Cell := twoBank p10748 ray10748
theorem signs10748 : ∀ j, Signs p10748 (bank10748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10749 := params 28
abbrev ray10749 := rays 28
def bank10749 : Fin 2 → Cell := twoBank p10749 ray10749
theorem signs10749 : ∀ j, Signs p10749 (bank10749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10750 := params 29
abbrev ray10750 := rays 29
def bank10750 : Fin 2 → Cell := twoBank p10750 ray10750
theorem signs10750 : ∀ j, Signs p10750 (bank10750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10751 := params 30
abbrev ray10751 := rays 30
def bank10751 : Fin 2 → Cell := twoBank p10751 ray10751
theorem signs10751 : ∀ j, Signs p10751 (bank10751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10752 := params 31
abbrev ray10752 := rays 31
def bank10752 : Fin 2 → Cell := twoBank p10752 ray10752
theorem signs10752 : ∀ j, Signs p10752 (bank10752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10721_10752
