/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10817_10848
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97163860701508,97163477648782,97163094576149,97162711483610,97162328371165,97161945238815,97161562086560,97161178914401,97160795722339,97160412510373,97160029278505,97159646026735,97159262755063,97158879463490,97158496152016,97158112820642,97157729469368,97157346098195,97156962707124,97156579296154,97156195865287,97155812414523,97155428943862,97155045453305,97154661942852,97154278412504,97153894862261,97153511292124,97153127702094,97152744092170,97152360462354,97151976812646,97151593143046]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10816+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10817 := params 0
abbrev ray10817 := rays 0
def bank10817 : Fin 2 → Cell := twoBank p10817 ray10817
theorem signs10817 : ∀ j, Signs p10817 (bank10817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10818 := params 1
abbrev ray10818 := rays 1
def bank10818 : Fin 2 → Cell := twoBank p10818 ray10818
theorem signs10818 : ∀ j, Signs p10818 (bank10818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10819 := params 2
abbrev ray10819 := rays 2
def bank10819 : Fin 2 → Cell := twoBank p10819 ray10819
theorem signs10819 : ∀ j, Signs p10819 (bank10819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10820 := params 3
abbrev ray10820 := rays 3
def bank10820 : Fin 2 → Cell := twoBank p10820 ray10820
theorem signs10820 : ∀ j, Signs p10820 (bank10820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10821 := params 4
abbrev ray10821 := rays 4
def bank10821 : Fin 2 → Cell := twoBank p10821 ray10821
theorem signs10821 : ∀ j, Signs p10821 (bank10821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10822 := params 5
abbrev ray10822 := rays 5
def bank10822 : Fin 2 → Cell := twoBank p10822 ray10822
theorem signs10822 : ∀ j, Signs p10822 (bank10822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10823 := params 6
abbrev ray10823 := rays 6
def bank10823 : Fin 2 → Cell := twoBank p10823 ray10823
theorem signs10823 : ∀ j, Signs p10823 (bank10823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10824 := params 7
abbrev ray10824 := rays 7
def bank10824 : Fin 2 → Cell := twoBank p10824 ray10824
theorem signs10824 : ∀ j, Signs p10824 (bank10824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10825 := params 8
abbrev ray10825 := rays 8
def bank10825 : Fin 2 → Cell := twoBank p10825 ray10825
theorem signs10825 : ∀ j, Signs p10825 (bank10825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10826 := params 9
abbrev ray10826 := rays 9
def bank10826 : Fin 2 → Cell := twoBank p10826 ray10826
theorem signs10826 : ∀ j, Signs p10826 (bank10826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10827 := params 10
abbrev ray10827 := rays 10
def bank10827 : Fin 2 → Cell := twoBank p10827 ray10827
theorem signs10827 : ∀ j, Signs p10827 (bank10827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10828 := params 11
abbrev ray10828 := rays 11
def bank10828 : Fin 2 → Cell := twoBank p10828 ray10828
theorem signs10828 : ∀ j, Signs p10828 (bank10828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10829 := params 12
abbrev ray10829 := rays 12
def bank10829 : Fin 2 → Cell := twoBank p10829 ray10829
theorem signs10829 : ∀ j, Signs p10829 (bank10829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10830 := params 13
abbrev ray10830 := rays 13
def bank10830 : Fin 2 → Cell := twoBank p10830 ray10830
theorem signs10830 : ∀ j, Signs p10830 (bank10830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10831 := params 14
abbrev ray10831 := rays 14
def bank10831 : Fin 2 → Cell := twoBank p10831 ray10831
theorem signs10831 : ∀ j, Signs p10831 (bank10831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10832 := params 15
abbrev ray10832 := rays 15
def bank10832 : Fin 2 → Cell := twoBank p10832 ray10832
theorem signs10832 : ∀ j, Signs p10832 (bank10832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10833 := params 16
abbrev ray10833 := rays 16
def bank10833 : Fin 2 → Cell := twoBank p10833 ray10833
theorem signs10833 : ∀ j, Signs p10833 (bank10833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10834 := params 17
abbrev ray10834 := rays 17
def bank10834 : Fin 2 → Cell := twoBank p10834 ray10834
theorem signs10834 : ∀ j, Signs p10834 (bank10834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10835 := params 18
abbrev ray10835 := rays 18
def bank10835 : Fin 2 → Cell := twoBank p10835 ray10835
theorem signs10835 : ∀ j, Signs p10835 (bank10835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10836 := params 19
abbrev ray10836 := rays 19
def bank10836 : Fin 2 → Cell := twoBank p10836 ray10836
theorem signs10836 : ∀ j, Signs p10836 (bank10836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10837 := params 20
abbrev ray10837 := rays 20
def bank10837 : Fin 2 → Cell := twoBank p10837 ray10837
theorem signs10837 : ∀ j, Signs p10837 (bank10837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10838 := params 21
abbrev ray10838 := rays 21
def bank10838 : Fin 2 → Cell := twoBank p10838 ray10838
theorem signs10838 : ∀ j, Signs p10838 (bank10838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10839 := params 22
abbrev ray10839 := rays 22
def bank10839 : Fin 2 → Cell := twoBank p10839 ray10839
theorem signs10839 : ∀ j, Signs p10839 (bank10839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10840 := params 23
abbrev ray10840 := rays 23
def bank10840 : Fin 2 → Cell := twoBank p10840 ray10840
theorem signs10840 : ∀ j, Signs p10840 (bank10840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10841 := params 24
abbrev ray10841 := rays 24
def bank10841 : Fin 2 → Cell := twoBank p10841 ray10841
theorem signs10841 : ∀ j, Signs p10841 (bank10841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10842 := params 25
abbrev ray10842 := rays 25
def bank10842 : Fin 2 → Cell := twoBank p10842 ray10842
theorem signs10842 : ∀ j, Signs p10842 (bank10842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10843 := params 26
abbrev ray10843 := rays 26
def bank10843 : Fin 2 → Cell := twoBank p10843 ray10843
theorem signs10843 : ∀ j, Signs p10843 (bank10843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10844 := params 27
abbrev ray10844 := rays 27
def bank10844 : Fin 2 → Cell := twoBank p10844 ray10844
theorem signs10844 : ∀ j, Signs p10844 (bank10844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10845 := params 28
abbrev ray10845 := rays 28
def bank10845 : Fin 2 → Cell := twoBank p10845 ray10845
theorem signs10845 : ∀ j, Signs p10845 (bank10845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10846 := params 29
abbrev ray10846 := rays 29
def bank10846 : Fin 2 → Cell := twoBank p10846 ray10846
theorem signs10846 : ∀ j, Signs p10846 (bank10846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10847 := params 30
abbrev ray10847 := rays 30
def bank10847 : Fin 2 → Cell := twoBank p10847 ray10847
theorem signs10847 : ∀ j, Signs p10847 (bank10847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10848 := params 31
abbrev ray10848 := rays 31
def bank10848 : Fin 2 → Cell := twoBank p10848 ray10848
theorem signs10848 : ∀ j, Signs p10848 (bank10848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10817_10848
