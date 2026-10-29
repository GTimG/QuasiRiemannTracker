/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12833_12864
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96351838483886,96351416348142,96350994195916,96350572027209,96350149842021,96349727640352,96349305422202,96348883187572,96348460936461,96348038668871,96347616384801,96347194084252,96346771767224,96346349433717,96345927083731,96345504717267,96345082334325,96344659934906,96344237519009,96343815086635,96343392637784,96342970172457,96342547690653,96342125192373,96341702677617,96341280146386,96340857598680,96340435034499,96340012453843,96339589856713,96339167243109,96338744613031,96338321966479]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12832+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12833 := params 0
abbrev ray12833 := rays 0
def bank12833 : Fin 1 → Cell := oneBank p12833 ray12833
theorem signs12833 : ∀ j, Signs p12833 (bank12833 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12834 := params 1
abbrev ray12834 := rays 1
def bank12834 : Fin 1 → Cell := oneBank p12834 ray12834
theorem signs12834 : ∀ j, Signs p12834 (bank12834 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12835 := params 2
abbrev ray12835 := rays 2
def bank12835 : Fin 1 → Cell := oneBank p12835 ray12835
theorem signs12835 : ∀ j, Signs p12835 (bank12835 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12836 := params 3
abbrev ray12836 := rays 3
def bank12836 : Fin 1 → Cell := oneBank p12836 ray12836
theorem signs12836 : ∀ j, Signs p12836 (bank12836 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12837 := params 4
abbrev ray12837 := rays 4
def bank12837 : Fin 1 → Cell := oneBank p12837 ray12837
theorem signs12837 : ∀ j, Signs p12837 (bank12837 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12838 := params 5
abbrev ray12838 := rays 5
def bank12838 : Fin 1 → Cell := oneBank p12838 ray12838
theorem signs12838 : ∀ j, Signs p12838 (bank12838 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12839 := params 6
abbrev ray12839 := rays 6
def bank12839 : Fin 1 → Cell := oneBank p12839 ray12839
theorem signs12839 : ∀ j, Signs p12839 (bank12839 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12840 := params 7
abbrev ray12840 := rays 7
def bank12840 : Fin 1 → Cell := oneBank p12840 ray12840
theorem signs12840 : ∀ j, Signs p12840 (bank12840 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12841 := params 8
abbrev ray12841 := rays 8
def bank12841 : Fin 1 → Cell := oneBank p12841 ray12841
theorem signs12841 : ∀ j, Signs p12841 (bank12841 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12842 := params 9
abbrev ray12842 := rays 9
def bank12842 : Fin 1 → Cell := oneBank p12842 ray12842
theorem signs12842 : ∀ j, Signs p12842 (bank12842 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12843 := params 10
abbrev ray12843 := rays 10
def bank12843 : Fin 1 → Cell := oneBank p12843 ray12843
theorem signs12843 : ∀ j, Signs p12843 (bank12843 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12844 := params 11
abbrev ray12844 := rays 11
def bank12844 : Fin 1 → Cell := oneBank p12844 ray12844
theorem signs12844 : ∀ j, Signs p12844 (bank12844 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12845 := params 12
abbrev ray12845 := rays 12
def bank12845 : Fin 1 → Cell := oneBank p12845 ray12845
theorem signs12845 : ∀ j, Signs p12845 (bank12845 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12846 := params 13
abbrev ray12846 := rays 13
def bank12846 : Fin 1 → Cell := oneBank p12846 ray12846
theorem signs12846 : ∀ j, Signs p12846 (bank12846 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12847 := params 14
abbrev ray12847 := rays 14
def bank12847 : Fin 1 → Cell := oneBank p12847 ray12847
theorem signs12847 : ∀ j, Signs p12847 (bank12847 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12848 := params 15
abbrev ray12848 := rays 15
def bank12848 : Fin 1 → Cell := oneBank p12848 ray12848
theorem signs12848 : ∀ j, Signs p12848 (bank12848 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12849 := params 16
abbrev ray12849 := rays 16
def bank12849 : Fin 1 → Cell := oneBank p12849 ray12849
theorem signs12849 : ∀ j, Signs p12849 (bank12849 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12850 := params 17
abbrev ray12850 := rays 17
def bank12850 : Fin 1 → Cell := oneBank p12850 ray12850
theorem signs12850 : ∀ j, Signs p12850 (bank12850 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12851 := params 18
abbrev ray12851 := rays 18
def bank12851 : Fin 1 → Cell := oneBank p12851 ray12851
theorem signs12851 : ∀ j, Signs p12851 (bank12851 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12852 := params 19
abbrev ray12852 := rays 19
def bank12852 : Fin 1 → Cell := oneBank p12852 ray12852
theorem signs12852 : ∀ j, Signs p12852 (bank12852 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12853 := params 20
abbrev ray12853 := rays 20
def bank12853 : Fin 1 → Cell := oneBank p12853 ray12853
theorem signs12853 : ∀ j, Signs p12853 (bank12853 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12854 := params 21
abbrev ray12854 := rays 21
def bank12854 : Fin 1 → Cell := oneBank p12854 ray12854
theorem signs12854 : ∀ j, Signs p12854 (bank12854 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12855 := params 22
abbrev ray12855 := rays 22
def bank12855 : Fin 1 → Cell := oneBank p12855 ray12855
theorem signs12855 : ∀ j, Signs p12855 (bank12855 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12856 := params 23
abbrev ray12856 := rays 23
def bank12856 : Fin 1 → Cell := oneBank p12856 ray12856
theorem signs12856 : ∀ j, Signs p12856 (bank12856 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12857 := params 24
abbrev ray12857 := rays 24
def bank12857 : Fin 1 → Cell := oneBank p12857 ray12857
theorem signs12857 : ∀ j, Signs p12857 (bank12857 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12858 := params 25
abbrev ray12858 := rays 25
def bank12858 : Fin 1 → Cell := oneBank p12858 ray12858
theorem signs12858 : ∀ j, Signs p12858 (bank12858 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12859 := params 26
abbrev ray12859 := rays 26
def bank12859 : Fin 1 → Cell := oneBank p12859 ray12859
theorem signs12859 : ∀ j, Signs p12859 (bank12859 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12860 := params 27
abbrev ray12860 := rays 27
def bank12860 : Fin 1 → Cell := oneBank p12860 ray12860
theorem signs12860 : ∀ j, Signs p12860 (bank12860 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12861 := params 28
abbrev ray12861 := rays 28
def bank12861 : Fin 1 → Cell := oneBank p12861 ray12861
theorem signs12861 : ∀ j, Signs p12861 (bank12861 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12862 := params 29
abbrev ray12862 := rays 29
def bank12862 : Fin 1 → Cell := oneBank p12862 ray12862
theorem signs12862 : ∀ j, Signs p12862 (bank12862 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12863 := params 30
abbrev ray12863 := rays 30
def bank12863 : Fin 1 → Cell := oneBank p12863 ray12863
theorem signs12863 : ∀ j, Signs p12863 (bank12863 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12864 := params 31
abbrev ray12864 := rays 31
def bank12864 : Fin 1 → Cell := oneBank p12864 ray12864
theorem signs12864 : ∀ j, Signs p12864 (bank12864 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12833_12864
