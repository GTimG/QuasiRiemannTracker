/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14849_14880
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95467657730748,95467202820551,95466747894270,95466292951906,95465837993459,95465383018929,95464928028316,95464473021620,95464017998841,95463562959979,95463107905035,95462652834008,95462197746899,95461742643708,95461287524435,95460832389080,95460377237643,95459922070125,95459466886525,95459011686844,95458556471081,95458101239237,95457645991312,95457190727306,95456735447220,95456280151053,95455824838805,95455369510477,95454914166068,95454458805579,95454003429010,95453548036361,95453092627632]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14848+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14849 := params 0
abbrev ray14849 := rays 0
def bank14849 : Fin 1 → Cell := oneBank p14849 ray14849
theorem signs14849 : ∀ j, Signs p14849 (bank14849 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14850 := params 1
abbrev ray14850 := rays 1
def bank14850 : Fin 1 → Cell := oneBank p14850 ray14850
theorem signs14850 : ∀ j, Signs p14850 (bank14850 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14851 := params 2
abbrev ray14851 := rays 2
def bank14851 : Fin 1 → Cell := oneBank p14851 ray14851
theorem signs14851 : ∀ j, Signs p14851 (bank14851 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14852 := params 3
abbrev ray14852 := rays 3
def bank14852 : Fin 1 → Cell := oneBank p14852 ray14852
theorem signs14852 : ∀ j, Signs p14852 (bank14852 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14853 := params 4
abbrev ray14853 := rays 4
def bank14853 : Fin 1 → Cell := oneBank p14853 ray14853
theorem signs14853 : ∀ j, Signs p14853 (bank14853 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14854 := params 5
abbrev ray14854 := rays 5
def bank14854 : Fin 1 → Cell := oneBank p14854 ray14854
theorem signs14854 : ∀ j, Signs p14854 (bank14854 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14855 := params 6
abbrev ray14855 := rays 6
def bank14855 : Fin 1 → Cell := oneBank p14855 ray14855
theorem signs14855 : ∀ j, Signs p14855 (bank14855 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14856 := params 7
abbrev ray14856 := rays 7
def bank14856 : Fin 1 → Cell := oneBank p14856 ray14856
theorem signs14856 : ∀ j, Signs p14856 (bank14856 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14857 := params 8
abbrev ray14857 := rays 8
def bank14857 : Fin 1 → Cell := oneBank p14857 ray14857
theorem signs14857 : ∀ j, Signs p14857 (bank14857 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14858 := params 9
abbrev ray14858 := rays 9
def bank14858 : Fin 1 → Cell := oneBank p14858 ray14858
theorem signs14858 : ∀ j, Signs p14858 (bank14858 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14859 := params 10
abbrev ray14859 := rays 10
def bank14859 : Fin 1 → Cell := oneBank p14859 ray14859
theorem signs14859 : ∀ j, Signs p14859 (bank14859 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14860 := params 11
abbrev ray14860 := rays 11
def bank14860 : Fin 1 → Cell := oneBank p14860 ray14860
theorem signs14860 : ∀ j, Signs p14860 (bank14860 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14861 := params 12
abbrev ray14861 := rays 12
def bank14861 : Fin 1 → Cell := oneBank p14861 ray14861
theorem signs14861 : ∀ j, Signs p14861 (bank14861 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14862 := params 13
abbrev ray14862 := rays 13
def bank14862 : Fin 1 → Cell := oneBank p14862 ray14862
theorem signs14862 : ∀ j, Signs p14862 (bank14862 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14863 := params 14
abbrev ray14863 := rays 14
def bank14863 : Fin 1 → Cell := oneBank p14863 ray14863
theorem signs14863 : ∀ j, Signs p14863 (bank14863 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14864 := params 15
abbrev ray14864 := rays 15
def bank14864 : Fin 1 → Cell := oneBank p14864 ray14864
theorem signs14864 : ∀ j, Signs p14864 (bank14864 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14865 := params 16
abbrev ray14865 := rays 16
def bank14865 : Fin 1 → Cell := oneBank p14865 ray14865
theorem signs14865 : ∀ j, Signs p14865 (bank14865 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14866 := params 17
abbrev ray14866 := rays 17
def bank14866 : Fin 1 → Cell := oneBank p14866 ray14866
theorem signs14866 : ∀ j, Signs p14866 (bank14866 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14867 := params 18
abbrev ray14867 := rays 18
def bank14867 : Fin 1 → Cell := oneBank p14867 ray14867
theorem signs14867 : ∀ j, Signs p14867 (bank14867 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14868 := params 19
abbrev ray14868 := rays 19
def bank14868 : Fin 1 → Cell := oneBank p14868 ray14868
theorem signs14868 : ∀ j, Signs p14868 (bank14868 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14869 := params 20
abbrev ray14869 := rays 20
def bank14869 : Fin 1 → Cell := oneBank p14869 ray14869
theorem signs14869 : ∀ j, Signs p14869 (bank14869 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14870 := params 21
abbrev ray14870 := rays 21
def bank14870 : Fin 1 → Cell := oneBank p14870 ray14870
theorem signs14870 : ∀ j, Signs p14870 (bank14870 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14871 := params 22
abbrev ray14871 := rays 22
def bank14871 : Fin 1 → Cell := oneBank p14871 ray14871
theorem signs14871 : ∀ j, Signs p14871 (bank14871 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14872 := params 23
abbrev ray14872 := rays 23
def bank14872 : Fin 1 → Cell := oneBank p14872 ray14872
theorem signs14872 : ∀ j, Signs p14872 (bank14872 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14873 := params 24
abbrev ray14873 := rays 24
def bank14873 : Fin 1 → Cell := oneBank p14873 ray14873
theorem signs14873 : ∀ j, Signs p14873 (bank14873 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14874 := params 25
abbrev ray14874 := rays 25
def bank14874 : Fin 1 → Cell := oneBank p14874 ray14874
theorem signs14874 : ∀ j, Signs p14874 (bank14874 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14875 := params 26
abbrev ray14875 := rays 26
def bank14875 : Fin 1 → Cell := oneBank p14875 ray14875
theorem signs14875 : ∀ j, Signs p14875 (bank14875 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14876 := params 27
abbrev ray14876 := rays 27
def bank14876 : Fin 1 → Cell := oneBank p14876 ray14876
theorem signs14876 : ∀ j, Signs p14876 (bank14876 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14877 := params 28
abbrev ray14877 := rays 28
def bank14877 : Fin 1 → Cell := oneBank p14877 ray14877
theorem signs14877 : ∀ j, Signs p14877 (bank14877 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14878 := params 29
abbrev ray14878 := rays 29
def bank14878 : Fin 1 → Cell := oneBank p14878 ray14878
theorem signs14878 : ∀ j, Signs p14878 (bank14878 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14879 := params 30
abbrev ray14879 := rays 30
def bank14879 : Fin 1 → Cell := oneBank p14879 ray14879
theorem signs14879 : ∀ j, Signs p14879 (bank14879 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14880 := params 31
abbrev ray14880 := rays 31
def bank14880 : Fin 1 → Cell := oneBank p14880 ray14880
theorem signs14880 : ∀ j, Signs p14880 (bank14880 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14849_14880
