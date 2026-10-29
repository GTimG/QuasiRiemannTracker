/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15841_15872
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95008498026698,95008027209641,95007556376585,95007085527530,95006614662477,95006143781425,95005672884374,95005201971324,95004731042276,95004260097229,95003789136184,95003318159140,95002847166098,95002376157058,95001905132019,95001434090982,95000963033947,95000491960913,95000020871881,94999549766851,94999078645823,94998607508797,94998136355773,94997665186751,94997194001731,94996722800714,94996251583699,94995780350686,94995309101676,94994837836668,94994366555662,94993895258659,94993423945658]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15840+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15841 := params 0
abbrev ray15841 := rays 0
def bank15841 : Fin 1 → Cell := oneBank p15841 ray15841
theorem signs15841 : ∀ j, Signs p15841 (bank15841 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15842 := params 1
abbrev ray15842 := rays 1
def bank15842 : Fin 1 → Cell := oneBank p15842 ray15842
theorem signs15842 : ∀ j, Signs p15842 (bank15842 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15843 := params 2
abbrev ray15843 := rays 2
def bank15843 : Fin 1 → Cell := oneBank p15843 ray15843
theorem signs15843 : ∀ j, Signs p15843 (bank15843 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15844 := params 3
abbrev ray15844 := rays 3
def bank15844 : Fin 1 → Cell := oneBank p15844 ray15844
theorem signs15844 : ∀ j, Signs p15844 (bank15844 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15845 := params 4
abbrev ray15845 := rays 4
def bank15845 : Fin 1 → Cell := oneBank p15845 ray15845
theorem signs15845 : ∀ j, Signs p15845 (bank15845 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15846 := params 5
abbrev ray15846 := rays 5
def bank15846 : Fin 1 → Cell := oneBank p15846 ray15846
theorem signs15846 : ∀ j, Signs p15846 (bank15846 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15847 := params 6
abbrev ray15847 := rays 6
def bank15847 : Fin 1 → Cell := oneBank p15847 ray15847
theorem signs15847 : ∀ j, Signs p15847 (bank15847 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15848 := params 7
abbrev ray15848 := rays 7
def bank15848 : Fin 1 → Cell := oneBank p15848 ray15848
theorem signs15848 : ∀ j, Signs p15848 (bank15848 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15849 := params 8
abbrev ray15849 := rays 8
def bank15849 : Fin 1 → Cell := oneBank p15849 ray15849
theorem signs15849 : ∀ j, Signs p15849 (bank15849 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15850 := params 9
abbrev ray15850 := rays 9
def bank15850 : Fin 1 → Cell := oneBank p15850 ray15850
theorem signs15850 : ∀ j, Signs p15850 (bank15850 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15851 := params 10
abbrev ray15851 := rays 10
def bank15851 : Fin 1 → Cell := oneBank p15851 ray15851
theorem signs15851 : ∀ j, Signs p15851 (bank15851 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15852 := params 11
abbrev ray15852 := rays 11
def bank15852 : Fin 1 → Cell := oneBank p15852 ray15852
theorem signs15852 : ∀ j, Signs p15852 (bank15852 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15853 := params 12
abbrev ray15853 := rays 12
def bank15853 : Fin 1 → Cell := oneBank p15853 ray15853
theorem signs15853 : ∀ j, Signs p15853 (bank15853 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15854 := params 13
abbrev ray15854 := rays 13
def bank15854 : Fin 1 → Cell := oneBank p15854 ray15854
theorem signs15854 : ∀ j, Signs p15854 (bank15854 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15855 := params 14
abbrev ray15855 := rays 14
def bank15855 : Fin 1 → Cell := oneBank p15855 ray15855
theorem signs15855 : ∀ j, Signs p15855 (bank15855 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15856 := params 15
abbrev ray15856 := rays 15
def bank15856 : Fin 1 → Cell := oneBank p15856 ray15856
theorem signs15856 : ∀ j, Signs p15856 (bank15856 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15857 := params 16
abbrev ray15857 := rays 16
def bank15857 : Fin 1 → Cell := oneBank p15857 ray15857
theorem signs15857 : ∀ j, Signs p15857 (bank15857 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15858 := params 17
abbrev ray15858 := rays 17
def bank15858 : Fin 1 → Cell := oneBank p15858 ray15858
theorem signs15858 : ∀ j, Signs p15858 (bank15858 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15859 := params 18
abbrev ray15859 := rays 18
def bank15859 : Fin 1 → Cell := oneBank p15859 ray15859
theorem signs15859 : ∀ j, Signs p15859 (bank15859 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15860 := params 19
abbrev ray15860 := rays 19
def bank15860 : Fin 1 → Cell := oneBank p15860 ray15860
theorem signs15860 : ∀ j, Signs p15860 (bank15860 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15861 := params 20
abbrev ray15861 := rays 20
def bank15861 : Fin 1 → Cell := oneBank p15861 ray15861
theorem signs15861 : ∀ j, Signs p15861 (bank15861 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15862 := params 21
abbrev ray15862 := rays 21
def bank15862 : Fin 1 → Cell := oneBank p15862 ray15862
theorem signs15862 : ∀ j, Signs p15862 (bank15862 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15863 := params 22
abbrev ray15863 := rays 22
def bank15863 : Fin 1 → Cell := oneBank p15863 ray15863
theorem signs15863 : ∀ j, Signs p15863 (bank15863 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15864 := params 23
abbrev ray15864 := rays 23
def bank15864 : Fin 1 → Cell := oneBank p15864 ray15864
theorem signs15864 : ∀ j, Signs p15864 (bank15864 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15865 := params 24
abbrev ray15865 := rays 24
def bank15865 : Fin 1 → Cell := oneBank p15865 ray15865
theorem signs15865 : ∀ j, Signs p15865 (bank15865 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15866 := params 25
abbrev ray15866 := rays 25
def bank15866 : Fin 1 → Cell := oneBank p15866 ray15866
theorem signs15866 : ∀ j, Signs p15866 (bank15866 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15867 := params 26
abbrev ray15867 := rays 26
def bank15867 : Fin 1 → Cell := oneBank p15867 ray15867
theorem signs15867 : ∀ j, Signs p15867 (bank15867 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15868 := params 27
abbrev ray15868 := rays 27
def bank15868 : Fin 1 → Cell := oneBank p15868 ray15868
theorem signs15868 : ∀ j, Signs p15868 (bank15868 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15869 := params 28
abbrev ray15869 := rays 28
def bank15869 : Fin 1 → Cell := oneBank p15869 ray15869
theorem signs15869 : ∀ j, Signs p15869 (bank15869 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15870 := params 29
abbrev ray15870 := rays 29
def bank15870 : Fin 1 → Cell := oneBank p15870 ray15870
theorem signs15870 : ∀ j, Signs p15870 (bank15870 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15871 := params 30
abbrev ray15871 := rays 30
def bank15871 : Fin 1 → Cell := oneBank p15871 ray15871
theorem signs15871 : ∀ j, Signs p15871 (bank15871 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15872 := params 31
abbrev ray15872 := rays 31
def bank15872 : Fin 1 → Cell := oneBank p15872 ray15872
theorem signs15872 : ∀ j, Signs p15872 (bank15872 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15841_15872
