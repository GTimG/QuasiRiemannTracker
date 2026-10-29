/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13825_13856
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95925019839065,95924581475727,95924143096141,95923704700308,95923266288228,95922827859901,95922389415327,95921950954507,95921512477440,95921073984127,95920635474568,95920196948764,95919758406714,95919319848419,95918881273879,95918442683094,95918004076064,95917565452790,95917126813271,95916688157508,95916249485501,95915810797251,95915372092757,95914933372020,95914494635040,95914055881817,95913617112351,95913178326643,95912739524692,95912300706499,95911861872064,95911423021387,95910984154469]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13824+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13825 := params 0
abbrev ray13825 := rays 0
def bank13825 : Fin 1 → Cell := oneBank p13825 ray13825
theorem signs13825 : ∀ j, Signs p13825 (bank13825 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13826 := params 1
abbrev ray13826 := rays 1
def bank13826 : Fin 1 → Cell := oneBank p13826 ray13826
theorem signs13826 : ∀ j, Signs p13826 (bank13826 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13827 := params 2
abbrev ray13827 := rays 2
def bank13827 : Fin 1 → Cell := oneBank p13827 ray13827
theorem signs13827 : ∀ j, Signs p13827 (bank13827 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13828 := params 3
abbrev ray13828 := rays 3
def bank13828 : Fin 1 → Cell := oneBank p13828 ray13828
theorem signs13828 : ∀ j, Signs p13828 (bank13828 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13829 := params 4
abbrev ray13829 := rays 4
def bank13829 : Fin 1 → Cell := oneBank p13829 ray13829
theorem signs13829 : ∀ j, Signs p13829 (bank13829 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13830 := params 5
abbrev ray13830 := rays 5
def bank13830 : Fin 1 → Cell := oneBank p13830 ray13830
theorem signs13830 : ∀ j, Signs p13830 (bank13830 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13831 := params 6
abbrev ray13831 := rays 6
def bank13831 : Fin 1 → Cell := oneBank p13831 ray13831
theorem signs13831 : ∀ j, Signs p13831 (bank13831 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13832 := params 7
abbrev ray13832 := rays 7
def bank13832 : Fin 1 → Cell := oneBank p13832 ray13832
theorem signs13832 : ∀ j, Signs p13832 (bank13832 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13833 := params 8
abbrev ray13833 := rays 8
def bank13833 : Fin 1 → Cell := oneBank p13833 ray13833
theorem signs13833 : ∀ j, Signs p13833 (bank13833 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13834 := params 9
abbrev ray13834 := rays 9
def bank13834 : Fin 1 → Cell := oneBank p13834 ray13834
theorem signs13834 : ∀ j, Signs p13834 (bank13834 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13835 := params 10
abbrev ray13835 := rays 10
def bank13835 : Fin 1 → Cell := oneBank p13835 ray13835
theorem signs13835 : ∀ j, Signs p13835 (bank13835 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13836 := params 11
abbrev ray13836 := rays 11
def bank13836 : Fin 1 → Cell := oneBank p13836 ray13836
theorem signs13836 : ∀ j, Signs p13836 (bank13836 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13837 := params 12
abbrev ray13837 := rays 12
def bank13837 : Fin 1 → Cell := oneBank p13837 ray13837
theorem signs13837 : ∀ j, Signs p13837 (bank13837 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13838 := params 13
abbrev ray13838 := rays 13
def bank13838 : Fin 1 → Cell := oneBank p13838 ray13838
theorem signs13838 : ∀ j, Signs p13838 (bank13838 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13839 := params 14
abbrev ray13839 := rays 14
def bank13839 : Fin 1 → Cell := oneBank p13839 ray13839
theorem signs13839 : ∀ j, Signs p13839 (bank13839 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13840 := params 15
abbrev ray13840 := rays 15
def bank13840 : Fin 1 → Cell := oneBank p13840 ray13840
theorem signs13840 : ∀ j, Signs p13840 (bank13840 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13841 := params 16
abbrev ray13841 := rays 16
def bank13841 : Fin 1 → Cell := oneBank p13841 ray13841
theorem signs13841 : ∀ j, Signs p13841 (bank13841 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13842 := params 17
abbrev ray13842 := rays 17
def bank13842 : Fin 1 → Cell := oneBank p13842 ray13842
theorem signs13842 : ∀ j, Signs p13842 (bank13842 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13843 := params 18
abbrev ray13843 := rays 18
def bank13843 : Fin 1 → Cell := oneBank p13843 ray13843
theorem signs13843 : ∀ j, Signs p13843 (bank13843 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13844 := params 19
abbrev ray13844 := rays 19
def bank13844 : Fin 1 → Cell := oneBank p13844 ray13844
theorem signs13844 : ∀ j, Signs p13844 (bank13844 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13845 := params 20
abbrev ray13845 := rays 20
def bank13845 : Fin 1 → Cell := oneBank p13845 ray13845
theorem signs13845 : ∀ j, Signs p13845 (bank13845 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13846 := params 21
abbrev ray13846 := rays 21
def bank13846 : Fin 1 → Cell := oneBank p13846 ray13846
theorem signs13846 : ∀ j, Signs p13846 (bank13846 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13847 := params 22
abbrev ray13847 := rays 22
def bank13847 : Fin 1 → Cell := oneBank p13847 ray13847
theorem signs13847 : ∀ j, Signs p13847 (bank13847 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13848 := params 23
abbrev ray13848 := rays 23
def bank13848 : Fin 1 → Cell := oneBank p13848 ray13848
theorem signs13848 : ∀ j, Signs p13848 (bank13848 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13849 := params 24
abbrev ray13849 := rays 24
def bank13849 : Fin 1 → Cell := oneBank p13849 ray13849
theorem signs13849 : ∀ j, Signs p13849 (bank13849 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13850 := params 25
abbrev ray13850 := rays 25
def bank13850 : Fin 1 → Cell := oneBank p13850 ray13850
theorem signs13850 : ∀ j, Signs p13850 (bank13850 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13851 := params 26
abbrev ray13851 := rays 26
def bank13851 : Fin 1 → Cell := oneBank p13851 ray13851
theorem signs13851 : ∀ j, Signs p13851 (bank13851 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13852 := params 27
abbrev ray13852 := rays 27
def bank13852 : Fin 1 → Cell := oneBank p13852 ray13852
theorem signs13852 : ∀ j, Signs p13852 (bank13852 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13853 := params 28
abbrev ray13853 := rays 28
def bank13853 : Fin 1 → Cell := oneBank p13853 ray13853
theorem signs13853 : ∀ j, Signs p13853 (bank13853 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13854 := params 29
abbrev ray13854 := rays 29
def bank13854 : Fin 1 → Cell := oneBank p13854 ray13854
theorem signs13854 : ∀ j, Signs p13854 (bank13854 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13855 := params 30
abbrev ray13855 := rays 30
def bank13855 : Fin 1 → Cell := oneBank p13855 ray13855
theorem signs13855 : ∀ j, Signs p13855 (bank13855 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13856 := params 31
abbrev ray13856 := rays 31
def bank13856 : Fin 1 → Cell := oneBank p13856 ray13856
theorem signs13856 : ∀ j, Signs p13856 (bank13856 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13825_13856
