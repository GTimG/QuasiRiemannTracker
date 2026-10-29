/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages06849_06880
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98521148326401,98520848917072,98520549485294,98520250031068,98519950554395,98519651055275,98519351533710,98519051989700,98518752423246,98518452834349,98518153223010,98517853589229,98517553933008,98517254254347,98516954553246,98516654829707,98516355083731,98516055315318,98515755524469,98515455711185,98515155875466,98514856017314,98514556136729,98514256233712,98513956308264,98513656360386,98513356390078,98513056397341,98512756382177,98512456344585,98512156284567,98511856202123,98511556097255]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (6848+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p6849 := params 0
abbrev ray6849 := rays 0
def bank6849 : Fin 2 → Cell := twoBank p6849 ray6849
theorem signs6849 : ∀ j, Signs p6849 (bank6849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6850 := params 1
abbrev ray6850 := rays 1
def bank6850 : Fin 2 → Cell := twoBank p6850 ray6850
theorem signs6850 : ∀ j, Signs p6850 (bank6850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6851 := params 2
abbrev ray6851 := rays 2
def bank6851 : Fin 2 → Cell := twoBank p6851 ray6851
theorem signs6851 : ∀ j, Signs p6851 (bank6851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6852 := params 3
abbrev ray6852 := rays 3
def bank6852 : Fin 2 → Cell := twoBank p6852 ray6852
theorem signs6852 : ∀ j, Signs p6852 (bank6852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6853 := params 4
abbrev ray6853 := rays 4
def bank6853 : Fin 2 → Cell := twoBank p6853 ray6853
theorem signs6853 : ∀ j, Signs p6853 (bank6853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6854 := params 5
abbrev ray6854 := rays 5
def bank6854 : Fin 2 → Cell := twoBank p6854 ray6854
theorem signs6854 : ∀ j, Signs p6854 (bank6854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6855 := params 6
abbrev ray6855 := rays 6
def bank6855 : Fin 2 → Cell := twoBank p6855 ray6855
theorem signs6855 : ∀ j, Signs p6855 (bank6855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6856 := params 7
abbrev ray6856 := rays 7
def bank6856 : Fin 2 → Cell := twoBank p6856 ray6856
theorem signs6856 : ∀ j, Signs p6856 (bank6856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6857 := params 8
abbrev ray6857 := rays 8
def bank6857 : Fin 2 → Cell := twoBank p6857 ray6857
theorem signs6857 : ∀ j, Signs p6857 (bank6857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6858 := params 9
abbrev ray6858 := rays 9
def bank6858 : Fin 2 → Cell := twoBank p6858 ray6858
theorem signs6858 : ∀ j, Signs p6858 (bank6858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6859 := params 10
abbrev ray6859 := rays 10
def bank6859 : Fin 2 → Cell := twoBank p6859 ray6859
theorem signs6859 : ∀ j, Signs p6859 (bank6859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6860 := params 11
abbrev ray6860 := rays 11
def bank6860 : Fin 2 → Cell := twoBank p6860 ray6860
theorem signs6860 : ∀ j, Signs p6860 (bank6860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6861 := params 12
abbrev ray6861 := rays 12
def bank6861 : Fin 2 → Cell := twoBank p6861 ray6861
theorem signs6861 : ∀ j, Signs p6861 (bank6861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6862 := params 13
abbrev ray6862 := rays 13
def bank6862 : Fin 2 → Cell := twoBank p6862 ray6862
theorem signs6862 : ∀ j, Signs p6862 (bank6862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6863 := params 14
abbrev ray6863 := rays 14
def bank6863 : Fin 2 → Cell := twoBank p6863 ray6863
theorem signs6863 : ∀ j, Signs p6863 (bank6863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6864 := params 15
abbrev ray6864 := rays 15
def bank6864 : Fin 2 → Cell := twoBank p6864 ray6864
theorem signs6864 : ∀ j, Signs p6864 (bank6864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6865 := params 16
abbrev ray6865 := rays 16
def bank6865 : Fin 2 → Cell := twoBank p6865 ray6865
theorem signs6865 : ∀ j, Signs p6865 (bank6865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6866 := params 17
abbrev ray6866 := rays 17
def bank6866 : Fin 2 → Cell := twoBank p6866 ray6866
theorem signs6866 : ∀ j, Signs p6866 (bank6866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6867 := params 18
abbrev ray6867 := rays 18
def bank6867 : Fin 2 → Cell := twoBank p6867 ray6867
theorem signs6867 : ∀ j, Signs p6867 (bank6867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6868 := params 19
abbrev ray6868 := rays 19
def bank6868 : Fin 2 → Cell := twoBank p6868 ray6868
theorem signs6868 : ∀ j, Signs p6868 (bank6868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6869 := params 20
abbrev ray6869 := rays 20
def bank6869 : Fin 2 → Cell := twoBank p6869 ray6869
theorem signs6869 : ∀ j, Signs p6869 (bank6869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6870 := params 21
abbrev ray6870 := rays 21
def bank6870 : Fin 2 → Cell := twoBank p6870 ray6870
theorem signs6870 : ∀ j, Signs p6870 (bank6870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6871 := params 22
abbrev ray6871 := rays 22
def bank6871 : Fin 2 → Cell := twoBank p6871 ray6871
theorem signs6871 : ∀ j, Signs p6871 (bank6871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6872 := params 23
abbrev ray6872 := rays 23
def bank6872 : Fin 2 → Cell := twoBank p6872 ray6872
theorem signs6872 : ∀ j, Signs p6872 (bank6872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6873 := params 24
abbrev ray6873 := rays 24
def bank6873 : Fin 2 → Cell := twoBank p6873 ray6873
theorem signs6873 : ∀ j, Signs p6873 (bank6873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6874 := params 25
abbrev ray6874 := rays 25
def bank6874 : Fin 2 → Cell := twoBank p6874 ray6874
theorem signs6874 : ∀ j, Signs p6874 (bank6874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6875 := params 26
abbrev ray6875 := rays 26
def bank6875 : Fin 2 → Cell := twoBank p6875 ray6875
theorem signs6875 : ∀ j, Signs p6875 (bank6875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6876 := params 27
abbrev ray6876 := rays 27
def bank6876 : Fin 2 → Cell := twoBank p6876 ray6876
theorem signs6876 : ∀ j, Signs p6876 (bank6876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6877 := params 28
abbrev ray6877 := rays 28
def bank6877 : Fin 2 → Cell := twoBank p6877 ray6877
theorem signs6877 : ∀ j, Signs p6877 (bank6877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6878 := params 29
abbrev ray6878 := rays 29
def bank6878 : Fin 2 → Cell := twoBank p6878 ray6878
theorem signs6878 : ∀ j, Signs p6878 (bank6878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6879 := params 30
abbrev ray6879 := rays 30
def bank6879 : Fin 2 → Cell := twoBank p6879 ray6879
theorem signs6879 : ∀ j, Signs p6879 (bank6879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p6880 := params 31
abbrev ray6880 := rays 31
def bank6880 : Fin 2 → Cell := twoBank p6880 ray6880
theorem signs6880 : ∀ j, Signs p6880 (bank6880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages06849_06880
