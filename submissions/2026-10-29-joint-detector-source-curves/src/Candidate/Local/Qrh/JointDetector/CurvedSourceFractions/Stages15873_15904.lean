/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15873_15904
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94993423945658,94992952616660,94992481271664,94992009910671,94991538533681,94991067140694,94990595731709,94990124306727,94989652865748,94989181408772,94988709935799,94988238446829,94987766941862,94987295420898,94986823883937,94986352330979,94985880762025,94985409177074,94984937576126,94984465959182,94983994326241,94983522677304,94983051012370,94982579331440,94982107634513,94981635921590,94981164192671,94980692447755,94980220686843,94979748909935,94979277117031,94978805308131,94978333483235]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15872+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15873 := params 0
abbrev ray15873 := rays 0
def bank15873 : Fin 1 → Cell := oneBank p15873 ray15873
theorem signs15873 : ∀ j, Signs p15873 (bank15873 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15874 := params 1
abbrev ray15874 := rays 1
def bank15874 : Fin 1 → Cell := oneBank p15874 ray15874
theorem signs15874 : ∀ j, Signs p15874 (bank15874 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15875 := params 2
abbrev ray15875 := rays 2
def bank15875 : Fin 1 → Cell := oneBank p15875 ray15875
theorem signs15875 : ∀ j, Signs p15875 (bank15875 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15876 := params 3
abbrev ray15876 := rays 3
def bank15876 : Fin 1 → Cell := oneBank p15876 ray15876
theorem signs15876 : ∀ j, Signs p15876 (bank15876 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15877 := params 4
abbrev ray15877 := rays 4
def bank15877 : Fin 1 → Cell := oneBank p15877 ray15877
theorem signs15877 : ∀ j, Signs p15877 (bank15877 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15878 := params 5
abbrev ray15878 := rays 5
def bank15878 : Fin 1 → Cell := oneBank p15878 ray15878
theorem signs15878 : ∀ j, Signs p15878 (bank15878 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15879 := params 6
abbrev ray15879 := rays 6
def bank15879 : Fin 1 → Cell := oneBank p15879 ray15879
theorem signs15879 : ∀ j, Signs p15879 (bank15879 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15880 := params 7
abbrev ray15880 := rays 7
def bank15880 : Fin 1 → Cell := oneBank p15880 ray15880
theorem signs15880 : ∀ j, Signs p15880 (bank15880 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15881 := params 8
abbrev ray15881 := rays 8
def bank15881 : Fin 1 → Cell := oneBank p15881 ray15881
theorem signs15881 : ∀ j, Signs p15881 (bank15881 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15882 := params 9
abbrev ray15882 := rays 9
def bank15882 : Fin 1 → Cell := oneBank p15882 ray15882
theorem signs15882 : ∀ j, Signs p15882 (bank15882 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15883 := params 10
abbrev ray15883 := rays 10
def bank15883 : Fin 1 → Cell := oneBank p15883 ray15883
theorem signs15883 : ∀ j, Signs p15883 (bank15883 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15884 := params 11
abbrev ray15884 := rays 11
def bank15884 : Fin 1 → Cell := oneBank p15884 ray15884
theorem signs15884 : ∀ j, Signs p15884 (bank15884 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15885 := params 12
abbrev ray15885 := rays 12
def bank15885 : Fin 1 → Cell := oneBank p15885 ray15885
theorem signs15885 : ∀ j, Signs p15885 (bank15885 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15886 := params 13
abbrev ray15886 := rays 13
def bank15886 : Fin 1 → Cell := oneBank p15886 ray15886
theorem signs15886 : ∀ j, Signs p15886 (bank15886 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15887 := params 14
abbrev ray15887 := rays 14
def bank15887 : Fin 1 → Cell := oneBank p15887 ray15887
theorem signs15887 : ∀ j, Signs p15887 (bank15887 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15888 := params 15
abbrev ray15888 := rays 15
def bank15888 : Fin 1 → Cell := oneBank p15888 ray15888
theorem signs15888 : ∀ j, Signs p15888 (bank15888 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15889 := params 16
abbrev ray15889 := rays 16
def bank15889 : Fin 1 → Cell := oneBank p15889 ray15889
theorem signs15889 : ∀ j, Signs p15889 (bank15889 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15890 := params 17
abbrev ray15890 := rays 17
def bank15890 : Fin 1 → Cell := oneBank p15890 ray15890
theorem signs15890 : ∀ j, Signs p15890 (bank15890 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15891 := params 18
abbrev ray15891 := rays 18
def bank15891 : Fin 1 → Cell := oneBank p15891 ray15891
theorem signs15891 : ∀ j, Signs p15891 (bank15891 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15892 := params 19
abbrev ray15892 := rays 19
def bank15892 : Fin 1 → Cell := oneBank p15892 ray15892
theorem signs15892 : ∀ j, Signs p15892 (bank15892 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15893 := params 20
abbrev ray15893 := rays 20
def bank15893 : Fin 1 → Cell := oneBank p15893 ray15893
theorem signs15893 : ∀ j, Signs p15893 (bank15893 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15894 := params 21
abbrev ray15894 := rays 21
def bank15894 : Fin 1 → Cell := oneBank p15894 ray15894
theorem signs15894 : ∀ j, Signs p15894 (bank15894 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15895 := params 22
abbrev ray15895 := rays 22
def bank15895 : Fin 1 → Cell := oneBank p15895 ray15895
theorem signs15895 : ∀ j, Signs p15895 (bank15895 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15896 := params 23
abbrev ray15896 := rays 23
def bank15896 : Fin 1 → Cell := oneBank p15896 ray15896
theorem signs15896 : ∀ j, Signs p15896 (bank15896 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15897 := params 24
abbrev ray15897 := rays 24
def bank15897 : Fin 1 → Cell := oneBank p15897 ray15897
theorem signs15897 : ∀ j, Signs p15897 (bank15897 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15898 := params 25
abbrev ray15898 := rays 25
def bank15898 : Fin 1 → Cell := oneBank p15898 ray15898
theorem signs15898 : ∀ j, Signs p15898 (bank15898 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15899 := params 26
abbrev ray15899 := rays 26
def bank15899 : Fin 1 → Cell := oneBank p15899 ray15899
theorem signs15899 : ∀ j, Signs p15899 (bank15899 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15900 := params 27
abbrev ray15900 := rays 27
def bank15900 : Fin 1 → Cell := oneBank p15900 ray15900
theorem signs15900 : ∀ j, Signs p15900 (bank15900 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15901 := params 28
abbrev ray15901 := rays 28
def bank15901 : Fin 1 → Cell := oneBank p15901 ray15901
theorem signs15901 : ∀ j, Signs p15901 (bank15901 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15902 := params 29
abbrev ray15902 := rays 29
def bank15902 : Fin 1 → Cell := oneBank p15902 ray15902
theorem signs15902 : ∀ j, Signs p15902 (bank15902 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15903 := params 30
abbrev ray15903 := rays 30
def bank15903 : Fin 1 → Cell := oneBank p15903 ray15903
theorem signs15903 : ∀ j, Signs p15903 (bank15903 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15904 := params 31
abbrev ray15904 := rays 31
def bank15904 : Fin 1 → Cell := oneBank p15904 ray15904
theorem signs15904 : ∀ j, Signs p15904 (bank15904 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15873_15904
