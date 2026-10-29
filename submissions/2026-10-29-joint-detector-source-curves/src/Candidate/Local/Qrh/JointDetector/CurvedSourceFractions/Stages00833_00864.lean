/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00833_00864
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99883938711116,99883788158217,99883637579526,99883486975044,99883336344775,99883185688721,99883035006884,99882884299268,99882733565874,99882582806705,99882432021764,99882281211054,99882130374576,99881979512334,99881828624330,99881677710566,99881526771045,99881375805770,99881224814742,99881073797965,99880922755441,99880771687173,99880620593163,99880469473414,99880318327928,99880167156708,99880015959757,99879864737077,99879713488670,99879562214539,99879410914686,99879259589114,99879108237826]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (832+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(68268385462732696636526/88384120431730879479885:Fraction),(1197586255623788661709/1550567902311098762805:Fraction),(68256448701647659679488/88380620431734379479885:Fraction),(22750160214082185375026/29459623477245376493295:Fraction),(1516544746804339821725/1963936009594175099553:Fraction),(3249454589509767121027/4208350972939982356185:Fraction),(9747511453806423442316/12624802918820197068555:Fraction),(168460777770547274328/218202149214180566617:Fraction),(68220649627152200605208/88370120431744879479885:Fraction),(13642936813379845322944/17673674086349325895977:Fraction),(22736239843413396331006/29455540143916126493295:Fraction),(1948650137237185218128/2524710583764289413711:Fraction),(68196791100036873903724/88363120431751879479885:Fraction),(120266011323638678248/155840159491628976155:Fraction),(4545657703385497357088/5890641362117025298659:Fraction),(1842673040294223521632/2388050552209652148105:Fraction),(4544862696988533516535/5890408028783925298659:Fraction),(4544465296177548722696/5890291362117375298659:Fraction),(68161018240415649093968/88352620431762379479885:Fraction),(1514556818846644778372/1963352676261425099553:Fraction),(68149096479782899348744/88349120431765879479885:Fraction),(22714378640483453440852/29449123477255876493295:Fraction),(2523599125451837755739/3272060015991458499255:Fraction),(68131217877086227765504/88343870431771129479885:Fraction),(68125259177049073910098/88342120431772879479885:Fraction),(2522937047670397179734/3271865571547208499255:Fraction),(68113342421397872157854/88338620431776379479885:Fraction),(68107385579994877022638/88336870431778129479885:Fraction),(648585033797841089584/841286861255046471237:Fraction),(68095471327745742169082/88333370431781629479885:Fraction),(986804567117753089064/1280168412054831586665:Fraction),(4538903997264433281932/5888658028785675298659:Fraction)]
abbrev p833 := params 0
abbrev ray833 := rays 0
def bank833 : Fin 1 → Cell := oneBank p833 ray833
theorem signs833 : ∀ j, Signs p833 (bank833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p834 := params 1
abbrev ray834 := rays 1
def bank834 : Fin 1 → Cell := oneBank p834 ray834
theorem signs834 : ∀ j, Signs p834 (bank834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p835 := params 2
abbrev ray835 := rays 2
def bank835 : Fin 1 → Cell := oneBank p835 ray835
theorem signs835 : ∀ j, Signs p835 (bank835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p836 := params 3
abbrev ray836 := rays 3
def bank836 : Fin 1 → Cell := oneBank p836 ray836
theorem signs836 : ∀ j, Signs p836 (bank836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p837 := params 4
abbrev ray837 := rays 4
def bank837 : Fin 1 → Cell := oneBank p837 ray837
theorem signs837 : ∀ j, Signs p837 (bank837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p838 := params 5
abbrev ray838 := rays 5
def bank838 : Fin 1 → Cell := oneBank p838 ray838
theorem signs838 : ∀ j, Signs p838 (bank838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p839 := params 6
abbrev ray839 := rays 6
def bank839 : Fin 1 → Cell := oneBank p839 ray839
theorem signs839 : ∀ j, Signs p839 (bank839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p840 := params 7
abbrev ray840 := rays 7
def bank840 : Fin 1 → Cell := oneBank p840 ray840
theorem signs840 : ∀ j, Signs p840 (bank840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p841 := params 8
abbrev ray841 := rays 8
def bank841 : Fin 1 → Cell := oneBank p841 ray841
theorem signs841 : ∀ j, Signs p841 (bank841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p842 := params 9
abbrev ray842 := rays 9
def bank842 : Fin 1 → Cell := oneBank p842 ray842
theorem signs842 : ∀ j, Signs p842 (bank842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p843 := params 10
abbrev ray843 := rays 10
def bank843 : Fin 1 → Cell := oneBank p843 ray843
theorem signs843 : ∀ j, Signs p843 (bank843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p844 := params 11
abbrev ray844 := rays 11
def bank844 : Fin 1 → Cell := oneBank p844 ray844
theorem signs844 : ∀ j, Signs p844 (bank844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p845 := params 12
abbrev ray845 := rays 12
def bank845 : Fin 1 → Cell := oneBank p845 ray845
theorem signs845 : ∀ j, Signs p845 (bank845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p846 := params 13
abbrev ray846 := rays 13
def bank846 : Fin 1 → Cell := oneBank p846 ray846
theorem signs846 : ∀ j, Signs p846 (bank846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p847 := params 14
abbrev ray847 := rays 14
def bank847 : Fin 1 → Cell := oneBank p847 ray847
theorem signs847 : ∀ j, Signs p847 (bank847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p848 := params 15
abbrev ray848 := rays 15
def bank848 : Fin 1 → Cell := oneBank p848 ray848
theorem signs848 : ∀ j, Signs p848 (bank848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p849 := params 16
abbrev ray849 := rays 16
def bank849 : Fin 1 → Cell := oneBank p849 ray849
theorem signs849 : ∀ j, Signs p849 (bank849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p850 := params 17
abbrev ray850 := rays 17
def bank850 : Fin 1 → Cell := oneBank p850 ray850
theorem signs850 : ∀ j, Signs p850 (bank850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p851 := params 18
abbrev ray851 := rays 18
def bank851 : Fin 1 → Cell := oneBank p851 ray851
theorem signs851 : ∀ j, Signs p851 (bank851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p852 := params 19
abbrev ray852 := rays 19
def bank852 : Fin 1 → Cell := oneBank p852 ray852
theorem signs852 : ∀ j, Signs p852 (bank852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p853 := params 20
abbrev ray853 := rays 20
def bank853 : Fin 1 → Cell := oneBank p853 ray853
theorem signs853 : ∀ j, Signs p853 (bank853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p854 := params 21
abbrev ray854 := rays 21
def bank854 : Fin 1 → Cell := oneBank p854 ray854
theorem signs854 : ∀ j, Signs p854 (bank854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p855 := params 22
abbrev ray855 := rays 22
def bank855 : Fin 1 → Cell := oneBank p855 ray855
theorem signs855 : ∀ j, Signs p855 (bank855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p856 := params 23
abbrev ray856 := rays 23
def bank856 : Fin 1 → Cell := oneBank p856 ray856
theorem signs856 : ∀ j, Signs p856 (bank856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p857 := params 24
abbrev ray857 := rays 24
def bank857 : Fin 1 → Cell := oneBank p857 ray857
theorem signs857 : ∀ j, Signs p857 (bank857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p858 := params 25
abbrev ray858 := rays 25
def bank858 : Fin 1 → Cell := oneBank p858 ray858
theorem signs858 : ∀ j, Signs p858 (bank858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p859 := params 26
abbrev ray859 := rays 26
def bank859 : Fin 1 → Cell := oneBank p859 ray859
theorem signs859 : ∀ j, Signs p859 (bank859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p860 := params 27
abbrev ray860 := rays 27
def bank860 : Fin 1 → Cell := oneBank p860 ray860
theorem signs860 : ∀ j, Signs p860 (bank860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p861 := params 28
abbrev ray861 := rays 28
def bank861 : Fin 1 → Cell := oneBank p861 ray861
theorem signs861 : ∀ j, Signs p861 (bank861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p862 := params 29
abbrev ray862 := rays 29
def bank862 : Fin 1 → Cell := oneBank p862 ray862
theorem signs862 : ∀ j, Signs p862 (bank862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p863 := params 30
abbrev ray863 := rays 30
def bank863 : Fin 1 → Cell := oneBank p863 ray863
theorem signs863 : ∀ j, Signs p863 (bank863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p864 := params 31
abbrev ray864 := rays 31
def bank864 : Fin 1 → Cell := oneBank p864 ray864
theorem signs864 : ∀ j, Signs p864 (bank864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00833_00864
