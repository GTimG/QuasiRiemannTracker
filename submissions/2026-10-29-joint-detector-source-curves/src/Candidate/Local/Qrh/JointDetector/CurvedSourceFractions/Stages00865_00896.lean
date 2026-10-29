/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00865_00896
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99879108237826,99878956860824,99878805458110,99878654029687,99878502575558,99878351095725,99878199590191,99878048058958,99877896502029,99877744919406,99877593311092,99877441677089,99877290017399,99877138332026,99876986620972,99876834884240,99876683121831,99876531333749,99876379519995,99876227680573,99876075815485,99875923924733,99875772008320,99875620066249,99875468098521,99875316105140,99875164086108,99875012041427,99874859971101,99874707875131,99874555753520,99874403606271,99874251433386]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (864+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(9725372085299399982412/12618302918826697068555:Fraction),(748040112744710176316/970619455294380543735:Fraction),(648244721264577153208/841186861255146471237:Fraction),(883892740469406112184/1147050265347949733505:Fraction),(800632792048935621376/1039072005079927993881:Fraction),(4536522310458713027485/5887958028786375298659:Fraction),(22680627266682427513978/29439206810599126493295:Fraction),(9719418393381521395144/12616552918828447068555:Fraction),(7558886303567550501419/9812680047977875497765:Fraction),(3239239320733976448448/4205350972942982356185:Fraction),(68018074549269528839354/88310620431804379479885:Fraction),(2518967569928701765939/3270698904881708499255:Fraction),(9715167719640310595069/12615302918829697068555:Fraction),(68000223497504909447132/88305370431809629479885:Fraction),(581147640876795001088/754731798562490422905:Fraction),(13597665098555590852900/17660374086362625895977:Fraction),(22660792271225897956364/29433373477271626493295:Fraction),(122480052540128611343/159096162940210143207:Fraction),(13594096263324869271122/17659324086363675895977:Fraction),(359600705207673456587/467168626623386928465:Fraction),(1510190806159486962095/1962069342929375099553:Fraction),(13590528059091700511906/17658274086364725895977:Fraction),(13589338824921096196670/17657924086365075895977:Fraction),(7548972108798852148831/9809763381314125497765:Fraction),(7548311516076724754353/9809568936869875497765:Fraction),(215647172494316348204/280267842640732157079:Fraction),(838554504169124160198/1089908894220152833085:Fraction),(7546330016741118541444/9808985603537125497765:Fraction),(67911026489267203097756/88279120431835879479885:Fraction),(1509001863412078427473/1961719342929725099553:Fraction),(13579828205778997468636/17655124086367875895977:Fraction),(67893199230007836273544/88273870431841129479885:Fraction)]
abbrev p865 := params 0
abbrev ray865 := rays 0
def bank865 : Fin 1 → Cell := oneBank p865 ray865
theorem signs865 : ∀ j, Signs p865 (bank865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p866 := params 1
abbrev ray866 := rays 1
def bank866 : Fin 1 → Cell := oneBank p866 ray866
theorem signs866 : ∀ j, Signs p866 (bank866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p867 := params 2
abbrev ray867 := rays 2
def bank867 : Fin 1 → Cell := oneBank p867 ray867
theorem signs867 : ∀ j, Signs p867 (bank867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p868 := params 3
abbrev ray868 := rays 3
def bank868 : Fin 1 → Cell := oneBank p868 ray868
theorem signs868 : ∀ j, Signs p868 (bank868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p869 := params 4
abbrev ray869 := rays 4
def bank869 : Fin 1 → Cell := oneBank p869 ray869
theorem signs869 : ∀ j, Signs p869 (bank869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p870 := params 5
abbrev ray870 := rays 5
def bank870 : Fin 1 → Cell := oneBank p870 ray870
theorem signs870 : ∀ j, Signs p870 (bank870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p871 := params 6
abbrev ray871 := rays 6
def bank871 : Fin 1 → Cell := oneBank p871 ray871
theorem signs871 : ∀ j, Signs p871 (bank871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p872 := params 7
abbrev ray872 := rays 7
def bank872 : Fin 1 → Cell := oneBank p872 ray872
theorem signs872 : ∀ j, Signs p872 (bank872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p873 := params 8
abbrev ray873 := rays 8
def bank873 : Fin 1 → Cell := oneBank p873 ray873
theorem signs873 : ∀ j, Signs p873 (bank873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p874 := params 9
abbrev ray874 := rays 9
def bank874 : Fin 1 → Cell := oneBank p874 ray874
theorem signs874 : ∀ j, Signs p874 (bank874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p875 := params 10
abbrev ray875 := rays 10
def bank875 : Fin 1 → Cell := oneBank p875 ray875
theorem signs875 : ∀ j, Signs p875 (bank875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p876 := params 11
abbrev ray876 := rays 11
def bank876 : Fin 1 → Cell := oneBank p876 ray876
theorem signs876 : ∀ j, Signs p876 (bank876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p877 := params 12
abbrev ray877 := rays 12
def bank877 : Fin 1 → Cell := oneBank p877 ray877
theorem signs877 : ∀ j, Signs p877 (bank877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p878 := params 13
abbrev ray878 := rays 13
def bank878 : Fin 1 → Cell := oneBank p878 ray878
theorem signs878 : ∀ j, Signs p878 (bank878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p879 := params 14
abbrev ray879 := rays 14
def bank879 : Fin 1 → Cell := oneBank p879 ray879
theorem signs879 : ∀ j, Signs p879 (bank879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p880 := params 15
abbrev ray880 := rays 15
def bank880 : Fin 1 → Cell := oneBank p880 ray880
theorem signs880 : ∀ j, Signs p880 (bank880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p881 := params 16
abbrev ray881 := rays 16
def bank881 : Fin 1 → Cell := oneBank p881 ray881
theorem signs881 : ∀ j, Signs p881 (bank881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p882 := params 17
abbrev ray882 := rays 17
def bank882 : Fin 1 → Cell := oneBank p882 ray882
theorem signs882 : ∀ j, Signs p882 (bank882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p883 := params 18
abbrev ray883 := rays 18
def bank883 : Fin 1 → Cell := oneBank p883 ray883
theorem signs883 : ∀ j, Signs p883 (bank883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p884 := params 19
abbrev ray884 := rays 19
def bank884 : Fin 1 → Cell := oneBank p884 ray884
theorem signs884 : ∀ j, Signs p884 (bank884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p885 := params 20
abbrev ray885 := rays 20
def bank885 : Fin 1 → Cell := oneBank p885 ray885
theorem signs885 : ∀ j, Signs p885 (bank885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p886 := params 21
abbrev ray886 := rays 21
def bank886 : Fin 1 → Cell := oneBank p886 ray886
theorem signs886 : ∀ j, Signs p886 (bank886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p887 := params 22
abbrev ray887 := rays 22
def bank887 : Fin 1 → Cell := oneBank p887 ray887
theorem signs887 : ∀ j, Signs p887 (bank887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p888 := params 23
abbrev ray888 := rays 23
def bank888 : Fin 1 → Cell := oneBank p888 ray888
theorem signs888 : ∀ j, Signs p888 (bank888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p889 := params 24
abbrev ray889 := rays 24
def bank889 : Fin 1 → Cell := oneBank p889 ray889
theorem signs889 : ∀ j, Signs p889 (bank889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p890 := params 25
abbrev ray890 := rays 25
def bank890 : Fin 1 → Cell := oneBank p890 ray890
theorem signs890 : ∀ j, Signs p890 (bank890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p891 := params 26
abbrev ray891 := rays 26
def bank891 : Fin 1 → Cell := oneBank p891 ray891
theorem signs891 : ∀ j, Signs p891 (bank891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p892 := params 27
abbrev ray892 := rays 27
def bank892 : Fin 1 → Cell := oneBank p892 ray892
theorem signs892 : ∀ j, Signs p892 (bank892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p893 := params 28
abbrev ray893 := rays 28
def bank893 : Fin 1 → Cell := oneBank p893 ray893
theorem signs893 : ∀ j, Signs p893 (bank893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p894 := params 29
abbrev ray894 := rays 29
def bank894 : Fin 1 → Cell := oneBank p894 ray894
theorem signs894 : ∀ j, Signs p894 (bank894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p895 := params 30
abbrev ray895 := rays 30
def bank895 : Fin 1 → Cell := oneBank p895 ray895
theorem signs895 : ∀ j, Signs p895 (bank895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p896 := params 31
abbrev ray896 := rays 31
def bank896 : Fin 1 → Cell := oneBank p896 ray896
theorem signs896 : ∀ j, Signs p896 (bank896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00865_00896
