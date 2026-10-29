/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00737_00768
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99898271308554,99898123243725,99897975152855,99897827035947,99897678893003,99897530724027,99897382529020,99897234307986,99897086060927,99896937787845,99896789488743,99896641163624,99896492812491,99896344435346,99896196032192,99896047603031,99895899147866,99895750666700,99895602159535,99895453626373,99895305067217,99895156482071,99895007870936,99894859233815,99894710570711,99894561881626,99894413166563,99894264425525,99894115658514,99893966865533,99893818046584,99893669201670,99893520330794]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (736+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(9834759374806635498724/12650302918794697068555:Fraction),(509905977162335447065/655928669863441699851:Fraction),(13766259845904107883448/17709724086313275895977:Fraction),(68825291349082529511443/88546870431568129479885:Fraction),(509772468708243506338/655889780974591699851:Fraction),(7645919580176667936866/9838152270174625497765:Fraction),(4587151264972580195372/5902774695438225298659:Fraction),(22933754249038719746204/29513290143858376493295:Fraction),(22931752513075717341439/29512706810525626493295:Fraction),(1965407203955841725375/2529610583759389413711:Fraction),(694780268129402845003/894289095268488681615:Fraction),(68777241970859970968296/88532870431582129479885:Fraction),(68771237204092532834339/88531120431583879479885:Fraction),(29963064687189409900/38574889076943629403:Fraction),(68759230729937400598264/88527620431587379479885:Fraction),(22917742603350699537043/29508623477196376493295:Fraction),(22915741565818858124072/29508040143863626493295:Fraction),(371574176242165783120/478499299630230429621:Fraction),(4582348102142608042457/5901374695439625298659:Fraction),(22909740088953612329662/29506290143865376493295:Fraction),(68723218808978595312047/88517120431597879479885:Fraction),(6247019851927358313931/8046851857418148134535:Fraction),(7634579883731267379188/9834846714622375497765:Fraction),(13741043868690511637759/17702374086320625895977:Fraction),(68699219540827164574364/88510120431604879479885:Fraction),(7632580084274321863144/9834263381289625497765:Fraction),(68687222996433651036457/88506620431608379479885:Fraction),(4578748336133098081400/5900324695440675298659:Fraction),(1526116153225976164340/1966736009591375099553:Fraction),(68669229768773376683237/88501370431613629479885:Fraction),(22887744554288170441072/29499873477205126493295:Fraction),(4577149157643990672512/5899858028774475298659:Fraction)]
abbrev p737 := params 0
abbrev ray737 := rays 0
def bank737 : Fin 1 → Cell := oneBank p737 ray737
theorem signs737 : ∀ j, Signs p737 (bank737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p738 := params 1
abbrev ray738 := rays 1
def bank738 : Fin 1 → Cell := oneBank p738 ray738
theorem signs738 : ∀ j, Signs p738 (bank738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p739 := params 2
abbrev ray739 := rays 2
def bank739 : Fin 1 → Cell := oneBank p739 ray739
theorem signs739 : ∀ j, Signs p739 (bank739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p740 := params 3
abbrev ray740 := rays 3
def bank740 : Fin 1 → Cell := oneBank p740 ray740
theorem signs740 : ∀ j, Signs p740 (bank740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p741 := params 4
abbrev ray741 := rays 4
def bank741 : Fin 1 → Cell := oneBank p741 ray741
theorem signs741 : ∀ j, Signs p741 (bank741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p742 := params 5
abbrev ray742 := rays 5
def bank742 : Fin 1 → Cell := oneBank p742 ray742
theorem signs742 : ∀ j, Signs p742 (bank742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p743 := params 6
abbrev ray743 := rays 6
def bank743 : Fin 1 → Cell := oneBank p743 ray743
theorem signs743 : ∀ j, Signs p743 (bank743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p744 := params 7
abbrev ray744 := rays 7
def bank744 : Fin 1 → Cell := oneBank p744 ray744
theorem signs744 : ∀ j, Signs p744 (bank744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p745 := params 8
abbrev ray745 := rays 8
def bank745 : Fin 1 → Cell := oneBank p745 ray745
theorem signs745 : ∀ j, Signs p745 (bank745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p746 := params 9
abbrev ray746 := rays 9
def bank746 : Fin 1 → Cell := oneBank p746 ray746
theorem signs746 : ∀ j, Signs p746 (bank746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p747 := params 10
abbrev ray747 := rays 10
def bank747 : Fin 1 → Cell := oneBank p747 ray747
theorem signs747 : ∀ j, Signs p747 (bank747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p748 := params 11
abbrev ray748 := rays 11
def bank748 : Fin 1 → Cell := oneBank p748 ray748
theorem signs748 : ∀ j, Signs p748 (bank748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p749 := params 12
abbrev ray749 := rays 12
def bank749 : Fin 1 → Cell := oneBank p749 ray749
theorem signs749 : ∀ j, Signs p749 (bank749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p750 := params 13
abbrev ray750 := rays 13
def bank750 : Fin 1 → Cell := oneBank p750 ray750
theorem signs750 : ∀ j, Signs p750 (bank750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p751 := params 14
abbrev ray751 := rays 14
def bank751 : Fin 1 → Cell := oneBank p751 ray751
theorem signs751 : ∀ j, Signs p751 (bank751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p752 := params 15
abbrev ray752 := rays 15
def bank752 : Fin 1 → Cell := oneBank p752 ray752
theorem signs752 : ∀ j, Signs p752 (bank752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p753 := params 16
abbrev ray753 := rays 16
def bank753 : Fin 1 → Cell := oneBank p753 ray753
theorem signs753 : ∀ j, Signs p753 (bank753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p754 := params 17
abbrev ray754 := rays 17
def bank754 : Fin 1 → Cell := oneBank p754 ray754
theorem signs754 : ∀ j, Signs p754 (bank754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p755 := params 18
abbrev ray755 := rays 18
def bank755 : Fin 1 → Cell := oneBank p755 ray755
theorem signs755 : ∀ j, Signs p755 (bank755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p756 := params 19
abbrev ray756 := rays 19
def bank756 : Fin 1 → Cell := oneBank p756 ray756
theorem signs756 : ∀ j, Signs p756 (bank756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p757 := params 20
abbrev ray757 := rays 20
def bank757 : Fin 1 → Cell := oneBank p757 ray757
theorem signs757 : ∀ j, Signs p757 (bank757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p758 := params 21
abbrev ray758 := rays 21
def bank758 : Fin 1 → Cell := oneBank p758 ray758
theorem signs758 : ∀ j, Signs p758 (bank758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p759 := params 22
abbrev ray759 := rays 22
def bank759 : Fin 1 → Cell := oneBank p759 ray759
theorem signs759 : ∀ j, Signs p759 (bank759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p760 := params 23
abbrev ray760 := rays 23
def bank760 : Fin 1 → Cell := oneBank p760 ray760
theorem signs760 : ∀ j, Signs p760 (bank760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p761 := params 24
abbrev ray761 := rays 24
def bank761 : Fin 1 → Cell := oneBank p761 ray761
theorem signs761 : ∀ j, Signs p761 (bank761 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p762 := params 25
abbrev ray762 := rays 25
def bank762 : Fin 1 → Cell := oneBank p762 ray762
theorem signs762 : ∀ j, Signs p762 (bank762 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p763 := params 26
abbrev ray763 := rays 26
def bank763 : Fin 1 → Cell := oneBank p763 ray763
theorem signs763 : ∀ j, Signs p763 (bank763 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p764 := params 27
abbrev ray764 := rays 27
def bank764 : Fin 1 → Cell := oneBank p764 ray764
theorem signs764 : ∀ j, Signs p764 (bank764 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p765 := params 28
abbrev ray765 := rays 28
def bank765 : Fin 1 → Cell := oneBank p765 ray765
theorem signs765 : ∀ j, Signs p765 (bank765 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p766 := params 29
abbrev ray766 := rays 29
def bank766 : Fin 1 → Cell := oneBank p766 ray766
theorem signs766 : ∀ j, Signs p766 (bank766 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p767 := params 30
abbrev ray767 := rays 30
def bank767 : Fin 1 → Cell := oneBank p767 ray767
theorem signs767 : ∀ j, Signs p767 (bank767 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p768 := params 31
abbrev ray768 := rays 31
def bank768 : Fin 1 → Cell := oneBank p768 ray768
theorem signs768 : ∀ j, Signs p768 (bank768 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00737_00768
