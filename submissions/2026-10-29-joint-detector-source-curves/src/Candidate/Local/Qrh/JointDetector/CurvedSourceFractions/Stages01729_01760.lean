/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01729_01760
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99738987939283,99738815218292,99738642473530,99738469705000,99738296912704,99738124096643,99737951256820,99737778393237,99737605505896,99737432594799,99737259659947,99737086701344,99736913718990,99736740712888,99736567683039,99736394629446,99736221552111,99736048451036,99735875326223,99735702177673,99735529005389,99735355809372,99735182589625,99735009346150,99734836078948,99734662788022,99734489473374,99734316135005,99734142772918,99733969387114,99733795977596,99733622544365,99733449087424]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1728+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(63092079750086084034004/86816120433298879479885:Fraction),(9012356537171928844018/12402052919042947068555:Fraction),(4205394188573758269988/5787508028886825298659:Fraction),(4205021981926539167750/5787391362220275298659:Fraction),(2335916581020426653864/3215152608640958499255:Fraction),(7007129497571127660503/9645263381478625497765:Fraction),(4203905540044993303988/5787041362220625298659:Fraction),(63053001781670255853938/86803870433311129479885:Fraction),(2335089685969543272554/3214893349381958499255:Fraction),(1341315767930132009824/1846816392198183605955:Fraction),(63036260496294622619837/86798620433316379479885:Fraction),(7003408995387225982406/9644096714813125497765:Fraction),(12605020495867343564176/17359024086663975895977:Fraction),(7002169314701593144186/9643707825924625497765:Fraction),(21004648339142215906832/28930540144441126493295:Fraction),(21002789087100045855232/28929956811108376493295:Fraction),(9000398476765255160224/12398302919046697068555:Fraction),(20999070824083244285002/28928790144442876493295:Fraction),(4199442444402026482505/5785641362222025298659:Fraction),(20995353155135678512828/28927623477777376493295:Fraction),(6997831616711518830493/9642346714814875497765:Fraction),(99801758268961468996/137526736027473263835:Fraction),(4197955614490065641245/5785174695555825298659:Fraction),(155466074138392274400/214261408477380566617:Fraction),(4197212377807887807730/5784941362222725298659:Fraction),(62952612367324428211424/86772370433342629479885:Fraction),(777123937036426238536/1071242227572152833085:Fraction),(1798327614051065021741/2479110583809889413711:Fraction),(1398575420357585612944/1928158231852175099553:Fraction),(2330752681469671792408/3213532238272208499255:Fraction),(62924751942609092862604/86763620433351379479885:Fraction),(12583836018250156182319/17352374086670625895977:Fraction)]
abbrev p1729 := params 0
abbrev ray1729 := rays 0
def bank1729 : Fin 1 → Cell := oneBank p1729 ray1729
theorem signs1729 : ∀ j, Signs p1729 (bank1729 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1730 := params 1
abbrev ray1730 := rays 1
def bank1730 : Fin 1 → Cell := oneBank p1730 ray1730
theorem signs1730 : ∀ j, Signs p1730 (bank1730 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1731 := params 2
abbrev ray1731 := rays 2
def bank1731 : Fin 1 → Cell := oneBank p1731 ray1731
theorem signs1731 : ∀ j, Signs p1731 (bank1731 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1732 := params 3
abbrev ray1732 := rays 3
def bank1732 : Fin 1 → Cell := oneBank p1732 ray1732
theorem signs1732 : ∀ j, Signs p1732 (bank1732 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1733 := params 4
abbrev ray1733 := rays 4
def bank1733 : Fin 1 → Cell := oneBank p1733 ray1733
theorem signs1733 : ∀ j, Signs p1733 (bank1733 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1734 := params 5
abbrev ray1734 := rays 5
def bank1734 : Fin 1 → Cell := oneBank p1734 ray1734
theorem signs1734 : ∀ j, Signs p1734 (bank1734 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1735 := params 6
abbrev ray1735 := rays 6
def bank1735 : Fin 1 → Cell := oneBank p1735 ray1735
theorem signs1735 : ∀ j, Signs p1735 (bank1735 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1736 := params 7
abbrev ray1736 := rays 7
def bank1736 : Fin 1 → Cell := oneBank p1736 ray1736
theorem signs1736 : ∀ j, Signs p1736 (bank1736 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1737 := params 8
abbrev ray1737 := rays 8
def bank1737 : Fin 1 → Cell := oneBank p1737 ray1737
theorem signs1737 : ∀ j, Signs p1737 (bank1737 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1738 := params 9
abbrev ray1738 := rays 9
def bank1738 : Fin 1 → Cell := oneBank p1738 ray1738
theorem signs1738 : ∀ j, Signs p1738 (bank1738 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1739 := params 10
abbrev ray1739 := rays 10
def bank1739 : Fin 1 → Cell := oneBank p1739 ray1739
theorem signs1739 : ∀ j, Signs p1739 (bank1739 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1740 := params 11
abbrev ray1740 := rays 11
def bank1740 : Fin 1 → Cell := oneBank p1740 ray1740
theorem signs1740 : ∀ j, Signs p1740 (bank1740 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1741 := params 12
abbrev ray1741 := rays 12
def bank1741 : Fin 1 → Cell := oneBank p1741 ray1741
theorem signs1741 : ∀ j, Signs p1741 (bank1741 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1742 := params 13
abbrev ray1742 := rays 13
def bank1742 : Fin 1 → Cell := oneBank p1742 ray1742
theorem signs1742 : ∀ j, Signs p1742 (bank1742 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1743 := params 14
abbrev ray1743 := rays 14
def bank1743 : Fin 1 → Cell := oneBank p1743 ray1743
theorem signs1743 : ∀ j, Signs p1743 (bank1743 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1744 := params 15
abbrev ray1744 := rays 15
def bank1744 : Fin 1 → Cell := oneBank p1744 ray1744
theorem signs1744 : ∀ j, Signs p1744 (bank1744 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1745 := params 16
abbrev ray1745 := rays 16
def bank1745 : Fin 1 → Cell := oneBank p1745 ray1745
theorem signs1745 : ∀ j, Signs p1745 (bank1745 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1746 := params 17
abbrev ray1746 := rays 17
def bank1746 : Fin 1 → Cell := oneBank p1746 ray1746
theorem signs1746 : ∀ j, Signs p1746 (bank1746 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1747 := params 18
abbrev ray1747 := rays 18
def bank1747 : Fin 1 → Cell := oneBank p1747 ray1747
theorem signs1747 : ∀ j, Signs p1747 (bank1747 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1748 := params 19
abbrev ray1748 := rays 19
def bank1748 : Fin 1 → Cell := oneBank p1748 ray1748
theorem signs1748 : ∀ j, Signs p1748 (bank1748 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1749 := params 20
abbrev ray1749 := rays 20
def bank1749 : Fin 1 → Cell := oneBank p1749 ray1749
theorem signs1749 : ∀ j, Signs p1749 (bank1749 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1750 := params 21
abbrev ray1750 := rays 21
def bank1750 : Fin 1 → Cell := oneBank p1750 ray1750
theorem signs1750 : ∀ j, Signs p1750 (bank1750 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1751 := params 22
abbrev ray1751 := rays 22
def bank1751 : Fin 1 → Cell := oneBank p1751 ray1751
theorem signs1751 : ∀ j, Signs p1751 (bank1751 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1752 := params 23
abbrev ray1752 := rays 23
def bank1752 : Fin 1 → Cell := oneBank p1752 ray1752
theorem signs1752 : ∀ j, Signs p1752 (bank1752 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1753 := params 24
abbrev ray1753 := rays 24
def bank1753 : Fin 1 → Cell := oneBank p1753 ray1753
theorem signs1753 : ∀ j, Signs p1753 (bank1753 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1754 := params 25
abbrev ray1754 := rays 25
def bank1754 : Fin 1 → Cell := oneBank p1754 ray1754
theorem signs1754 : ∀ j, Signs p1754 (bank1754 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1755 := params 26
abbrev ray1755 := rays 26
def bank1755 : Fin 1 → Cell := oneBank p1755 ray1755
theorem signs1755 : ∀ j, Signs p1755 (bank1755 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1756 := params 27
abbrev ray1756 := rays 27
def bank1756 : Fin 1 → Cell := oneBank p1756 ray1756
theorem signs1756 : ∀ j, Signs p1756 (bank1756 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1757 := params 28
abbrev ray1757 := rays 28
def bank1757 : Fin 1 → Cell := oneBank p1757 ray1757
theorem signs1757 : ∀ j, Signs p1757 (bank1757 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1758 := params 29
abbrev ray1758 := rays 29
def bank1758 : Fin 1 → Cell := oneBank p1758 ray1758
theorem signs1758 : ∀ j, Signs p1758 (bank1758 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1759 := params 30
abbrev ray1759 := rays 30
def bank1759 : Fin 1 → Cell := oneBank p1759 ray1759
theorem signs1759 : ∀ j, Signs p1759 (bank1759 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1760 := params 31
abbrev ray1760 := rays 31
def bank1760 : Fin 1 → Cell := oneBank p1760 ray1760
theorem signs1760 : ∀ j, Signs p1760 (bank1760 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01729_01760
