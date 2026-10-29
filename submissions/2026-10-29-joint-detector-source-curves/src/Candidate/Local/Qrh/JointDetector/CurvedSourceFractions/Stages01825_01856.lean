/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01825_01856
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99722298615364,99722123621456,99721948603967,99721773562899,99721598498254,99721423410033,99721248298239,99721073162874,99720898003939,99720722821437,99720547615369,99720372385737,99720197132544,99720021855791,99719846555480,99719671231613,99719495884192,99719320513219,99719145118696,99718969700625,99718794259008,99718618793847,99718443305143,99718267792899,99718092257116,99717916697797,99717741114944,99717565508558,99717389878641,99717214225196,99717038548223,99716862847725,99716687123704]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1824+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(1390177729150039149646/1925513787410375099553:Fraction),(20850818486491459943014/28882123477822876493295:Fraction),(6949656993476123393717/9627180048163375497765:Fraction),(62541371484972191668018/86642870433472129479885:Fraction),(2316141892243955238752/3208930386424958499255:Fraction),(4168686035358187892614/5775958028898375298659:Fraction),(62524749804341034844696/86637620433477379479885:Fraction),(62519210140334963813996/86635870433479129479885:Fraction),(6945963367839671016974/9626013381497875497765:Fraction),(1785946615510842653986/2475210583813789413711:Fraction),(62502593837352405812153/86630620433484379479885:Fraction),(2314705731046247939663/3208476682721708499255:Fraction),(62491517929246455391394/86627120433487879479885:Fraction),(62485980954603711505339/86625370433489629479885:Fraction),(1388454306985114286618/1924969342966475099553:Fraction),(20824969245459939854276/28873956811164376493295:Fraction),(12493874298569132944702/17324024086698975895977:Fraction),(462695083790439852565/641617558766641699851:Fraction),(337612437648844588222/468197948289180429621:Fraction),(12490553336167120471820/17322974086700025895977:Fraction),(770953484335124515386/1069297783129652833085:Fraction),(20813899614667219403761/28870456811167876493295:Fraction),(62436165291414260981093/86609620433505379479885:Fraction),(2972887217780648977247/4124184306357482356185:Fraction),(62425100146085823477122/86606120433508879479885:Fraction),(12483913465067364312190/17320874086702125895977:Fraction),(20804678522435853987892/28867540144504126493295:Fraction),(62408504872048076007032/86600870433514129479885:Fraction),(770407086561549091544/1069124943623652833085:Fraction),(112427827412195100860/156031298078410143207:Fraction),(62391914250793840222708/86595620433519379479885:Fraction),(4159092274838191688810/5772924695568075298659:Fraction)]
abbrev p1825 := params 0
abbrev ray1825 := rays 0
def bank1825 : Fin 1 → Cell := oneBank p1825 ray1825
theorem signs1825 : ∀ j, Signs p1825 (bank1825 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1826 := params 1
abbrev ray1826 := rays 1
def bank1826 : Fin 1 → Cell := oneBank p1826 ray1826
theorem signs1826 : ∀ j, Signs p1826 (bank1826 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1827 := params 2
abbrev ray1827 := rays 2
def bank1827 : Fin 1 → Cell := oneBank p1827 ray1827
theorem signs1827 : ∀ j, Signs p1827 (bank1827 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1828 := params 3
abbrev ray1828 := rays 3
def bank1828 : Fin 1 → Cell := oneBank p1828 ray1828
theorem signs1828 : ∀ j, Signs p1828 (bank1828 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1829 := params 4
abbrev ray1829 := rays 4
def bank1829 : Fin 1 → Cell := oneBank p1829 ray1829
theorem signs1829 : ∀ j, Signs p1829 (bank1829 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1830 := params 5
abbrev ray1830 := rays 5
def bank1830 : Fin 1 → Cell := oneBank p1830 ray1830
theorem signs1830 : ∀ j, Signs p1830 (bank1830 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1831 := params 6
abbrev ray1831 := rays 6
def bank1831 : Fin 1 → Cell := oneBank p1831 ray1831
theorem signs1831 : ∀ j, Signs p1831 (bank1831 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1832 := params 7
abbrev ray1832 := rays 7
def bank1832 : Fin 1 → Cell := oneBank p1832 ray1832
theorem signs1832 : ∀ j, Signs p1832 (bank1832 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1833 := params 8
abbrev ray1833 := rays 8
def bank1833 : Fin 1 → Cell := oneBank p1833 ray1833
theorem signs1833 : ∀ j, Signs p1833 (bank1833 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1834 := params 9
abbrev ray1834 := rays 9
def bank1834 : Fin 1 → Cell := oneBank p1834 ray1834
theorem signs1834 : ∀ j, Signs p1834 (bank1834 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1835 := params 10
abbrev ray1835 := rays 10
def bank1835 : Fin 1 → Cell := oneBank p1835 ray1835
theorem signs1835 : ∀ j, Signs p1835 (bank1835 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1836 := params 11
abbrev ray1836 := rays 11
def bank1836 : Fin 1 → Cell := oneBank p1836 ray1836
theorem signs1836 : ∀ j, Signs p1836 (bank1836 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1837 := params 12
abbrev ray1837 := rays 12
def bank1837 : Fin 1 → Cell := oneBank p1837 ray1837
theorem signs1837 : ∀ j, Signs p1837 (bank1837 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1838 := params 13
abbrev ray1838 := rays 13
def bank1838 : Fin 1 → Cell := oneBank p1838 ray1838
theorem signs1838 : ∀ j, Signs p1838 (bank1838 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1839 := params 14
abbrev ray1839 := rays 14
def bank1839 : Fin 1 → Cell := oneBank p1839 ray1839
theorem signs1839 : ∀ j, Signs p1839 (bank1839 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1840 := params 15
abbrev ray1840 := rays 15
def bank1840 : Fin 1 → Cell := oneBank p1840 ray1840
theorem signs1840 : ∀ j, Signs p1840 (bank1840 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1841 := params 16
abbrev ray1841 := rays 16
def bank1841 : Fin 1 → Cell := oneBank p1841 ray1841
theorem signs1841 : ∀ j, Signs p1841 (bank1841 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1842 := params 17
abbrev ray1842 := rays 17
def bank1842 : Fin 1 → Cell := oneBank p1842 ray1842
theorem signs1842 : ∀ j, Signs p1842 (bank1842 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1843 := params 18
abbrev ray1843 := rays 18
def bank1843 : Fin 1 → Cell := oneBank p1843 ray1843
theorem signs1843 : ∀ j, Signs p1843 (bank1843 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1844 := params 19
abbrev ray1844 := rays 19
def bank1844 : Fin 1 → Cell := oneBank p1844 ray1844
theorem signs1844 : ∀ j, Signs p1844 (bank1844 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1845 := params 20
abbrev ray1845 := rays 20
def bank1845 : Fin 1 → Cell := oneBank p1845 ray1845
theorem signs1845 : ∀ j, Signs p1845 (bank1845 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1846 := params 21
abbrev ray1846 := rays 21
def bank1846 : Fin 1 → Cell := oneBank p1846 ray1846
theorem signs1846 : ∀ j, Signs p1846 (bank1846 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1847 := params 22
abbrev ray1847 := rays 22
def bank1847 : Fin 1 → Cell := oneBank p1847 ray1847
theorem signs1847 : ∀ j, Signs p1847 (bank1847 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1848 := params 23
abbrev ray1848 := rays 23
def bank1848 : Fin 1 → Cell := oneBank p1848 ray1848
theorem signs1848 : ∀ j, Signs p1848 (bank1848 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1849 := params 24
abbrev ray1849 := rays 24
def bank1849 : Fin 1 → Cell := oneBank p1849 ray1849
theorem signs1849 : ∀ j, Signs p1849 (bank1849 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1850 := params 25
abbrev ray1850 := rays 25
def bank1850 : Fin 1 → Cell := oneBank p1850 ray1850
theorem signs1850 : ∀ j, Signs p1850 (bank1850 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1851 := params 26
abbrev ray1851 := rays 26
def bank1851 : Fin 1 → Cell := oneBank p1851 ray1851
theorem signs1851 : ∀ j, Signs p1851 (bank1851 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1852 := params 27
abbrev ray1852 := rays 27
def bank1852 : Fin 1 → Cell := oneBank p1852 ray1852
theorem signs1852 : ∀ j, Signs p1852 (bank1852 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1853 := params 28
abbrev ray1853 := rays 28
def bank1853 : Fin 1 → Cell := oneBank p1853 ray1853
theorem signs1853 : ∀ j, Signs p1853 (bank1853 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1854 := params 29
abbrev ray1854 := rays 29
def bank1854 : Fin 1 → Cell := oneBank p1854 ray1854
theorem signs1854 : ∀ j, Signs p1854 (bank1854 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1855 := params 30
abbrev ray1855 := rays 30
def bank1855 : Fin 1 → Cell := oneBank p1855 ray1855
theorem signs1855 : ∀ j, Signs p1855 (bank1855 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1856 := params 31
abbrev ray1856 := rays 31
def bank1856 : Fin 1 → Cell := oneBank p1856 ray1856
theorem signs1856 : ∀ j, Signs p1856 (bank1856 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01825_01856
