/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01793_01824
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99727885957938,99727711719655,99727537457728,99727363172159,99727188862951,99727014530105,99726840173624,99726665793509,99726491389762,99726316962385,99726142511380,99725968036749,99725793538494,99725619016617,99725444471120,99725269902005,99725095309274,99724920692928,99724746052970,99724571389402,99724396702225,99724221991442,99724047257054,99723872499064,99723697717474,99723522912285,99723348083499,99723173231119,99722998355146,99722823455582,99722648532429,99722473585689,99722298615364]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1792+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(20911860689100222963164/28901373477803626493295:Fraction),(1394000591627824038244/1926719342964725099553:Fraction),(20908157004188849812558/28900206811138126493295:Fraction),(4181261015683587973042/5779924695561075298659:Fraction),(2322717056247202697864/3211004460496958499255:Fraction),(12541561127103019775326/17339074086683925895977:Fraction),(12540450362632790490442/17338724086684275895977:Fraction),(2322099919417775584048/3210810016052708499255:Fraction),(20897048298759306034576/28896706811141626493295:Fraction),(4179039453452678930456/5779224695561775298659:Fraction),(4178669317883950863730/5779108028895225298659:Fraction),(62674487568289775861414/86684870433430129479885:Fraction),(62668936429351915668032/86683120433431879479885:Fraction),(1392519669422725030682/1926252676298525099553:Fraction),(4177188991986651158534/5778641362229025298659:Fraction),(464090996068389688108/642058299506941699851:Fraction),(4176449007989778113968/5778408028895925298659:Fraction),(62641185604162483635992/86674370433440629479885:Fraction),(12527127429946860344116/17334524086688475895977:Fraction),(6958898725450672401272/9630096714827125497765:Fraction),(1789272564061039516555/2476260583812739413711:Fraction),(12523798403314208900492/17333474086689525895977:Fraction),(6957049483601130654112/9629513381494375497765:Fraction),(62607898522093438546486/86663870433451129479885:Fraction),(20867450917752331345036/28887373477817626493295:Fraction),(1391040151518015482705/1925786009632325099553:Fraction),(62591260717264258417747/86658620433456379479885:Fraction),(62585715677796393297848/86656870433458129479885:Fraction),(1227062190195239676392/1699120008499213323135:Fraction),(1097800483440392118112/1520234569008098762805:Fraction),(62569083246241480424438/86651620433463379479885:Fraction),(6951504444234173025863/9627763381496125497765:Fraction)]
abbrev p1793 := params 0
abbrev ray1793 := rays 0
def bank1793 : Fin 1 → Cell := oneBank p1793 ray1793
theorem signs1793 : ∀ j, Signs p1793 (bank1793 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1794 := params 1
abbrev ray1794 := rays 1
def bank1794 : Fin 1 → Cell := oneBank p1794 ray1794
theorem signs1794 : ∀ j, Signs p1794 (bank1794 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1795 := params 2
abbrev ray1795 := rays 2
def bank1795 : Fin 1 → Cell := oneBank p1795 ray1795
theorem signs1795 : ∀ j, Signs p1795 (bank1795 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1796 := params 3
abbrev ray1796 := rays 3
def bank1796 : Fin 1 → Cell := oneBank p1796 ray1796
theorem signs1796 : ∀ j, Signs p1796 (bank1796 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1797 := params 4
abbrev ray1797 := rays 4
def bank1797 : Fin 1 → Cell := oneBank p1797 ray1797
theorem signs1797 : ∀ j, Signs p1797 (bank1797 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1798 := params 5
abbrev ray1798 := rays 5
def bank1798 : Fin 1 → Cell := oneBank p1798 ray1798
theorem signs1798 : ∀ j, Signs p1798 (bank1798 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1799 := params 6
abbrev ray1799 := rays 6
def bank1799 : Fin 1 → Cell := oneBank p1799 ray1799
theorem signs1799 : ∀ j, Signs p1799 (bank1799 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1800 := params 7
abbrev ray1800 := rays 7
def bank1800 : Fin 1 → Cell := oneBank p1800 ray1800
theorem signs1800 : ∀ j, Signs p1800 (bank1800 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1801 := params 8
abbrev ray1801 := rays 8
def bank1801 : Fin 1 → Cell := oneBank p1801 ray1801
theorem signs1801 : ∀ j, Signs p1801 (bank1801 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1802 := params 9
abbrev ray1802 := rays 9
def bank1802 : Fin 1 → Cell := oneBank p1802 ray1802
theorem signs1802 : ∀ j, Signs p1802 (bank1802 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1803 := params 10
abbrev ray1803 := rays 10
def bank1803 : Fin 1 → Cell := oneBank p1803 ray1803
theorem signs1803 : ∀ j, Signs p1803 (bank1803 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1804 := params 11
abbrev ray1804 := rays 11
def bank1804 : Fin 1 → Cell := oneBank p1804 ray1804
theorem signs1804 : ∀ j, Signs p1804 (bank1804 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1805 := params 12
abbrev ray1805 := rays 12
def bank1805 : Fin 1 → Cell := oneBank p1805 ray1805
theorem signs1805 : ∀ j, Signs p1805 (bank1805 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1806 := params 13
abbrev ray1806 := rays 13
def bank1806 : Fin 1 → Cell := oneBank p1806 ray1806
theorem signs1806 : ∀ j, Signs p1806 (bank1806 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1807 := params 14
abbrev ray1807 := rays 14
def bank1807 : Fin 1 → Cell := oneBank p1807 ray1807
theorem signs1807 : ∀ j, Signs p1807 (bank1807 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1808 := params 15
abbrev ray1808 := rays 15
def bank1808 : Fin 1 → Cell := oneBank p1808 ray1808
theorem signs1808 : ∀ j, Signs p1808 (bank1808 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1809 := params 16
abbrev ray1809 := rays 16
def bank1809 : Fin 1 → Cell := oneBank p1809 ray1809
theorem signs1809 : ∀ j, Signs p1809 (bank1809 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1810 := params 17
abbrev ray1810 := rays 17
def bank1810 : Fin 1 → Cell := oneBank p1810 ray1810
theorem signs1810 : ∀ j, Signs p1810 (bank1810 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1811 := params 18
abbrev ray1811 := rays 18
def bank1811 : Fin 1 → Cell := oneBank p1811 ray1811
theorem signs1811 : ∀ j, Signs p1811 (bank1811 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1812 := params 19
abbrev ray1812 := rays 19
def bank1812 : Fin 1 → Cell := oneBank p1812 ray1812
theorem signs1812 : ∀ j, Signs p1812 (bank1812 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1813 := params 20
abbrev ray1813 := rays 20
def bank1813 : Fin 1 → Cell := oneBank p1813 ray1813
theorem signs1813 : ∀ j, Signs p1813 (bank1813 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1814 := params 21
abbrev ray1814 := rays 21
def bank1814 : Fin 1 → Cell := oneBank p1814 ray1814
theorem signs1814 : ∀ j, Signs p1814 (bank1814 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1815 := params 22
abbrev ray1815 := rays 22
def bank1815 : Fin 1 → Cell := oneBank p1815 ray1815
theorem signs1815 : ∀ j, Signs p1815 (bank1815 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1816 := params 23
abbrev ray1816 := rays 23
def bank1816 : Fin 1 → Cell := oneBank p1816 ray1816
theorem signs1816 : ∀ j, Signs p1816 (bank1816 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1817 := params 24
abbrev ray1817 := rays 24
def bank1817 : Fin 1 → Cell := oneBank p1817 ray1817
theorem signs1817 : ∀ j, Signs p1817 (bank1817 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1818 := params 25
abbrev ray1818 := rays 25
def bank1818 : Fin 1 → Cell := oneBank p1818 ray1818
theorem signs1818 : ∀ j, Signs p1818 (bank1818 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1819 := params 26
abbrev ray1819 := rays 26
def bank1819 : Fin 1 → Cell := oneBank p1819 ray1819
theorem signs1819 : ∀ j, Signs p1819 (bank1819 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1820 := params 27
abbrev ray1820 := rays 27
def bank1820 : Fin 1 → Cell := oneBank p1820 ray1820
theorem signs1820 : ∀ j, Signs p1820 (bank1820 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1821 := params 28
abbrev ray1821 := rays 28
def bank1821 : Fin 1 → Cell := oneBank p1821 ray1821
theorem signs1821 : ∀ j, Signs p1821 (bank1821 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1822 := params 29
abbrev ray1822 := rays 29
def bank1822 : Fin 1 → Cell := oneBank p1822 ray1822
theorem signs1822 : ∀ j, Signs p1822 (bank1822 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1823 := params 30
abbrev ray1823 := rays 30
def bank1823 : Fin 1 → Cell := oneBank p1823 ray1823
theorem signs1823 : ∀ j, Signs p1823 (bank1823 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1824 := params 31
abbrev ray1824 := rays 31
def bank1824 : Fin 1 → Cell := oneBank p1824 ray1824
theorem signs1824 : ∀ j, Signs p1824 (bank1824 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01793_01824
