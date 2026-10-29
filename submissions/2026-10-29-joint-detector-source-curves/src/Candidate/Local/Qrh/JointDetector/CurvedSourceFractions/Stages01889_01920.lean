/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01889_01920
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99711051546420,99710875047220,99710698524562,99710521978448,99710345408880,99710168815860,99709992199390,99709815559472,99709638896108,99709462209299,99709285499047,99709108765355,99708932008225,99708755227658,99708578423656,99708401596221,99708224745355,99708047871060,99707870973338,99707694052191,99707517107620,99707340139628,99707163148216,99706986133387,99706809095142,99706632033483,99706454948412,99706277839931,99706100708042,99705923552747,99705746374047,99705569171945,99705391946442]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1888+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(12440831201589942278968/17307224086715775895977:Fraction),(4146576077190503828110/5768958028905375298659:Fraction),(62193127371970339824628/86532620433582379479885:Fraction),(6909734824630753239046/9614541159287125497765:Fraction),(592210469590347355942/824086861272246471237:Fraction),(12435317251319771109304/17305474086717525895977:Fraction),(51169608453139833008/71214502414476855539:Fraction),(20721854040072713377456/28841290144530376493295:Fraction),(986667476734910902646/1373366991009410785395:Fraction),(62154539784113532356782/86520370433594629479885:Fraction),(4143268557978010957739/5767908028906425298659:Fraction),(12428703603950502145433/17303374086719625895977:Fraction),(428537982797414858735/596656002990343996413:Fraction),(41840066031041597240/58258161908149245441:Fraction),(12425397934243661424200/17302324086720675895977:Fraction),(460159119423799794770/640813855063741699851:Fraction),(197193563203461414800/274628953757482157079:Fraction),(12422092952143060941922/17301274086721725895977:Fraction),(62104956948269696186296/86504620433610379479885:Fraction),(766659879020320545774/1067936672019902833085:Fraction),(12418788657799463897444/17300224086722775895977:Fraction),(20696145814081610703014/28833123477871876493295:Fraction),(20694310477171380007744/28832540144539126493295:Fraction),(1677768283398753399986/2337726227935652148105:Fraction),(12414384275212421318528/17298824086724175895977:Fraction),(1379253718475865887315/1922052676302725099553:Fraction),(1773168946368028854596/2471160583817839413711:Fraction),(667262472897483148702/929987854125012144945:Fraction),(20683302224070908571448/28829040144542626493295:Fraction),(62044404430151636657063/86485370433629629479885:Fraction),(3303280018332252412/4604846410395153585:Fraction),(459506671731190937498/640606447656541699851:Fraction)]
abbrev p1889 := params 0
abbrev ray1889 := rays 0
def bank1889 : Fin 1 → Cell := oneBank p1889 ray1889
theorem signs1889 : ∀ j, Signs p1889 (bank1889 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1890 := params 1
abbrev ray1890 := rays 1
def bank1890 : Fin 1 → Cell := oneBank p1890 ray1890
theorem signs1890 : ∀ j, Signs p1890 (bank1890 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1891 := params 2
abbrev ray1891 := rays 2
def bank1891 : Fin 1 → Cell := oneBank p1891 ray1891
theorem signs1891 : ∀ j, Signs p1891 (bank1891 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1892 := params 3
abbrev ray1892 := rays 3
def bank1892 : Fin 1 → Cell := oneBank p1892 ray1892
theorem signs1892 : ∀ j, Signs p1892 (bank1892 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1893 := params 4
abbrev ray1893 := rays 4
def bank1893 : Fin 1 → Cell := oneBank p1893 ray1893
theorem signs1893 : ∀ j, Signs p1893 (bank1893 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1894 := params 5
abbrev ray1894 := rays 5
def bank1894 : Fin 1 → Cell := oneBank p1894 ray1894
theorem signs1894 : ∀ j, Signs p1894 (bank1894 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1895 := params 6
abbrev ray1895 := rays 6
def bank1895 : Fin 1 → Cell := oneBank p1895 ray1895
theorem signs1895 : ∀ j, Signs p1895 (bank1895 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1896 := params 7
abbrev ray1896 := rays 7
def bank1896 : Fin 1 → Cell := oneBank p1896 ray1896
theorem signs1896 : ∀ j, Signs p1896 (bank1896 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1897 := params 8
abbrev ray1897 := rays 8
def bank1897 : Fin 1 → Cell := oneBank p1897 ray1897
theorem signs1897 : ∀ j, Signs p1897 (bank1897 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1898 := params 9
abbrev ray1898 := rays 9
def bank1898 : Fin 1 → Cell := oneBank p1898 ray1898
theorem signs1898 : ∀ j, Signs p1898 (bank1898 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1899 := params 10
abbrev ray1899 := rays 10
def bank1899 : Fin 1 → Cell := oneBank p1899 ray1899
theorem signs1899 : ∀ j, Signs p1899 (bank1899 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1900 := params 11
abbrev ray1900 := rays 11
def bank1900 : Fin 1 → Cell := oneBank p1900 ray1900
theorem signs1900 : ∀ j, Signs p1900 (bank1900 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1901 := params 12
abbrev ray1901 := rays 12
def bank1901 : Fin 1 → Cell := oneBank p1901 ray1901
theorem signs1901 : ∀ j, Signs p1901 (bank1901 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1902 := params 13
abbrev ray1902 := rays 13
def bank1902 : Fin 1 → Cell := oneBank p1902 ray1902
theorem signs1902 : ∀ j, Signs p1902 (bank1902 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1903 := params 14
abbrev ray1903 := rays 14
def bank1903 : Fin 1 → Cell := oneBank p1903 ray1903
theorem signs1903 : ∀ j, Signs p1903 (bank1903 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1904 := params 15
abbrev ray1904 := rays 15
def bank1904 : Fin 1 → Cell := oneBank p1904 ray1904
theorem signs1904 : ∀ j, Signs p1904 (bank1904 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1905 := params 16
abbrev ray1905 := rays 16
def bank1905 : Fin 1 → Cell := oneBank p1905 ray1905
theorem signs1905 : ∀ j, Signs p1905 (bank1905 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1906 := params 17
abbrev ray1906 := rays 17
def bank1906 : Fin 1 → Cell := oneBank p1906 ray1906
theorem signs1906 : ∀ j, Signs p1906 (bank1906 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1907 := params 18
abbrev ray1907 := rays 18
def bank1907 : Fin 1 → Cell := oneBank p1907 ray1907
theorem signs1907 : ∀ j, Signs p1907 (bank1907 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1908 := params 19
abbrev ray1908 := rays 19
def bank1908 : Fin 1 → Cell := oneBank p1908 ray1908
theorem signs1908 : ∀ j, Signs p1908 (bank1908 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1909 := params 20
abbrev ray1909 := rays 20
def bank1909 : Fin 1 → Cell := oneBank p1909 ray1909
theorem signs1909 : ∀ j, Signs p1909 (bank1909 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1910 := params 21
abbrev ray1910 := rays 21
def bank1910 : Fin 1 → Cell := oneBank p1910 ray1910
theorem signs1910 : ∀ j, Signs p1910 (bank1910 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1911 := params 22
abbrev ray1911 := rays 22
def bank1911 : Fin 1 → Cell := oneBank p1911 ray1911
theorem signs1911 : ∀ j, Signs p1911 (bank1911 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1912 := params 23
abbrev ray1912 := rays 23
def bank1912 : Fin 1 → Cell := oneBank p1912 ray1912
theorem signs1912 : ∀ j, Signs p1912 (bank1912 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1913 := params 24
abbrev ray1913 := rays 24
def bank1913 : Fin 1 → Cell := oneBank p1913 ray1913
theorem signs1913 : ∀ j, Signs p1913 (bank1913 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1914 := params 25
abbrev ray1914 := rays 25
def bank1914 : Fin 1 → Cell := oneBank p1914 ray1914
theorem signs1914 : ∀ j, Signs p1914 (bank1914 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1915 := params 26
abbrev ray1915 := rays 26
def bank1915 : Fin 1 → Cell := oneBank p1915 ray1915
theorem signs1915 : ∀ j, Signs p1915 (bank1915 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1916 := params 27
abbrev ray1916 := rays 27
def bank1916 : Fin 1 → Cell := oneBank p1916 ray1916
theorem signs1916 : ∀ j, Signs p1916 (bank1916 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1917 := params 28
abbrev ray1917 := rays 28
def bank1917 : Fin 1 → Cell := oneBank p1917 ray1917
theorem signs1917 : ∀ j, Signs p1917 (bank1917 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1918 := params 29
abbrev ray1918 := rays 29
def bank1918 : Fin 1 → Cell := oneBank p1918 ray1918
theorem signs1918 : ∀ j, Signs p1918 (bank1918 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1919 := params 30
abbrev ray1919 := rays 30
def bank1919 : Fin 1 → Cell := oneBank p1919 ray1919
theorem signs1919 : ∀ j, Signs p1919 (bank1919 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1920 := params 31
abbrev ray1920 := rays 31
def bank1920 : Fin 1 → Cell := oneBank p1920 ray1920
theorem signs1920 : ∀ j, Signs p1920 (bank1920 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01889_01920
