/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01857_01888
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99716687123704,99716511376162,99716335605101,99716159810523,99715983992429,99715808150822,99715632285704,99715456397077,99715280484942,99715104549301,99714928590156,99714752607510,99714576601364,99714400571720,99714224518579,99714048441945,99713872341818,99713696218201,99713520071096,99713343900504,99713167706428,99712991488869,99712815247830,99712638983312,99712462695317,99712286383847,99712110048904,99711933690490,99711757308607,99711580903256,99711404474440,99711228022161,99711051546420]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1856+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(4158723752364899225548/5772808028901525298659:Fraction),(62375327055009086522764/86590370433524629479885:Fraction),(1781994253930330770161/2473960583815039413711:Fraction),(20788090594394011289654/28862290144509376493295:Fraction),(769861043378839540777/1068952104117652833085:Fraction),(62353217079084194740864/86583370433531629479885:Fraction),(20782563569216108735956/28860540144511126493295:Fraction),(6926907266603273232779/9619985603726125497765:Fraction),(62336639926187900730848/86578120433536879479885:Fraction),(593629659885078948989/824536861271796471237:Fraction),(8903655673284651243286/12367802919077197068555:Fraction),(6118808539331047984/8500036370499963621:Fraction),(6923837921841028549672/9619013381504875497765:Fraction),(12461803736698240433444/17313874086709125895977:Fraction),(62303494677157514834231/86567620433547379479885:Fraction),(21974593637635796598/30534698565625795231:Fraction),(62292451083401190619412/86564120433550879479885:Fraction),(62286929039279327550644/86562370433552629479885:Fraction),(60175273486733560760/83633449694255439111:Fraction),(8896555273354194024232/12365552919079447068555:Fraction),(62270366831875699106374/86557120433557879479885:Fraction),(1383663257456424376802/1923452676301325099553:Fraction),(12451865480592629980288/17310724086712275895977:Fraction),(62253808055701093391972/86551870433563129479885:Fraction),(4149885984818203636705/5770008028904325298659:Fraction),(62242771324205731766968/86548370433566629479885:Fraction),(62237253940046843409736/86546620433568379479885:Fraction),(1382927475362121962048/1923219342968225099553:Fraction),(336357945440686346257/467800650992280429621:Fraction),(240234375510470032364/334136565380593164015:Fraction),(460853232913781119978/641034225433891699851:Fraction),(12441934384439376873122/17307574086715425895977:Fraction)]
abbrev p1857 := params 0
abbrev ray1857 := rays 0
def bank1857 : Fin 1 → Cell := oneBank p1857 ray1857
theorem signs1857 : ∀ j, Signs p1857 (bank1857 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1858 := params 1
abbrev ray1858 := rays 1
def bank1858 : Fin 1 → Cell := oneBank p1858 ray1858
theorem signs1858 : ∀ j, Signs p1858 (bank1858 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1859 := params 2
abbrev ray1859 := rays 2
def bank1859 : Fin 1 → Cell := oneBank p1859 ray1859
theorem signs1859 : ∀ j, Signs p1859 (bank1859 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1860 := params 3
abbrev ray1860 := rays 3
def bank1860 : Fin 1 → Cell := oneBank p1860 ray1860
theorem signs1860 : ∀ j, Signs p1860 (bank1860 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1861 := params 4
abbrev ray1861 := rays 4
def bank1861 : Fin 1 → Cell := oneBank p1861 ray1861
theorem signs1861 : ∀ j, Signs p1861 (bank1861 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1862 := params 5
abbrev ray1862 := rays 5
def bank1862 : Fin 1 → Cell := oneBank p1862 ray1862
theorem signs1862 : ∀ j, Signs p1862 (bank1862 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1863 := params 6
abbrev ray1863 := rays 6
def bank1863 : Fin 1 → Cell := oneBank p1863 ray1863
theorem signs1863 : ∀ j, Signs p1863 (bank1863 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1864 := params 7
abbrev ray1864 := rays 7
def bank1864 : Fin 1 → Cell := oneBank p1864 ray1864
theorem signs1864 : ∀ j, Signs p1864 (bank1864 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1865 := params 8
abbrev ray1865 := rays 8
def bank1865 : Fin 1 → Cell := oneBank p1865 ray1865
theorem signs1865 : ∀ j, Signs p1865 (bank1865 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1866 := params 9
abbrev ray1866 := rays 9
def bank1866 : Fin 1 → Cell := oneBank p1866 ray1866
theorem signs1866 : ∀ j, Signs p1866 (bank1866 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1867 := params 10
abbrev ray1867 := rays 10
def bank1867 : Fin 1 → Cell := oneBank p1867 ray1867
theorem signs1867 : ∀ j, Signs p1867 (bank1867 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1868 := params 11
abbrev ray1868 := rays 11
def bank1868 : Fin 1 → Cell := oneBank p1868 ray1868
theorem signs1868 : ∀ j, Signs p1868 (bank1868 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1869 := params 12
abbrev ray1869 := rays 12
def bank1869 : Fin 1 → Cell := oneBank p1869 ray1869
theorem signs1869 : ∀ j, Signs p1869 (bank1869 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1870 := params 13
abbrev ray1870 := rays 13
def bank1870 : Fin 1 → Cell := oneBank p1870 ray1870
theorem signs1870 : ∀ j, Signs p1870 (bank1870 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1871 := params 14
abbrev ray1871 := rays 14
def bank1871 : Fin 1 → Cell := oneBank p1871 ray1871
theorem signs1871 : ∀ j, Signs p1871 (bank1871 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1872 := params 15
abbrev ray1872 := rays 15
def bank1872 : Fin 1 → Cell := oneBank p1872 ray1872
theorem signs1872 : ∀ j, Signs p1872 (bank1872 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1873 := params 16
abbrev ray1873 := rays 16
def bank1873 : Fin 1 → Cell := oneBank p1873 ray1873
theorem signs1873 : ∀ j, Signs p1873 (bank1873 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1874 := params 17
abbrev ray1874 := rays 17
def bank1874 : Fin 1 → Cell := oneBank p1874 ray1874
theorem signs1874 : ∀ j, Signs p1874 (bank1874 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1875 := params 18
abbrev ray1875 := rays 18
def bank1875 : Fin 1 → Cell := oneBank p1875 ray1875
theorem signs1875 : ∀ j, Signs p1875 (bank1875 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1876 := params 19
abbrev ray1876 := rays 19
def bank1876 : Fin 1 → Cell := oneBank p1876 ray1876
theorem signs1876 : ∀ j, Signs p1876 (bank1876 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1877 := params 20
abbrev ray1877 := rays 20
def bank1877 : Fin 1 → Cell := oneBank p1877 ray1877
theorem signs1877 : ∀ j, Signs p1877 (bank1877 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1878 := params 21
abbrev ray1878 := rays 21
def bank1878 : Fin 1 → Cell := oneBank p1878 ray1878
theorem signs1878 : ∀ j, Signs p1878 (bank1878 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1879 := params 22
abbrev ray1879 := rays 22
def bank1879 : Fin 1 → Cell := oneBank p1879 ray1879
theorem signs1879 : ∀ j, Signs p1879 (bank1879 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1880 := params 23
abbrev ray1880 := rays 23
def bank1880 : Fin 1 → Cell := oneBank p1880 ray1880
theorem signs1880 : ∀ j, Signs p1880 (bank1880 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1881 := params 24
abbrev ray1881 := rays 24
def bank1881 : Fin 1 → Cell := oneBank p1881 ray1881
theorem signs1881 : ∀ j, Signs p1881 (bank1881 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1882 := params 25
abbrev ray1882 := rays 25
def bank1882 : Fin 1 → Cell := oneBank p1882 ray1882
theorem signs1882 : ∀ j, Signs p1882 (bank1882 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1883 := params 26
abbrev ray1883 := rays 26
def bank1883 : Fin 1 → Cell := oneBank p1883 ray1883
theorem signs1883 : ∀ j, Signs p1883 (bank1883 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1884 := params 27
abbrev ray1884 := rays 27
def bank1884 : Fin 1 → Cell := oneBank p1884 ray1884
theorem signs1884 : ∀ j, Signs p1884 (bank1884 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1885 := params 28
abbrev ray1885 := rays 28
def bank1885 : Fin 1 → Cell := oneBank p1885 ray1885
theorem signs1885 : ∀ j, Signs p1885 (bank1885 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1886 := params 29
abbrev ray1886 := rays 29
def bank1886 : Fin 1 → Cell := oneBank p1886 ray1886
theorem signs1886 : ∀ j, Signs p1886 (bank1886 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1887 := params 30
abbrev ray1887 := rays 30
def bank1887 : Fin 1 → Cell := oneBank p1887 ray1887
theorem signs1887 : ∀ j, Signs p1887 (bank1887 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1888 := params 31
abbrev ray1888 := rays 31
def bank1888 : Fin 1 → Cell := oneBank p1888 ray1888
theorem signs1888 : ∀ j, Signs p1888 (bank1888 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01857_01888
