/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01953_01984
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99699708386168,99699530389507,99699352369510,99699174326178,99698996259514,99698818169519,99698640056195,99698461919544,99698283759568,99698105576269,99697927369648,99697749139708,99697570886451,99697392609877,99697214309990,99697035986791,99696857640282,99696679270465,99696500877341,99696322460913,99696144021182,99695965558151,99695787071821,99695608562193,99695430029271,99695251473055,99695072893548,99694894290752,99694715664668,99694537015298,99694358342644,99694179646708,99694000927492]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1952+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(20617361436762452598088/28808040144563626493295:Fraction),(61846597083486711512314/86422370433692629479885:Fraction),(334276275260712495712/467138488830780429621:Fraction),(20611874866676143728352/28806290144565376493295:Fraction),(8832877049063548788896/12345302919099697068555:Fraction),(20608217974653096309512/28805123477899876493295:Fraction),(4121277889438751303720/5760908028913425298659:Fraction),(981169584538401171766/1371616991011160785395:Fraction),(1373515563933868269118/1920224898526775099553:Fraction),(2288989509826663671301/3200310016063208499255:Fraction),(6866359221201694368862/9600735603745375497765:Fraction),(12358350056634926802988/17280974086742025895977:Fraction),(20595422470927015997063/28801040144570626493295:Fraction),(8825826515617629508309/12343052919101947068555:Fraction),(252144101521855397440/352651511974348487673:Fraction),(326824465469392531099/457131589596386928465:Fraction),(8823477558844962179872/12342302919102697068555:Fraction),(12351772583439850467722/17278874086744125895977:Fraction),(6861486973318679120684/9599180048191375497765:Fraction),(61747903669695912419117/86390870433724129479885:Fraction),(61742424416954513906864/86389120433725879479885:Fraction),(2286553564127630227558/3199532238286208499255:Fraction),(12346293576682953951566/17277124086745875895977:Fraction),(12345198120537653207369/17276774086746225895977:Fraction),(1371566959099700221780/1919602676305175099553:Fraction),(12343007356732687388686/17276074086746925895977:Fraction),(61709560245410491569776/86378620433736379479885:Fraction),(20568028258203737718626/28792290144579376493295:Fraction),(8814087020203919223484/12339302919105697068555:Fraction),(8813304939395741353096/12339052919105947068555:Fraction),(979169203932934320956/1370978102122910785395:Fraction),(61682186187379978594898/86369870433745129479885:Fraction)]
abbrev p1953 := params 0
abbrev ray1953 := rays 0
def bank1953 : Fin 1 → Cell := oneBank p1953 ray1953
theorem signs1953 : ∀ j, Signs p1953 (bank1953 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1954 := params 1
abbrev ray1954 := rays 1
def bank1954 : Fin 1 → Cell := oneBank p1954 ray1954
theorem signs1954 : ∀ j, Signs p1954 (bank1954 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1955 := params 2
abbrev ray1955 := rays 2
def bank1955 : Fin 1 → Cell := oneBank p1955 ray1955
theorem signs1955 : ∀ j, Signs p1955 (bank1955 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1956 := params 3
abbrev ray1956 := rays 3
def bank1956 : Fin 1 → Cell := oneBank p1956 ray1956
theorem signs1956 : ∀ j, Signs p1956 (bank1956 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1957 := params 4
abbrev ray1957 := rays 4
def bank1957 : Fin 1 → Cell := oneBank p1957 ray1957
theorem signs1957 : ∀ j, Signs p1957 (bank1957 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1958 := params 5
abbrev ray1958 := rays 5
def bank1958 : Fin 1 → Cell := oneBank p1958 ray1958
theorem signs1958 : ∀ j, Signs p1958 (bank1958 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1959 := params 6
abbrev ray1959 := rays 6
def bank1959 : Fin 1 → Cell := oneBank p1959 ray1959
theorem signs1959 : ∀ j, Signs p1959 (bank1959 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1960 := params 7
abbrev ray1960 := rays 7
def bank1960 : Fin 1 → Cell := oneBank p1960 ray1960
theorem signs1960 : ∀ j, Signs p1960 (bank1960 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1961 := params 8
abbrev ray1961 := rays 8
def bank1961 : Fin 1 → Cell := oneBank p1961 ray1961
theorem signs1961 : ∀ j, Signs p1961 (bank1961 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1962 := params 9
abbrev ray1962 := rays 9
def bank1962 : Fin 1 → Cell := oneBank p1962 ray1962
theorem signs1962 : ∀ j, Signs p1962 (bank1962 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1963 := params 10
abbrev ray1963 := rays 10
def bank1963 : Fin 1 → Cell := oneBank p1963 ray1963
theorem signs1963 : ∀ j, Signs p1963 (bank1963 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1964 := params 11
abbrev ray1964 := rays 11
def bank1964 : Fin 1 → Cell := oneBank p1964 ray1964
theorem signs1964 : ∀ j, Signs p1964 (bank1964 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1965 := params 12
abbrev ray1965 := rays 12
def bank1965 : Fin 1 → Cell := oneBank p1965 ray1965
theorem signs1965 : ∀ j, Signs p1965 (bank1965 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1966 := params 13
abbrev ray1966 := rays 13
def bank1966 : Fin 1 → Cell := oneBank p1966 ray1966
theorem signs1966 : ∀ j, Signs p1966 (bank1966 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1967 := params 14
abbrev ray1967 := rays 14
def bank1967 : Fin 1 → Cell := oneBank p1967 ray1967
theorem signs1967 : ∀ j, Signs p1967 (bank1967 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1968 := params 15
abbrev ray1968 := rays 15
def bank1968 : Fin 1 → Cell := oneBank p1968 ray1968
theorem signs1968 : ∀ j, Signs p1968 (bank1968 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1969 := params 16
abbrev ray1969 := rays 16
def bank1969 : Fin 1 → Cell := oneBank p1969 ray1969
theorem signs1969 : ∀ j, Signs p1969 (bank1969 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1970 := params 17
abbrev ray1970 := rays 17
def bank1970 : Fin 1 → Cell := oneBank p1970 ray1970
theorem signs1970 : ∀ j, Signs p1970 (bank1970 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1971 := params 18
abbrev ray1971 := rays 18
def bank1971 : Fin 1 → Cell := oneBank p1971 ray1971
theorem signs1971 : ∀ j, Signs p1971 (bank1971 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1972 := params 19
abbrev ray1972 := rays 19
def bank1972 : Fin 1 → Cell := oneBank p1972 ray1972
theorem signs1972 : ∀ j, Signs p1972 (bank1972 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1973 := params 20
abbrev ray1973 := rays 20
def bank1973 : Fin 1 → Cell := oneBank p1973 ray1973
theorem signs1973 : ∀ j, Signs p1973 (bank1973 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1974 := params 21
abbrev ray1974 := rays 21
def bank1974 : Fin 1 → Cell := oneBank p1974 ray1974
theorem signs1974 : ∀ j, Signs p1974 (bank1974 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1975 := params 22
abbrev ray1975 := rays 22
def bank1975 : Fin 1 → Cell := oneBank p1975 ray1975
theorem signs1975 : ∀ j, Signs p1975 (bank1975 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1976 := params 23
abbrev ray1976 := rays 23
def bank1976 : Fin 1 → Cell := oneBank p1976 ray1976
theorem signs1976 : ∀ j, Signs p1976 (bank1976 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1977 := params 24
abbrev ray1977 := rays 24
def bank1977 : Fin 1 → Cell := oneBank p1977 ray1977
theorem signs1977 : ∀ j, Signs p1977 (bank1977 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1978 := params 25
abbrev ray1978 := rays 25
def bank1978 : Fin 1 → Cell := oneBank p1978 ray1978
theorem signs1978 : ∀ j, Signs p1978 (bank1978 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1979 := params 26
abbrev ray1979 := rays 26
def bank1979 : Fin 1 → Cell := oneBank p1979 ray1979
theorem signs1979 : ∀ j, Signs p1979 (bank1979 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1980 := params 27
abbrev ray1980 := rays 27
def bank1980 : Fin 1 → Cell := oneBank p1980 ray1980
theorem signs1980 : ∀ j, Signs p1980 (bank1980 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1981 := params 28
abbrev ray1981 := rays 28
def bank1981 : Fin 1 → Cell := oneBank p1981 ray1981
theorem signs1981 : ∀ j, Signs p1981 (bank1981 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1982 := params 29
abbrev ray1982 := rays 29
def bank1982 : Fin 1 → Cell := oneBank p1982 ray1982
theorem signs1982 : ∀ j, Signs p1982 (bank1982 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1983 := params 30
abbrev ray1983 := rays 30
def bank1983 : Fin 1 → Cell := oneBank p1983 ray1983
theorem signs1983 : ∀ j, Signs p1983 (bank1983 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1984 := params 31
abbrev ray1984 := rays 31
def bank1984 : Fin 1 → Cell := oneBank p1984 ray1984
theorem signs1984 : ∀ j, Signs p1984 (bank1984 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01953_01984
