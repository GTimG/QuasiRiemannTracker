/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12961_12992
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96297671237598,96297246994390,96296822734735,96296398458633,96295974166084,96295549857088,96295125531646,96294701189758,96294276831424,96293852456645,96293428065421,96293003657752,96292579233638,96292154793080,96291730336078,96291305862632,96290881372742,96290456866409,96290032343633,96289607804414,96289183248753,96288758676649,96288334088103,96287909483115,96287484861686,96287060223816,96286635569505,96286210898753,96285786211561,96285361507928,96284936787856,96284512051344,96284087298393]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12960+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12961 := params 0
abbrev ray12961 := rays 0
def bank12961 : Fin 1 → Cell := oneBank p12961 ray12961
theorem signs12961 : ∀ j, Signs p12961 (bank12961 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12962 := params 1
abbrev ray12962 := rays 1
def bank12962 : Fin 1 → Cell := oneBank p12962 ray12962
theorem signs12962 : ∀ j, Signs p12962 (bank12962 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12963 := params 2
abbrev ray12963 := rays 2
def bank12963 : Fin 1 → Cell := oneBank p12963 ray12963
theorem signs12963 : ∀ j, Signs p12963 (bank12963 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12964 := params 3
abbrev ray12964 := rays 3
def bank12964 : Fin 1 → Cell := oneBank p12964 ray12964
theorem signs12964 : ∀ j, Signs p12964 (bank12964 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12965 := params 4
abbrev ray12965 := rays 4
def bank12965 : Fin 1 → Cell := oneBank p12965 ray12965
theorem signs12965 : ∀ j, Signs p12965 (bank12965 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12966 := params 5
abbrev ray12966 := rays 5
def bank12966 : Fin 1 → Cell := oneBank p12966 ray12966
theorem signs12966 : ∀ j, Signs p12966 (bank12966 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12967 := params 6
abbrev ray12967 := rays 6
def bank12967 : Fin 1 → Cell := oneBank p12967 ray12967
theorem signs12967 : ∀ j, Signs p12967 (bank12967 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12968 := params 7
abbrev ray12968 := rays 7
def bank12968 : Fin 1 → Cell := oneBank p12968 ray12968
theorem signs12968 : ∀ j, Signs p12968 (bank12968 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12969 := params 8
abbrev ray12969 := rays 8
def bank12969 : Fin 1 → Cell := oneBank p12969 ray12969
theorem signs12969 : ∀ j, Signs p12969 (bank12969 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12970 := params 9
abbrev ray12970 := rays 9
def bank12970 : Fin 1 → Cell := oneBank p12970 ray12970
theorem signs12970 : ∀ j, Signs p12970 (bank12970 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12971 := params 10
abbrev ray12971 := rays 10
def bank12971 : Fin 1 → Cell := oneBank p12971 ray12971
theorem signs12971 : ∀ j, Signs p12971 (bank12971 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12972 := params 11
abbrev ray12972 := rays 11
def bank12972 : Fin 1 → Cell := oneBank p12972 ray12972
theorem signs12972 : ∀ j, Signs p12972 (bank12972 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12973 := params 12
abbrev ray12973 := rays 12
def bank12973 : Fin 1 → Cell := oneBank p12973 ray12973
theorem signs12973 : ∀ j, Signs p12973 (bank12973 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12974 := params 13
abbrev ray12974 := rays 13
def bank12974 : Fin 1 → Cell := oneBank p12974 ray12974
theorem signs12974 : ∀ j, Signs p12974 (bank12974 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12975 := params 14
abbrev ray12975 := rays 14
def bank12975 : Fin 1 → Cell := oneBank p12975 ray12975
theorem signs12975 : ∀ j, Signs p12975 (bank12975 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12976 := params 15
abbrev ray12976 := rays 15
def bank12976 : Fin 1 → Cell := oneBank p12976 ray12976
theorem signs12976 : ∀ j, Signs p12976 (bank12976 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12977 := params 16
abbrev ray12977 := rays 16
def bank12977 : Fin 1 → Cell := oneBank p12977 ray12977
theorem signs12977 : ∀ j, Signs p12977 (bank12977 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12978 := params 17
abbrev ray12978 := rays 17
def bank12978 : Fin 1 → Cell := oneBank p12978 ray12978
theorem signs12978 : ∀ j, Signs p12978 (bank12978 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12979 := params 18
abbrev ray12979 := rays 18
def bank12979 : Fin 1 → Cell := oneBank p12979 ray12979
theorem signs12979 : ∀ j, Signs p12979 (bank12979 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12980 := params 19
abbrev ray12980 := rays 19
def bank12980 : Fin 1 → Cell := oneBank p12980 ray12980
theorem signs12980 : ∀ j, Signs p12980 (bank12980 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12981 := params 20
abbrev ray12981 := rays 20
def bank12981 : Fin 1 → Cell := oneBank p12981 ray12981
theorem signs12981 : ∀ j, Signs p12981 (bank12981 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12982 := params 21
abbrev ray12982 := rays 21
def bank12982 : Fin 1 → Cell := oneBank p12982 ray12982
theorem signs12982 : ∀ j, Signs p12982 (bank12982 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12983 := params 22
abbrev ray12983 := rays 22
def bank12983 : Fin 1 → Cell := oneBank p12983 ray12983
theorem signs12983 : ∀ j, Signs p12983 (bank12983 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12984 := params 23
abbrev ray12984 := rays 23
def bank12984 : Fin 1 → Cell := oneBank p12984 ray12984
theorem signs12984 : ∀ j, Signs p12984 (bank12984 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12985 := params 24
abbrev ray12985 := rays 24
def bank12985 : Fin 1 → Cell := oneBank p12985 ray12985
theorem signs12985 : ∀ j, Signs p12985 (bank12985 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12986 := params 25
abbrev ray12986 := rays 25
def bank12986 : Fin 1 → Cell := oneBank p12986 ray12986
theorem signs12986 : ∀ j, Signs p12986 (bank12986 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12987 := params 26
abbrev ray12987 := rays 26
def bank12987 : Fin 1 → Cell := oneBank p12987 ray12987
theorem signs12987 : ∀ j, Signs p12987 (bank12987 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12988 := params 27
abbrev ray12988 := rays 27
def bank12988 : Fin 1 → Cell := oneBank p12988 ray12988
theorem signs12988 : ∀ j, Signs p12988 (bank12988 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12989 := params 28
abbrev ray12989 := rays 28
def bank12989 : Fin 1 → Cell := oneBank p12989 ray12989
theorem signs12989 : ∀ j, Signs p12989 (bank12989 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12990 := params 29
abbrev ray12990 := rays 29
def bank12990 : Fin 1 → Cell := oneBank p12990 ray12990
theorem signs12990 : ∀ j, Signs p12990 (bank12990 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12991 := params 30
abbrev ray12991 := rays 30
def bank12991 : Fin 1 → Cell := oneBank p12991 ray12991
theorem signs12991 : ∀ j, Signs p12991 (bank12991 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12992 := params 31
abbrev ray12992 := rays 31
def bank12992 : Fin 1 → Cell := oneBank p12992 ray12992
theorem signs12992 : ∀ j, Signs p12992 (bank12992 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12961_12992
