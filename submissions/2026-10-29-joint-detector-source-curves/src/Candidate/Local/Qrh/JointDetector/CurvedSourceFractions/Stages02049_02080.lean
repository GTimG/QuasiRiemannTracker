/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02049_02080
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99682511914724,99682331529972,99682151117571,99681970677522,99681790209827,99681609714488,99681429191506,99681248640882,99681068062618,99680887456715,99680706823175,99680526161999,99680345473189,99680164756746,99679984012671,99679803240966,99679622441632,99679441614671,99679260760084,99679079877873,99678898968039,99678718030583,99678537065507,99678356072812,99678175052500,99677994004572,99677812929030,99677631825875,99677450695109,99677269536733,99677088350748,99676907137156,99676725895958]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2048+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2049 := params 0
abbrev ray2049 := rays 0
def bank2049 : Fin 2 → Cell := twoBank p2049 ray2049
theorem signs2049 : ∀ j, Signs p2049 (bank2049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2050 := params 1
abbrev ray2050 := rays 1
def bank2050 : Fin 2 → Cell := twoBank p2050 ray2050
theorem signs2050 : ∀ j, Signs p2050 (bank2050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2051 := params 2
abbrev ray2051 := rays 2
def bank2051 : Fin 2 → Cell := twoBank p2051 ray2051
theorem signs2051 : ∀ j, Signs p2051 (bank2051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2052 := params 3
abbrev ray2052 := rays 3
def bank2052 : Fin 2 → Cell := twoBank p2052 ray2052
theorem signs2052 : ∀ j, Signs p2052 (bank2052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2053 := params 4
abbrev ray2053 := rays 4
def bank2053 : Fin 2 → Cell := twoBank p2053 ray2053
theorem signs2053 : ∀ j, Signs p2053 (bank2053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2054 := params 5
abbrev ray2054 := rays 5
def bank2054 : Fin 2 → Cell := twoBank p2054 ray2054
theorem signs2054 : ∀ j, Signs p2054 (bank2054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2055 := params 6
abbrev ray2055 := rays 6
def bank2055 : Fin 2 → Cell := twoBank p2055 ray2055
theorem signs2055 : ∀ j, Signs p2055 (bank2055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2056 := params 7
abbrev ray2056 := rays 7
def bank2056 : Fin 2 → Cell := twoBank p2056 ray2056
theorem signs2056 : ∀ j, Signs p2056 (bank2056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2057 := params 8
abbrev ray2057 := rays 8
def bank2057 : Fin 2 → Cell := twoBank p2057 ray2057
theorem signs2057 : ∀ j, Signs p2057 (bank2057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2058 := params 9
abbrev ray2058 := rays 9
def bank2058 : Fin 2 → Cell := twoBank p2058 ray2058
theorem signs2058 : ∀ j, Signs p2058 (bank2058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2059 := params 10
abbrev ray2059 := rays 10
def bank2059 : Fin 2 → Cell := twoBank p2059 ray2059
theorem signs2059 : ∀ j, Signs p2059 (bank2059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2060 := params 11
abbrev ray2060 := rays 11
def bank2060 : Fin 2 → Cell := twoBank p2060 ray2060
theorem signs2060 : ∀ j, Signs p2060 (bank2060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2061 := params 12
abbrev ray2061 := rays 12
def bank2061 : Fin 2 → Cell := twoBank p2061 ray2061
theorem signs2061 : ∀ j, Signs p2061 (bank2061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2062 := params 13
abbrev ray2062 := rays 13
def bank2062 : Fin 2 → Cell := twoBank p2062 ray2062
theorem signs2062 : ∀ j, Signs p2062 (bank2062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2063 := params 14
abbrev ray2063 := rays 14
def bank2063 : Fin 2 → Cell := twoBank p2063 ray2063
theorem signs2063 : ∀ j, Signs p2063 (bank2063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2064 := params 15
abbrev ray2064 := rays 15
def bank2064 : Fin 2 → Cell := twoBank p2064 ray2064
theorem signs2064 : ∀ j, Signs p2064 (bank2064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2065 := params 16
abbrev ray2065 := rays 16
def bank2065 : Fin 2 → Cell := twoBank p2065 ray2065
theorem signs2065 : ∀ j, Signs p2065 (bank2065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2066 := params 17
abbrev ray2066 := rays 17
def bank2066 : Fin 2 → Cell := twoBank p2066 ray2066
theorem signs2066 : ∀ j, Signs p2066 (bank2066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2067 := params 18
abbrev ray2067 := rays 18
def bank2067 : Fin 2 → Cell := twoBank p2067 ray2067
theorem signs2067 : ∀ j, Signs p2067 (bank2067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2068 := params 19
abbrev ray2068 := rays 19
def bank2068 : Fin 2 → Cell := twoBank p2068 ray2068
theorem signs2068 : ∀ j, Signs p2068 (bank2068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2069 := params 20
abbrev ray2069 := rays 20
def bank2069 : Fin 2 → Cell := twoBank p2069 ray2069
theorem signs2069 : ∀ j, Signs p2069 (bank2069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2070 := params 21
abbrev ray2070 := rays 21
def bank2070 : Fin 2 → Cell := twoBank p2070 ray2070
theorem signs2070 : ∀ j, Signs p2070 (bank2070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2071 := params 22
abbrev ray2071 := rays 22
def bank2071 : Fin 2 → Cell := twoBank p2071 ray2071
theorem signs2071 : ∀ j, Signs p2071 (bank2071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2072 := params 23
abbrev ray2072 := rays 23
def bank2072 : Fin 2 → Cell := twoBank p2072 ray2072
theorem signs2072 : ∀ j, Signs p2072 (bank2072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2073 := params 24
abbrev ray2073 := rays 24
def bank2073 : Fin 2 → Cell := twoBank p2073 ray2073
theorem signs2073 : ∀ j, Signs p2073 (bank2073 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2074 := params 25
abbrev ray2074 := rays 25
def bank2074 : Fin 2 → Cell := twoBank p2074 ray2074
theorem signs2074 : ∀ j, Signs p2074 (bank2074 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2075 := params 26
abbrev ray2075 := rays 26
def bank2075 : Fin 2 → Cell := twoBank p2075 ray2075
theorem signs2075 : ∀ j, Signs p2075 (bank2075 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2076 := params 27
abbrev ray2076 := rays 27
def bank2076 : Fin 2 → Cell := twoBank p2076 ray2076
theorem signs2076 : ∀ j, Signs p2076 (bank2076 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2077 := params 28
abbrev ray2077 := rays 28
def bank2077 : Fin 2 → Cell := twoBank p2077 ray2077
theorem signs2077 : ∀ j, Signs p2077 (bank2077 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2078 := params 29
abbrev ray2078 := rays 29
def bank2078 : Fin 2 → Cell := twoBank p2078 ray2078
theorem signs2078 : ∀ j, Signs p2078 (bank2078 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2079 := params 30
abbrev ray2079 := rays 30
def bank2079 : Fin 2 → Cell := twoBank p2079 ray2079
theorem signs2079 : ∀ j, Signs p2079 (bank2079 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2080 := params 31
abbrev ray2080 := rays 31
def bank2080 : Fin 2 → Cell := twoBank p2080 ray2080
theorem signs2080 : ∀ j, Signs p2080 (bank2080 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02049_02080
