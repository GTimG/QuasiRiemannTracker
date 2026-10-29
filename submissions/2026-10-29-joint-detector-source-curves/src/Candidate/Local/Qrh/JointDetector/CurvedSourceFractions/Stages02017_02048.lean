/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02017_02048
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99688269619591,99688090120362,99687910593438,99687731038821,99687551456512,99687371846512,99687192208823,99687012543446,99686832850383,99686653129635,99686473381204,99686293605091,99686113801297,99685933969824,99685754110673,99685574223846,99685394309344,99685214367169,99685034397322,99684854399805,99684674374619,99684494321765,99684314241245,99684134133060,99683953997212,99683773833702,99683593642532,99683413423703,99683233177216,99683052903073,99682872601276,99682692271826,99682511914724]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2016+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2017 := params 0
abbrev ray2017 := rays 0
def bank2017 : Fin 2 → Cell := twoBank p2017 ray2017
theorem signs2017 : ∀ j, Signs p2017 (bank2017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2018 := params 1
abbrev ray2018 := rays 1
def bank2018 : Fin 2 → Cell := twoBank p2018 ray2018
theorem signs2018 : ∀ j, Signs p2018 (bank2018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2019 := params 2
abbrev ray2019 := rays 2
def bank2019 : Fin 2 → Cell := twoBank p2019 ray2019
theorem signs2019 : ∀ j, Signs p2019 (bank2019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2020 := params 3
abbrev ray2020 := rays 3
def bank2020 : Fin 2 → Cell := twoBank p2020 ray2020
theorem signs2020 : ∀ j, Signs p2020 (bank2020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2021 := params 4
abbrev ray2021 := rays 4
def bank2021 : Fin 2 → Cell := twoBank p2021 ray2021
theorem signs2021 : ∀ j, Signs p2021 (bank2021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2022 := params 5
abbrev ray2022 := rays 5
def bank2022 : Fin 2 → Cell := twoBank p2022 ray2022
theorem signs2022 : ∀ j, Signs p2022 (bank2022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2023 := params 6
abbrev ray2023 := rays 6
def bank2023 : Fin 2 → Cell := twoBank p2023 ray2023
theorem signs2023 : ∀ j, Signs p2023 (bank2023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2024 := params 7
abbrev ray2024 := rays 7
def bank2024 : Fin 2 → Cell := twoBank p2024 ray2024
theorem signs2024 : ∀ j, Signs p2024 (bank2024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2025 := params 8
abbrev ray2025 := rays 8
def bank2025 : Fin 2 → Cell := twoBank p2025 ray2025
theorem signs2025 : ∀ j, Signs p2025 (bank2025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2026 := params 9
abbrev ray2026 := rays 9
def bank2026 : Fin 2 → Cell := twoBank p2026 ray2026
theorem signs2026 : ∀ j, Signs p2026 (bank2026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2027 := params 10
abbrev ray2027 := rays 10
def bank2027 : Fin 2 → Cell := twoBank p2027 ray2027
theorem signs2027 : ∀ j, Signs p2027 (bank2027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2028 := params 11
abbrev ray2028 := rays 11
def bank2028 : Fin 2 → Cell := twoBank p2028 ray2028
theorem signs2028 : ∀ j, Signs p2028 (bank2028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2029 := params 12
abbrev ray2029 := rays 12
def bank2029 : Fin 2 → Cell := twoBank p2029 ray2029
theorem signs2029 : ∀ j, Signs p2029 (bank2029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2030 := params 13
abbrev ray2030 := rays 13
def bank2030 : Fin 2 → Cell := twoBank p2030 ray2030
theorem signs2030 : ∀ j, Signs p2030 (bank2030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2031 := params 14
abbrev ray2031 := rays 14
def bank2031 : Fin 2 → Cell := twoBank p2031 ray2031
theorem signs2031 : ∀ j, Signs p2031 (bank2031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2032 := params 15
abbrev ray2032 := rays 15
def bank2032 : Fin 2 → Cell := twoBank p2032 ray2032
theorem signs2032 : ∀ j, Signs p2032 (bank2032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2033 := params 16
abbrev ray2033 := rays 16
def bank2033 : Fin 2 → Cell := twoBank p2033 ray2033
theorem signs2033 : ∀ j, Signs p2033 (bank2033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2034 := params 17
abbrev ray2034 := rays 17
def bank2034 : Fin 2 → Cell := twoBank p2034 ray2034
theorem signs2034 : ∀ j, Signs p2034 (bank2034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2035 := params 18
abbrev ray2035 := rays 18
def bank2035 : Fin 2 → Cell := twoBank p2035 ray2035
theorem signs2035 : ∀ j, Signs p2035 (bank2035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2036 := params 19
abbrev ray2036 := rays 19
def bank2036 : Fin 2 → Cell := twoBank p2036 ray2036
theorem signs2036 : ∀ j, Signs p2036 (bank2036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2037 := params 20
abbrev ray2037 := rays 20
def bank2037 : Fin 2 → Cell := twoBank p2037 ray2037
theorem signs2037 : ∀ j, Signs p2037 (bank2037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2038 := params 21
abbrev ray2038 := rays 21
def bank2038 : Fin 2 → Cell := twoBank p2038 ray2038
theorem signs2038 : ∀ j, Signs p2038 (bank2038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2039 := params 22
abbrev ray2039 := rays 22
def bank2039 : Fin 2 → Cell := twoBank p2039 ray2039
theorem signs2039 : ∀ j, Signs p2039 (bank2039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2040 := params 23
abbrev ray2040 := rays 23
def bank2040 : Fin 2 → Cell := twoBank p2040 ray2040
theorem signs2040 : ∀ j, Signs p2040 (bank2040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2041 := params 24
abbrev ray2041 := rays 24
def bank2041 : Fin 2 → Cell := twoBank p2041 ray2041
theorem signs2041 : ∀ j, Signs p2041 (bank2041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2042 := params 25
abbrev ray2042 := rays 25
def bank2042 : Fin 2 → Cell := twoBank p2042 ray2042
theorem signs2042 : ∀ j, Signs p2042 (bank2042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2043 := params 26
abbrev ray2043 := rays 26
def bank2043 : Fin 2 → Cell := twoBank p2043 ray2043
theorem signs2043 : ∀ j, Signs p2043 (bank2043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2044 := params 27
abbrev ray2044 := rays 27
def bank2044 : Fin 2 → Cell := twoBank p2044 ray2044
theorem signs2044 : ∀ j, Signs p2044 (bank2044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2045 := params 28
abbrev ray2045 := rays 28
def bank2045 : Fin 2 → Cell := twoBank p2045 ray2045
theorem signs2045 : ∀ j, Signs p2045 (bank2045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2046 := params 29
abbrev ray2046 := rays 29
def bank2046 : Fin 2 → Cell := twoBank p2046 ray2046
theorem signs2046 : ∀ j, Signs p2046 (bank2046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2047 := params 30
abbrev ray2047 := rays 30
def bank2047 : Fin 2 → Cell := twoBank p2047 ray2047
theorem signs2047 : ∀ j, Signs p2047 (bank2047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2048 := params 31
abbrev ray2048 := rays 31
def bank2048 : Fin 2 → Cell := twoBank p2048 ray2048
theorem signs2048 : ∀ j, Signs p2048 (bank2048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02017_02048
