/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10017_10048
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97463880777813,97463513816396,97463146834651,97462779832578,97462412810179,97462045767453,97461678704402,97461311621026,97460944517325,97460577393300,97460210248952,97459843084281,97459475899287,97459108693971,97458741468334,97458374222376,97458006956098,97457639669501,97457272362585,97456905035350,97456537687797,97456170319927,97455802931740,97455435523237,97455068094418,97454700645284,97454333175835,97453965686072,97453598175995,97453230645605,97452863094903,97452495523889,97452127932564]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10016+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10017 := params 0
abbrev ray10017 := rays 0
def bank10017 : Fin 2 → Cell := twoBank p10017 ray10017
theorem signs10017 : ∀ j, Signs p10017 (bank10017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10018 := params 1
abbrev ray10018 := rays 1
def bank10018 : Fin 2 → Cell := twoBank p10018 ray10018
theorem signs10018 : ∀ j, Signs p10018 (bank10018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10019 := params 2
abbrev ray10019 := rays 2
def bank10019 : Fin 2 → Cell := twoBank p10019 ray10019
theorem signs10019 : ∀ j, Signs p10019 (bank10019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10020 := params 3
abbrev ray10020 := rays 3
def bank10020 : Fin 2 → Cell := twoBank p10020 ray10020
theorem signs10020 : ∀ j, Signs p10020 (bank10020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10021 := params 4
abbrev ray10021 := rays 4
def bank10021 : Fin 2 → Cell := twoBank p10021 ray10021
theorem signs10021 : ∀ j, Signs p10021 (bank10021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10022 := params 5
abbrev ray10022 := rays 5
def bank10022 : Fin 2 → Cell := twoBank p10022 ray10022
theorem signs10022 : ∀ j, Signs p10022 (bank10022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10023 := params 6
abbrev ray10023 := rays 6
def bank10023 : Fin 2 → Cell := twoBank p10023 ray10023
theorem signs10023 : ∀ j, Signs p10023 (bank10023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10024 := params 7
abbrev ray10024 := rays 7
def bank10024 : Fin 2 → Cell := twoBank p10024 ray10024
theorem signs10024 : ∀ j, Signs p10024 (bank10024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10025 := params 8
abbrev ray10025 := rays 8
def bank10025 : Fin 2 → Cell := twoBank p10025 ray10025
theorem signs10025 : ∀ j, Signs p10025 (bank10025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10026 := params 9
abbrev ray10026 := rays 9
def bank10026 : Fin 2 → Cell := twoBank p10026 ray10026
theorem signs10026 : ∀ j, Signs p10026 (bank10026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10027 := params 10
abbrev ray10027 := rays 10
def bank10027 : Fin 2 → Cell := twoBank p10027 ray10027
theorem signs10027 : ∀ j, Signs p10027 (bank10027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10028 := params 11
abbrev ray10028 := rays 11
def bank10028 : Fin 2 → Cell := twoBank p10028 ray10028
theorem signs10028 : ∀ j, Signs p10028 (bank10028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10029 := params 12
abbrev ray10029 := rays 12
def bank10029 : Fin 2 → Cell := twoBank p10029 ray10029
theorem signs10029 : ∀ j, Signs p10029 (bank10029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10030 := params 13
abbrev ray10030 := rays 13
def bank10030 : Fin 2 → Cell := twoBank p10030 ray10030
theorem signs10030 : ∀ j, Signs p10030 (bank10030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10031 := params 14
abbrev ray10031 := rays 14
def bank10031 : Fin 2 → Cell := twoBank p10031 ray10031
theorem signs10031 : ∀ j, Signs p10031 (bank10031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10032 := params 15
abbrev ray10032 := rays 15
def bank10032 : Fin 2 → Cell := twoBank p10032 ray10032
theorem signs10032 : ∀ j, Signs p10032 (bank10032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10033 := params 16
abbrev ray10033 := rays 16
def bank10033 : Fin 2 → Cell := twoBank p10033 ray10033
theorem signs10033 : ∀ j, Signs p10033 (bank10033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10034 := params 17
abbrev ray10034 := rays 17
def bank10034 : Fin 2 → Cell := twoBank p10034 ray10034
theorem signs10034 : ∀ j, Signs p10034 (bank10034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10035 := params 18
abbrev ray10035 := rays 18
def bank10035 : Fin 2 → Cell := twoBank p10035 ray10035
theorem signs10035 : ∀ j, Signs p10035 (bank10035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10036 := params 19
abbrev ray10036 := rays 19
def bank10036 : Fin 2 → Cell := twoBank p10036 ray10036
theorem signs10036 : ∀ j, Signs p10036 (bank10036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10037 := params 20
abbrev ray10037 := rays 20
def bank10037 : Fin 2 → Cell := twoBank p10037 ray10037
theorem signs10037 : ∀ j, Signs p10037 (bank10037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10038 := params 21
abbrev ray10038 := rays 21
def bank10038 : Fin 2 → Cell := twoBank p10038 ray10038
theorem signs10038 : ∀ j, Signs p10038 (bank10038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10039 := params 22
abbrev ray10039 := rays 22
def bank10039 : Fin 2 → Cell := twoBank p10039 ray10039
theorem signs10039 : ∀ j, Signs p10039 (bank10039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10040 := params 23
abbrev ray10040 := rays 23
def bank10040 : Fin 2 → Cell := twoBank p10040 ray10040
theorem signs10040 : ∀ j, Signs p10040 (bank10040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10041 := params 24
abbrev ray10041 := rays 24
def bank10041 : Fin 2 → Cell := twoBank p10041 ray10041
theorem signs10041 : ∀ j, Signs p10041 (bank10041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10042 := params 25
abbrev ray10042 := rays 25
def bank10042 : Fin 2 → Cell := twoBank p10042 ray10042
theorem signs10042 : ∀ j, Signs p10042 (bank10042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10043 := params 26
abbrev ray10043 := rays 26
def bank10043 : Fin 2 → Cell := twoBank p10043 ray10043
theorem signs10043 : ∀ j, Signs p10043 (bank10043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10044 := params 27
abbrev ray10044 := rays 27
def bank10044 : Fin 2 → Cell := twoBank p10044 ray10044
theorem signs10044 : ∀ j, Signs p10044 (bank10044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10045 := params 28
abbrev ray10045 := rays 28
def bank10045 : Fin 2 → Cell := twoBank p10045 ray10045
theorem signs10045 : ∀ j, Signs p10045 (bank10045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10046 := params 29
abbrev ray10046 := rays 29
def bank10046 : Fin 2 → Cell := twoBank p10046 ray10046
theorem signs10046 : ∀ j, Signs p10046 (bank10046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10047 := params 30
abbrev ray10047 := rays 30
def bank10047 : Fin 2 → Cell := twoBank p10047 ray10047
theorem signs10047 : ∀ j, Signs p10047 (bank10047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10048 := params 31
abbrev ray10048 := rays 31
def bank10048 : Fin 2 → Cell := twoBank p10048 ray10048
theorem signs10048 : ∀ j, Signs p10048 (bank10048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10017_10048
