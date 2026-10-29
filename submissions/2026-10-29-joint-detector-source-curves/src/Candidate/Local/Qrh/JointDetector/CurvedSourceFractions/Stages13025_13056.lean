/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13025_13056
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96270486525514,96270061230209,96269635918474,96269210590308,96268785245712,96268359884687,96267934507232,96267509113348,96267083703035,96266658276293,96266232833123,96265807373525,96265381897499,96264956405045,96264530896164,96264105370855,96263679829120,96263254270958,96262828696369,96262403105354,96261977497913,96261551874047,96261126233756,96260700577039,96260274903898,96259849214332,96259423508342,96258997785928,96258572047090,96258146291828,96257720520143,96257294732035,96256868927504]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13024+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13025 := params 0
abbrev ray13025 := rays 0
def bank13025 : Fin 1 → Cell := oneBank p13025 ray13025
theorem signs13025 : ∀ j, Signs p13025 (bank13025 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13026 := params 1
abbrev ray13026 := rays 1
def bank13026 : Fin 1 → Cell := oneBank p13026 ray13026
theorem signs13026 : ∀ j, Signs p13026 (bank13026 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13027 := params 2
abbrev ray13027 := rays 2
def bank13027 : Fin 1 → Cell := oneBank p13027 ray13027
theorem signs13027 : ∀ j, Signs p13027 (bank13027 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13028 := params 3
abbrev ray13028 := rays 3
def bank13028 : Fin 1 → Cell := oneBank p13028 ray13028
theorem signs13028 : ∀ j, Signs p13028 (bank13028 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13029 := params 4
abbrev ray13029 := rays 4
def bank13029 : Fin 1 → Cell := oneBank p13029 ray13029
theorem signs13029 : ∀ j, Signs p13029 (bank13029 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13030 := params 5
abbrev ray13030 := rays 5
def bank13030 : Fin 1 → Cell := oneBank p13030 ray13030
theorem signs13030 : ∀ j, Signs p13030 (bank13030 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13031 := params 6
abbrev ray13031 := rays 6
def bank13031 : Fin 1 → Cell := oneBank p13031 ray13031
theorem signs13031 : ∀ j, Signs p13031 (bank13031 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13032 := params 7
abbrev ray13032 := rays 7
def bank13032 : Fin 1 → Cell := oneBank p13032 ray13032
theorem signs13032 : ∀ j, Signs p13032 (bank13032 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13033 := params 8
abbrev ray13033 := rays 8
def bank13033 : Fin 1 → Cell := oneBank p13033 ray13033
theorem signs13033 : ∀ j, Signs p13033 (bank13033 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13034 := params 9
abbrev ray13034 := rays 9
def bank13034 : Fin 1 → Cell := oneBank p13034 ray13034
theorem signs13034 : ∀ j, Signs p13034 (bank13034 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13035 := params 10
abbrev ray13035 := rays 10
def bank13035 : Fin 1 → Cell := oneBank p13035 ray13035
theorem signs13035 : ∀ j, Signs p13035 (bank13035 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13036 := params 11
abbrev ray13036 := rays 11
def bank13036 : Fin 1 → Cell := oneBank p13036 ray13036
theorem signs13036 : ∀ j, Signs p13036 (bank13036 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13037 := params 12
abbrev ray13037 := rays 12
def bank13037 : Fin 1 → Cell := oneBank p13037 ray13037
theorem signs13037 : ∀ j, Signs p13037 (bank13037 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13038 := params 13
abbrev ray13038 := rays 13
def bank13038 : Fin 1 → Cell := oneBank p13038 ray13038
theorem signs13038 : ∀ j, Signs p13038 (bank13038 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13039 := params 14
abbrev ray13039 := rays 14
def bank13039 : Fin 1 → Cell := oneBank p13039 ray13039
theorem signs13039 : ∀ j, Signs p13039 (bank13039 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13040 := params 15
abbrev ray13040 := rays 15
def bank13040 : Fin 1 → Cell := oneBank p13040 ray13040
theorem signs13040 : ∀ j, Signs p13040 (bank13040 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13041 := params 16
abbrev ray13041 := rays 16
def bank13041 : Fin 1 → Cell := oneBank p13041 ray13041
theorem signs13041 : ∀ j, Signs p13041 (bank13041 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13042 := params 17
abbrev ray13042 := rays 17
def bank13042 : Fin 1 → Cell := oneBank p13042 ray13042
theorem signs13042 : ∀ j, Signs p13042 (bank13042 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13043 := params 18
abbrev ray13043 := rays 18
def bank13043 : Fin 1 → Cell := oneBank p13043 ray13043
theorem signs13043 : ∀ j, Signs p13043 (bank13043 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13044 := params 19
abbrev ray13044 := rays 19
def bank13044 : Fin 1 → Cell := oneBank p13044 ray13044
theorem signs13044 : ∀ j, Signs p13044 (bank13044 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13045 := params 20
abbrev ray13045 := rays 20
def bank13045 : Fin 1 → Cell := oneBank p13045 ray13045
theorem signs13045 : ∀ j, Signs p13045 (bank13045 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13046 := params 21
abbrev ray13046 := rays 21
def bank13046 : Fin 1 → Cell := oneBank p13046 ray13046
theorem signs13046 : ∀ j, Signs p13046 (bank13046 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13047 := params 22
abbrev ray13047 := rays 22
def bank13047 : Fin 1 → Cell := oneBank p13047 ray13047
theorem signs13047 : ∀ j, Signs p13047 (bank13047 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13048 := params 23
abbrev ray13048 := rays 23
def bank13048 : Fin 1 → Cell := oneBank p13048 ray13048
theorem signs13048 : ∀ j, Signs p13048 (bank13048 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13049 := params 24
abbrev ray13049 := rays 24
def bank13049 : Fin 1 → Cell := oneBank p13049 ray13049
theorem signs13049 : ∀ j, Signs p13049 (bank13049 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13050 := params 25
abbrev ray13050 := rays 25
def bank13050 : Fin 1 → Cell := oneBank p13050 ray13050
theorem signs13050 : ∀ j, Signs p13050 (bank13050 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13051 := params 26
abbrev ray13051 := rays 26
def bank13051 : Fin 1 → Cell := oneBank p13051 ray13051
theorem signs13051 : ∀ j, Signs p13051 (bank13051 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13052 := params 27
abbrev ray13052 := rays 27
def bank13052 : Fin 1 → Cell := oneBank p13052 ray13052
theorem signs13052 : ∀ j, Signs p13052 (bank13052 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13053 := params 28
abbrev ray13053 := rays 28
def bank13053 : Fin 1 → Cell := oneBank p13053 ray13053
theorem signs13053 : ∀ j, Signs p13053 (bank13053 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13054 := params 29
abbrev ray13054 := rays 29
def bank13054 : Fin 1 → Cell := oneBank p13054 ray13054
theorem signs13054 : ∀ j, Signs p13054 (bank13054 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13055 := params 30
abbrev ray13055 := rays 30
def bank13055 : Fin 1 → Cell := oneBank p13055 ray13055
theorem signs13055 : ∀ j, Signs p13055 (bank13055 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13056 := params 31
abbrev ray13056 := rays 31
def bank13056 : Fin 1 → Cell := oneBank p13056 ray13056
theorem signs13056 : ∀ j, Signs p13056 (bank13056 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13025_13056
