/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages05025_05056
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99029050452753,99028793423635,99028536370439,99028279293166,99028022191816,99027765066391,99027507916891,99027250743318,99026993545673,99026736323956,99026479078169,99026221808312,99025964514387,99025707196394,99025449854335,99025192488210,99024935098021,99024677683768,99024420245453,99024162783076,99023905296639,99023647786142,99023390251587,99023132692974,99022875110305,99022617503580,99022359872800,99022102217967,99021844539081,99021586836144,99021329109156,99021071358118,99020813583032]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (5024+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p5025 := params 0
abbrev ray5025 := rays 0
def bank5025 : Fin 2 → Cell := twoBank p5025 ray5025
theorem signs5025 : ∀ j, Signs p5025 (bank5025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5026 := params 1
abbrev ray5026 := rays 1
def bank5026 : Fin 2 → Cell := twoBank p5026 ray5026
theorem signs5026 : ∀ j, Signs p5026 (bank5026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5027 := params 2
abbrev ray5027 := rays 2
def bank5027 : Fin 2 → Cell := twoBank p5027 ray5027
theorem signs5027 : ∀ j, Signs p5027 (bank5027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5028 := params 3
abbrev ray5028 := rays 3
def bank5028 : Fin 2 → Cell := twoBank p5028 ray5028
theorem signs5028 : ∀ j, Signs p5028 (bank5028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5029 := params 4
abbrev ray5029 := rays 4
def bank5029 : Fin 2 → Cell := twoBank p5029 ray5029
theorem signs5029 : ∀ j, Signs p5029 (bank5029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5030 := params 5
abbrev ray5030 := rays 5
def bank5030 : Fin 2 → Cell := twoBank p5030 ray5030
theorem signs5030 : ∀ j, Signs p5030 (bank5030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5031 := params 6
abbrev ray5031 := rays 6
def bank5031 : Fin 2 → Cell := twoBank p5031 ray5031
theorem signs5031 : ∀ j, Signs p5031 (bank5031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5032 := params 7
abbrev ray5032 := rays 7
def bank5032 : Fin 2 → Cell := twoBank p5032 ray5032
theorem signs5032 : ∀ j, Signs p5032 (bank5032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5033 := params 8
abbrev ray5033 := rays 8
def bank5033 : Fin 2 → Cell := twoBank p5033 ray5033
theorem signs5033 : ∀ j, Signs p5033 (bank5033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5034 := params 9
abbrev ray5034 := rays 9
def bank5034 : Fin 2 → Cell := twoBank p5034 ray5034
theorem signs5034 : ∀ j, Signs p5034 (bank5034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5035 := params 10
abbrev ray5035 := rays 10
def bank5035 : Fin 2 → Cell := twoBank p5035 ray5035
theorem signs5035 : ∀ j, Signs p5035 (bank5035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5036 := params 11
abbrev ray5036 := rays 11
def bank5036 : Fin 2 → Cell := twoBank p5036 ray5036
theorem signs5036 : ∀ j, Signs p5036 (bank5036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5037 := params 12
abbrev ray5037 := rays 12
def bank5037 : Fin 2 → Cell := twoBank p5037 ray5037
theorem signs5037 : ∀ j, Signs p5037 (bank5037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5038 := params 13
abbrev ray5038 := rays 13
def bank5038 : Fin 2 → Cell := twoBank p5038 ray5038
theorem signs5038 : ∀ j, Signs p5038 (bank5038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5039 := params 14
abbrev ray5039 := rays 14
def bank5039 : Fin 2 → Cell := twoBank p5039 ray5039
theorem signs5039 : ∀ j, Signs p5039 (bank5039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5040 := params 15
abbrev ray5040 := rays 15
def bank5040 : Fin 2 → Cell := twoBank p5040 ray5040
theorem signs5040 : ∀ j, Signs p5040 (bank5040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5041 := params 16
abbrev ray5041 := rays 16
def bank5041 : Fin 2 → Cell := twoBank p5041 ray5041
theorem signs5041 : ∀ j, Signs p5041 (bank5041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5042 := params 17
abbrev ray5042 := rays 17
def bank5042 : Fin 2 → Cell := twoBank p5042 ray5042
theorem signs5042 : ∀ j, Signs p5042 (bank5042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5043 := params 18
abbrev ray5043 := rays 18
def bank5043 : Fin 2 → Cell := twoBank p5043 ray5043
theorem signs5043 : ∀ j, Signs p5043 (bank5043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5044 := params 19
abbrev ray5044 := rays 19
def bank5044 : Fin 2 → Cell := twoBank p5044 ray5044
theorem signs5044 : ∀ j, Signs p5044 (bank5044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5045 := params 20
abbrev ray5045 := rays 20
def bank5045 : Fin 2 → Cell := twoBank p5045 ray5045
theorem signs5045 : ∀ j, Signs p5045 (bank5045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5046 := params 21
abbrev ray5046 := rays 21
def bank5046 : Fin 2 → Cell := twoBank p5046 ray5046
theorem signs5046 : ∀ j, Signs p5046 (bank5046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5047 := params 22
abbrev ray5047 := rays 22
def bank5047 : Fin 2 → Cell := twoBank p5047 ray5047
theorem signs5047 : ∀ j, Signs p5047 (bank5047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5048 := params 23
abbrev ray5048 := rays 23
def bank5048 : Fin 2 → Cell := twoBank p5048 ray5048
theorem signs5048 : ∀ j, Signs p5048 (bank5048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5049 := params 24
abbrev ray5049 := rays 24
def bank5049 : Fin 2 → Cell := twoBank p5049 ray5049
theorem signs5049 : ∀ j, Signs p5049 (bank5049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5050 := params 25
abbrev ray5050 := rays 25
def bank5050 : Fin 2 → Cell := twoBank p5050 ray5050
theorem signs5050 : ∀ j, Signs p5050 (bank5050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5051 := params 26
abbrev ray5051 := rays 26
def bank5051 : Fin 2 → Cell := twoBank p5051 ray5051
theorem signs5051 : ∀ j, Signs p5051 (bank5051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5052 := params 27
abbrev ray5052 := rays 27
def bank5052 : Fin 2 → Cell := twoBank p5052 ray5052
theorem signs5052 : ∀ j, Signs p5052 (bank5052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5053 := params 28
abbrev ray5053 := rays 28
def bank5053 : Fin 2 → Cell := twoBank p5053 ray5053
theorem signs5053 : ∀ j, Signs p5053 (bank5053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5054 := params 29
abbrev ray5054 := rays 29
def bank5054 : Fin 2 → Cell := twoBank p5054 ray5054
theorem signs5054 : ∀ j, Signs p5054 (bank5054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5055 := params 30
abbrev ray5055 := rays 30
def bank5055 : Fin 2 → Cell := twoBank p5055 ray5055
theorem signs5055 : ∀ j, Signs p5055 (bank5055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5056 := params 31
abbrev ray5056 := rays 31
def bank5056 : Fin 2 → Cell := twoBank p5056 ray5056
theorem signs5056 : ∀ j, Signs p5056 (bank5056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages05025_05056
