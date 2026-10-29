/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages09025_09056
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97817801572331,97817455059286,97817108525332,97816761970469,97816415394698,97816068798019,97815722180433,97815375541941,97815028882543,97814682202240,97814335501033,97813988778922,97813642035907,97813295271990,97812948487171,97812601681450,97812254854829,97811908007308,97811561138887,97811214249567,97810867339349,97810520408233,97810173456220,97809826483311,97809479489506,97809132474806,97808785439211,97808438382722,97808091305340,97807744207065,97807397087898,97807049947839,97806702786890]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (9024+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p9025 := params 0
abbrev ray9025 := rays 0
def bank9025 : Fin 2 → Cell := twoBank p9025 ray9025
theorem signs9025 : ∀ j, Signs p9025 (bank9025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9026 := params 1
abbrev ray9026 := rays 1
def bank9026 : Fin 2 → Cell := twoBank p9026 ray9026
theorem signs9026 : ∀ j, Signs p9026 (bank9026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9027 := params 2
abbrev ray9027 := rays 2
def bank9027 : Fin 2 → Cell := twoBank p9027 ray9027
theorem signs9027 : ∀ j, Signs p9027 (bank9027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9028 := params 3
abbrev ray9028 := rays 3
def bank9028 : Fin 2 → Cell := twoBank p9028 ray9028
theorem signs9028 : ∀ j, Signs p9028 (bank9028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9029 := params 4
abbrev ray9029 := rays 4
def bank9029 : Fin 2 → Cell := twoBank p9029 ray9029
theorem signs9029 : ∀ j, Signs p9029 (bank9029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9030 := params 5
abbrev ray9030 := rays 5
def bank9030 : Fin 2 → Cell := twoBank p9030 ray9030
theorem signs9030 : ∀ j, Signs p9030 (bank9030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9031 := params 6
abbrev ray9031 := rays 6
def bank9031 : Fin 2 → Cell := twoBank p9031 ray9031
theorem signs9031 : ∀ j, Signs p9031 (bank9031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9032 := params 7
abbrev ray9032 := rays 7
def bank9032 : Fin 2 → Cell := twoBank p9032 ray9032
theorem signs9032 : ∀ j, Signs p9032 (bank9032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9033 := params 8
abbrev ray9033 := rays 8
def bank9033 : Fin 2 → Cell := twoBank p9033 ray9033
theorem signs9033 : ∀ j, Signs p9033 (bank9033 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9034 := params 9
abbrev ray9034 := rays 9
def bank9034 : Fin 2 → Cell := twoBank p9034 ray9034
theorem signs9034 : ∀ j, Signs p9034 (bank9034 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9035 := params 10
abbrev ray9035 := rays 10
def bank9035 : Fin 2 → Cell := twoBank p9035 ray9035
theorem signs9035 : ∀ j, Signs p9035 (bank9035 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9036 := params 11
abbrev ray9036 := rays 11
def bank9036 : Fin 2 → Cell := twoBank p9036 ray9036
theorem signs9036 : ∀ j, Signs p9036 (bank9036 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9037 := params 12
abbrev ray9037 := rays 12
def bank9037 : Fin 2 → Cell := twoBank p9037 ray9037
theorem signs9037 : ∀ j, Signs p9037 (bank9037 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9038 := params 13
abbrev ray9038 := rays 13
def bank9038 : Fin 2 → Cell := twoBank p9038 ray9038
theorem signs9038 : ∀ j, Signs p9038 (bank9038 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9039 := params 14
abbrev ray9039 := rays 14
def bank9039 : Fin 2 → Cell := twoBank p9039 ray9039
theorem signs9039 : ∀ j, Signs p9039 (bank9039 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9040 := params 15
abbrev ray9040 := rays 15
def bank9040 : Fin 2 → Cell := twoBank p9040 ray9040
theorem signs9040 : ∀ j, Signs p9040 (bank9040 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9041 := params 16
abbrev ray9041 := rays 16
def bank9041 : Fin 2 → Cell := twoBank p9041 ray9041
theorem signs9041 : ∀ j, Signs p9041 (bank9041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9042 := params 17
abbrev ray9042 := rays 17
def bank9042 : Fin 2 → Cell := twoBank p9042 ray9042
theorem signs9042 : ∀ j, Signs p9042 (bank9042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9043 := params 18
abbrev ray9043 := rays 18
def bank9043 : Fin 2 → Cell := twoBank p9043 ray9043
theorem signs9043 : ∀ j, Signs p9043 (bank9043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9044 := params 19
abbrev ray9044 := rays 19
def bank9044 : Fin 2 → Cell := twoBank p9044 ray9044
theorem signs9044 : ∀ j, Signs p9044 (bank9044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9045 := params 20
abbrev ray9045 := rays 20
def bank9045 : Fin 2 → Cell := twoBank p9045 ray9045
theorem signs9045 : ∀ j, Signs p9045 (bank9045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9046 := params 21
abbrev ray9046 := rays 21
def bank9046 : Fin 2 → Cell := twoBank p9046 ray9046
theorem signs9046 : ∀ j, Signs p9046 (bank9046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9047 := params 22
abbrev ray9047 := rays 22
def bank9047 : Fin 2 → Cell := twoBank p9047 ray9047
theorem signs9047 : ∀ j, Signs p9047 (bank9047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9048 := params 23
abbrev ray9048 := rays 23
def bank9048 : Fin 2 → Cell := twoBank p9048 ray9048
theorem signs9048 : ∀ j, Signs p9048 (bank9048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9049 := params 24
abbrev ray9049 := rays 24
def bank9049 : Fin 2 → Cell := twoBank p9049 ray9049
theorem signs9049 : ∀ j, Signs p9049 (bank9049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9050 := params 25
abbrev ray9050 := rays 25
def bank9050 : Fin 2 → Cell := twoBank p9050 ray9050
theorem signs9050 : ∀ j, Signs p9050 (bank9050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9051 := params 26
abbrev ray9051 := rays 26
def bank9051 : Fin 2 → Cell := twoBank p9051 ray9051
theorem signs9051 : ∀ j, Signs p9051 (bank9051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9052 := params 27
abbrev ray9052 := rays 27
def bank9052 : Fin 2 → Cell := twoBank p9052 ray9052
theorem signs9052 : ∀ j, Signs p9052 (bank9052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9053 := params 28
abbrev ray9053 := rays 28
def bank9053 : Fin 2 → Cell := twoBank p9053 ray9053
theorem signs9053 : ∀ j, Signs p9053 (bank9053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9054 := params 29
abbrev ray9054 := rays 29
def bank9054 : Fin 2 → Cell := twoBank p9054 ray9054
theorem signs9054 : ∀ j, Signs p9054 (bank9054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9055 := params 30
abbrev ray9055 := rays 30
def bank9055 : Fin 2 → Cell := twoBank p9055 ray9055
theorem signs9055 : ∀ j, Signs p9055 (bank9055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9056 := params 31
abbrev ray9056 := rays 31
def bank9056 : Fin 2 → Cell := twoBank p9056 ray9056
theorem signs9056 : ∀ j, Signs p9056 (bank9056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages09025_09056
