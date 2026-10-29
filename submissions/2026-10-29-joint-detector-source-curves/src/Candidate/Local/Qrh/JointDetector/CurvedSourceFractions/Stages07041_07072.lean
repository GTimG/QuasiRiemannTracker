/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07041_07072
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98463251040060,98462947335150,98462643607944,98462339858442,98462036086645,98461732292553,98461428476168,98461124637490,98460820776520,98460516893259,98460212987708,98459909059867,98459605109737,98459301137319,98458997142614,98458693125622,98458389086345,98458085024783,98457780940936,98457476834806,98457172706394,98456868555700,98456564382725,98456260187469,98455955969934,98455651730120,98455347468028,98455043183659,98454738877014,98454434548093,98454130196898,98453825823429,98453521427686]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7040+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7041 := params 0
abbrev ray7041 := rays 0
def bank7041 : Fin 2 → Cell := twoBank p7041 ray7041
theorem signs7041 : ∀ j, Signs p7041 (bank7041 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7042 := params 1
abbrev ray7042 := rays 1
def bank7042 : Fin 2 → Cell := twoBank p7042 ray7042
theorem signs7042 : ∀ j, Signs p7042 (bank7042 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7043 := params 2
abbrev ray7043 := rays 2
def bank7043 : Fin 2 → Cell := twoBank p7043 ray7043
theorem signs7043 : ∀ j, Signs p7043 (bank7043 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7044 := params 3
abbrev ray7044 := rays 3
def bank7044 : Fin 2 → Cell := twoBank p7044 ray7044
theorem signs7044 : ∀ j, Signs p7044 (bank7044 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7045 := params 4
abbrev ray7045 := rays 4
def bank7045 : Fin 2 → Cell := twoBank p7045 ray7045
theorem signs7045 : ∀ j, Signs p7045 (bank7045 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7046 := params 5
abbrev ray7046 := rays 5
def bank7046 : Fin 2 → Cell := twoBank p7046 ray7046
theorem signs7046 : ∀ j, Signs p7046 (bank7046 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7047 := params 6
abbrev ray7047 := rays 6
def bank7047 : Fin 2 → Cell := twoBank p7047 ray7047
theorem signs7047 : ∀ j, Signs p7047 (bank7047 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7048 := params 7
abbrev ray7048 := rays 7
def bank7048 : Fin 2 → Cell := twoBank p7048 ray7048
theorem signs7048 : ∀ j, Signs p7048 (bank7048 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7049 := params 8
abbrev ray7049 := rays 8
def bank7049 : Fin 2 → Cell := twoBank p7049 ray7049
theorem signs7049 : ∀ j, Signs p7049 (bank7049 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7050 := params 9
abbrev ray7050 := rays 9
def bank7050 : Fin 2 → Cell := twoBank p7050 ray7050
theorem signs7050 : ∀ j, Signs p7050 (bank7050 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7051 := params 10
abbrev ray7051 := rays 10
def bank7051 : Fin 2 → Cell := twoBank p7051 ray7051
theorem signs7051 : ∀ j, Signs p7051 (bank7051 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7052 := params 11
abbrev ray7052 := rays 11
def bank7052 : Fin 2 → Cell := twoBank p7052 ray7052
theorem signs7052 : ∀ j, Signs p7052 (bank7052 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7053 := params 12
abbrev ray7053 := rays 12
def bank7053 : Fin 2 → Cell := twoBank p7053 ray7053
theorem signs7053 : ∀ j, Signs p7053 (bank7053 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7054 := params 13
abbrev ray7054 := rays 13
def bank7054 : Fin 2 → Cell := twoBank p7054 ray7054
theorem signs7054 : ∀ j, Signs p7054 (bank7054 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7055 := params 14
abbrev ray7055 := rays 14
def bank7055 : Fin 2 → Cell := twoBank p7055 ray7055
theorem signs7055 : ∀ j, Signs p7055 (bank7055 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7056 := params 15
abbrev ray7056 := rays 15
def bank7056 : Fin 2 → Cell := twoBank p7056 ray7056
theorem signs7056 : ∀ j, Signs p7056 (bank7056 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7057 := params 16
abbrev ray7057 := rays 16
def bank7057 : Fin 2 → Cell := twoBank p7057 ray7057
theorem signs7057 : ∀ j, Signs p7057 (bank7057 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7058 := params 17
abbrev ray7058 := rays 17
def bank7058 : Fin 2 → Cell := twoBank p7058 ray7058
theorem signs7058 : ∀ j, Signs p7058 (bank7058 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7059 := params 18
abbrev ray7059 := rays 18
def bank7059 : Fin 2 → Cell := twoBank p7059 ray7059
theorem signs7059 : ∀ j, Signs p7059 (bank7059 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7060 := params 19
abbrev ray7060 := rays 19
def bank7060 : Fin 2 → Cell := twoBank p7060 ray7060
theorem signs7060 : ∀ j, Signs p7060 (bank7060 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7061 := params 20
abbrev ray7061 := rays 20
def bank7061 : Fin 2 → Cell := twoBank p7061 ray7061
theorem signs7061 : ∀ j, Signs p7061 (bank7061 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7062 := params 21
abbrev ray7062 := rays 21
def bank7062 : Fin 2 → Cell := twoBank p7062 ray7062
theorem signs7062 : ∀ j, Signs p7062 (bank7062 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7063 := params 22
abbrev ray7063 := rays 22
def bank7063 : Fin 2 → Cell := twoBank p7063 ray7063
theorem signs7063 : ∀ j, Signs p7063 (bank7063 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7064 := params 23
abbrev ray7064 := rays 23
def bank7064 : Fin 2 → Cell := twoBank p7064 ray7064
theorem signs7064 : ∀ j, Signs p7064 (bank7064 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7065 := params 24
abbrev ray7065 := rays 24
def bank7065 : Fin 2 → Cell := twoBank p7065 ray7065
theorem signs7065 : ∀ j, Signs p7065 (bank7065 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7066 := params 25
abbrev ray7066 := rays 25
def bank7066 : Fin 2 → Cell := twoBank p7066 ray7066
theorem signs7066 : ∀ j, Signs p7066 (bank7066 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7067 := params 26
abbrev ray7067 := rays 26
def bank7067 : Fin 2 → Cell := twoBank p7067 ray7067
theorem signs7067 : ∀ j, Signs p7067 (bank7067 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7068 := params 27
abbrev ray7068 := rays 27
def bank7068 : Fin 2 → Cell := twoBank p7068 ray7068
theorem signs7068 : ∀ j, Signs p7068 (bank7068 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7069 := params 28
abbrev ray7069 := rays 28
def bank7069 : Fin 2 → Cell := twoBank p7069 ray7069
theorem signs7069 : ∀ j, Signs p7069 (bank7069 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7070 := params 29
abbrev ray7070 := rays 29
def bank7070 : Fin 2 → Cell := twoBank p7070 ray7070
theorem signs7070 : ∀ j, Signs p7070 (bank7070 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7071 := params 30
abbrev ray7071 := rays 30
def bank7071 : Fin 2 → Cell := twoBank p7071 ray7071
theorem signs7071 : ∀ j, Signs p7071 (bank7071 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7072 := params 31
abbrev ray7072 := rays 31
def bank7072 : Fin 2 → Cell := twoBank p7072 ray7072
theorem signs7072 : ∀ j, Signs p7072 (bank7072 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07041_07072
