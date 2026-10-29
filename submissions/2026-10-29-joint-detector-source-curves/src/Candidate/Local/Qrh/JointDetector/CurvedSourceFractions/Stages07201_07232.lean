/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07201_07232
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98414375163202,98414067900727,98413760616079,98413453309260,98413145980270,98412838629109,98412531255779,98412223860280,98411916442613,98411609002779,98411301540779,98410994056613,98410686550282,98410379021787,98410071471129,98409763898308,98409456303326,98409148686183,98408841046880,98408533385417,98408225701795,98407917996015,98407610268078,98407302517985,98406994745736,98406686951332,98406379134774,98406071296063,98405763435199,98405455552184,98405147647018,98404839719701,98404531770235]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7200+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7201 := params 0
abbrev ray7201 := rays 0
def bank7201 : Fin 2 → Cell := twoBank p7201 ray7201
theorem signs7201 : ∀ j, Signs p7201 (bank7201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7202 := params 1
abbrev ray7202 := rays 1
def bank7202 : Fin 2 → Cell := twoBank p7202 ray7202
theorem signs7202 : ∀ j, Signs p7202 (bank7202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7203 := params 2
abbrev ray7203 := rays 2
def bank7203 : Fin 2 → Cell := twoBank p7203 ray7203
theorem signs7203 : ∀ j, Signs p7203 (bank7203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7204 := params 3
abbrev ray7204 := rays 3
def bank7204 : Fin 2 → Cell := twoBank p7204 ray7204
theorem signs7204 : ∀ j, Signs p7204 (bank7204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7205 := params 4
abbrev ray7205 := rays 4
def bank7205 : Fin 2 → Cell := twoBank p7205 ray7205
theorem signs7205 : ∀ j, Signs p7205 (bank7205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7206 := params 5
abbrev ray7206 := rays 5
def bank7206 : Fin 2 → Cell := twoBank p7206 ray7206
theorem signs7206 : ∀ j, Signs p7206 (bank7206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7207 := params 6
abbrev ray7207 := rays 6
def bank7207 : Fin 2 → Cell := twoBank p7207 ray7207
theorem signs7207 : ∀ j, Signs p7207 (bank7207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7208 := params 7
abbrev ray7208 := rays 7
def bank7208 : Fin 2 → Cell := twoBank p7208 ray7208
theorem signs7208 : ∀ j, Signs p7208 (bank7208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7209 := params 8
abbrev ray7209 := rays 8
def bank7209 : Fin 2 → Cell := twoBank p7209 ray7209
theorem signs7209 : ∀ j, Signs p7209 (bank7209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7210 := params 9
abbrev ray7210 := rays 9
def bank7210 : Fin 2 → Cell := twoBank p7210 ray7210
theorem signs7210 : ∀ j, Signs p7210 (bank7210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7211 := params 10
abbrev ray7211 := rays 10
def bank7211 : Fin 2 → Cell := twoBank p7211 ray7211
theorem signs7211 : ∀ j, Signs p7211 (bank7211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7212 := params 11
abbrev ray7212 := rays 11
def bank7212 : Fin 2 → Cell := twoBank p7212 ray7212
theorem signs7212 : ∀ j, Signs p7212 (bank7212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7213 := params 12
abbrev ray7213 := rays 12
def bank7213 : Fin 2 → Cell := twoBank p7213 ray7213
theorem signs7213 : ∀ j, Signs p7213 (bank7213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7214 := params 13
abbrev ray7214 := rays 13
def bank7214 : Fin 2 → Cell := twoBank p7214 ray7214
theorem signs7214 : ∀ j, Signs p7214 (bank7214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7215 := params 14
abbrev ray7215 := rays 14
def bank7215 : Fin 2 → Cell := twoBank p7215 ray7215
theorem signs7215 : ∀ j, Signs p7215 (bank7215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7216 := params 15
abbrev ray7216 := rays 15
def bank7216 : Fin 2 → Cell := twoBank p7216 ray7216
theorem signs7216 : ∀ j, Signs p7216 (bank7216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7217 := params 16
abbrev ray7217 := rays 16
def bank7217 : Fin 2 → Cell := twoBank p7217 ray7217
theorem signs7217 : ∀ j, Signs p7217 (bank7217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7218 := params 17
abbrev ray7218 := rays 17
def bank7218 : Fin 2 → Cell := twoBank p7218 ray7218
theorem signs7218 : ∀ j, Signs p7218 (bank7218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7219 := params 18
abbrev ray7219 := rays 18
def bank7219 : Fin 2 → Cell := twoBank p7219 ray7219
theorem signs7219 : ∀ j, Signs p7219 (bank7219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7220 := params 19
abbrev ray7220 := rays 19
def bank7220 : Fin 2 → Cell := twoBank p7220 ray7220
theorem signs7220 : ∀ j, Signs p7220 (bank7220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7221 := params 20
abbrev ray7221 := rays 20
def bank7221 : Fin 2 → Cell := twoBank p7221 ray7221
theorem signs7221 : ∀ j, Signs p7221 (bank7221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7222 := params 21
abbrev ray7222 := rays 21
def bank7222 : Fin 2 → Cell := twoBank p7222 ray7222
theorem signs7222 : ∀ j, Signs p7222 (bank7222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7223 := params 22
abbrev ray7223 := rays 22
def bank7223 : Fin 2 → Cell := twoBank p7223 ray7223
theorem signs7223 : ∀ j, Signs p7223 (bank7223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7224 := params 23
abbrev ray7224 := rays 23
def bank7224 : Fin 2 → Cell := twoBank p7224 ray7224
theorem signs7224 : ∀ j, Signs p7224 (bank7224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7225 := params 24
abbrev ray7225 := rays 24
def bank7225 : Fin 2 → Cell := twoBank p7225 ray7225
theorem signs7225 : ∀ j, Signs p7225 (bank7225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7226 := params 25
abbrev ray7226 := rays 25
def bank7226 : Fin 2 → Cell := twoBank p7226 ray7226
theorem signs7226 : ∀ j, Signs p7226 (bank7226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7227 := params 26
abbrev ray7227 := rays 26
def bank7227 : Fin 2 → Cell := twoBank p7227 ray7227
theorem signs7227 : ∀ j, Signs p7227 (bank7227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7228 := params 27
abbrev ray7228 := rays 27
def bank7228 : Fin 2 → Cell := twoBank p7228 ray7228
theorem signs7228 : ∀ j, Signs p7228 (bank7228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7229 := params 28
abbrev ray7229 := rays 28
def bank7229 : Fin 2 → Cell := twoBank p7229 ray7229
theorem signs7229 : ∀ j, Signs p7229 (bank7229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7230 := params 29
abbrev ray7230 := rays 29
def bank7230 : Fin 2 → Cell := twoBank p7230 ray7230
theorem signs7230 : ∀ j, Signs p7230 (bank7230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7231 := params 30
abbrev ray7231 := rays 30
def bank7231 : Fin 2 → Cell := twoBank p7231 ray7231
theorem signs7231 : ∀ j, Signs p7231 (bank7231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7232 := params 31
abbrev ray7232 := rays 31
def bank7232 : Fin 2 → Cell := twoBank p7232 ray7232
theorem signs7232 : ∀ j, Signs p7232 (bank7232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07201_07232
