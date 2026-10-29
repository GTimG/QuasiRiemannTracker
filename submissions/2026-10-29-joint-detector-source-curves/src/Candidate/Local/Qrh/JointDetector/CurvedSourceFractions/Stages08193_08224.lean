/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08193_08224
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98098793369616,98098464475711,98098135560353,98097806623544,98097477665284,98097148685573,98096819684413,98096490661804,98096161617746,98095832552241,98095503465289,98095174356891,98094845227047,98094516075758,98094186903025,98093857708849,98093528493230,98093199256169,98092869997666,98092540717723,98092211416339,98091882093516,98091552749254,98091223383554,98090893996417,98090564587843,98090235157833,98089905706388,98089576233508,98089246739195,98088917223448,98088587686269,98088258127658]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8192+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8193 := params 0
abbrev ray8193 := rays 0
def bank8193 : Fin 2 → Cell := twoBank p8193 ray8193
theorem signs8193 : ∀ j, Signs p8193 (bank8193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8194 := params 1
abbrev ray8194 := rays 1
def bank8194 : Fin 2 → Cell := twoBank p8194 ray8194
theorem signs8194 : ∀ j, Signs p8194 (bank8194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8195 := params 2
abbrev ray8195 := rays 2
def bank8195 : Fin 2 → Cell := twoBank p8195 ray8195
theorem signs8195 : ∀ j, Signs p8195 (bank8195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8196 := params 3
abbrev ray8196 := rays 3
def bank8196 : Fin 2 → Cell := twoBank p8196 ray8196
theorem signs8196 : ∀ j, Signs p8196 (bank8196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8197 := params 4
abbrev ray8197 := rays 4
def bank8197 : Fin 2 → Cell := twoBank p8197 ray8197
theorem signs8197 : ∀ j, Signs p8197 (bank8197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8198 := params 5
abbrev ray8198 := rays 5
def bank8198 : Fin 2 → Cell := twoBank p8198 ray8198
theorem signs8198 : ∀ j, Signs p8198 (bank8198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8199 := params 6
abbrev ray8199 := rays 6
def bank8199 : Fin 2 → Cell := twoBank p8199 ray8199
theorem signs8199 : ∀ j, Signs p8199 (bank8199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8200 := params 7
abbrev ray8200 := rays 7
def bank8200 : Fin 2 → Cell := twoBank p8200 ray8200
theorem signs8200 : ∀ j, Signs p8200 (bank8200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8201 := params 8
abbrev ray8201 := rays 8
def bank8201 : Fin 2 → Cell := twoBank p8201 ray8201
theorem signs8201 : ∀ j, Signs p8201 (bank8201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8202 := params 9
abbrev ray8202 := rays 9
def bank8202 : Fin 2 → Cell := twoBank p8202 ray8202
theorem signs8202 : ∀ j, Signs p8202 (bank8202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8203 := params 10
abbrev ray8203 := rays 10
def bank8203 : Fin 2 → Cell := twoBank p8203 ray8203
theorem signs8203 : ∀ j, Signs p8203 (bank8203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8204 := params 11
abbrev ray8204 := rays 11
def bank8204 : Fin 2 → Cell := twoBank p8204 ray8204
theorem signs8204 : ∀ j, Signs p8204 (bank8204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8205 := params 12
abbrev ray8205 := rays 12
def bank8205 : Fin 2 → Cell := twoBank p8205 ray8205
theorem signs8205 : ∀ j, Signs p8205 (bank8205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8206 := params 13
abbrev ray8206 := rays 13
def bank8206 : Fin 2 → Cell := twoBank p8206 ray8206
theorem signs8206 : ∀ j, Signs p8206 (bank8206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8207 := params 14
abbrev ray8207 := rays 14
def bank8207 : Fin 2 → Cell := twoBank p8207 ray8207
theorem signs8207 : ∀ j, Signs p8207 (bank8207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8208 := params 15
abbrev ray8208 := rays 15
def bank8208 : Fin 2 → Cell := twoBank p8208 ray8208
theorem signs8208 : ∀ j, Signs p8208 (bank8208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8209 := params 16
abbrev ray8209 := rays 16
def bank8209 : Fin 2 → Cell := twoBank p8209 ray8209
theorem signs8209 : ∀ j, Signs p8209 (bank8209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8210 := params 17
abbrev ray8210 := rays 17
def bank8210 : Fin 2 → Cell := twoBank p8210 ray8210
theorem signs8210 : ∀ j, Signs p8210 (bank8210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8211 := params 18
abbrev ray8211 := rays 18
def bank8211 : Fin 2 → Cell := twoBank p8211 ray8211
theorem signs8211 : ∀ j, Signs p8211 (bank8211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8212 := params 19
abbrev ray8212 := rays 19
def bank8212 : Fin 2 → Cell := twoBank p8212 ray8212
theorem signs8212 : ∀ j, Signs p8212 (bank8212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8213 := params 20
abbrev ray8213 := rays 20
def bank8213 : Fin 2 → Cell := twoBank p8213 ray8213
theorem signs8213 : ∀ j, Signs p8213 (bank8213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8214 := params 21
abbrev ray8214 := rays 21
def bank8214 : Fin 2 → Cell := twoBank p8214 ray8214
theorem signs8214 : ∀ j, Signs p8214 (bank8214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8215 := params 22
abbrev ray8215 := rays 22
def bank8215 : Fin 2 → Cell := twoBank p8215 ray8215
theorem signs8215 : ∀ j, Signs p8215 (bank8215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8216 := params 23
abbrev ray8216 := rays 23
def bank8216 : Fin 2 → Cell := twoBank p8216 ray8216
theorem signs8216 : ∀ j, Signs p8216 (bank8216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8217 := params 24
abbrev ray8217 := rays 24
def bank8217 : Fin 2 → Cell := twoBank p8217 ray8217
theorem signs8217 : ∀ j, Signs p8217 (bank8217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8218 := params 25
abbrev ray8218 := rays 25
def bank8218 : Fin 2 → Cell := twoBank p8218 ray8218
theorem signs8218 : ∀ j, Signs p8218 (bank8218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8219 := params 26
abbrev ray8219 := rays 26
def bank8219 : Fin 2 → Cell := twoBank p8219 ray8219
theorem signs8219 : ∀ j, Signs p8219 (bank8219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8220 := params 27
abbrev ray8220 := rays 27
def bank8220 : Fin 2 → Cell := twoBank p8220 ray8220
theorem signs8220 : ∀ j, Signs p8220 (bank8220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8221 := params 28
abbrev ray8221 := rays 28
def bank8221 : Fin 2 → Cell := twoBank p8221 ray8221
theorem signs8221 : ∀ j, Signs p8221 (bank8221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8222 := params 29
abbrev ray8222 := rays 29
def bank8222 : Fin 2 → Cell := twoBank p8222 ray8222
theorem signs8222 : ∀ j, Signs p8222 (bank8222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8223 := params 30
abbrev ray8223 := rays 30
def bank8223 : Fin 2 → Cell := twoBank p8223 ray8223
theorem signs8223 : ∀ j, Signs p8223 (bank8223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8224 := params 31
abbrev ray8224 := rays 31
def bank8224 : Fin 2 → Cell := twoBank p8224 ray8224
theorem signs8224 : ∀ j, Signs p8224 (bank8224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08193_08224
