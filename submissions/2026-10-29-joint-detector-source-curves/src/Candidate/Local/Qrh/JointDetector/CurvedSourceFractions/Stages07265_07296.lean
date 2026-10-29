/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07265_07296
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98394665696967,98394357016997,98394048314903,98393739590687,98393430844349,98393122075889,98392813285309,98392504472609,98392195637790,98391886780853,98391577901799,98391269000628,98390960077341,98390651131939,98390342164423,98390033174793,98389724163050,98389415129195,98389106073229,98388796995152,98388487894966,98388178772671,98387869628267,98387560461756,98387251273138,98386942062414,98386632829585,98386323574651,98386014297614,98385704998474,98385395677232,98385086333888,98384776968444]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7264+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7265 := params 0
abbrev ray7265 := rays 0
def bank7265 : Fin 2 → Cell := twoBank p7265 ray7265
theorem signs7265 : ∀ j, Signs p7265 (bank7265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7266 := params 1
abbrev ray7266 := rays 1
def bank7266 : Fin 2 → Cell := twoBank p7266 ray7266
theorem signs7266 : ∀ j, Signs p7266 (bank7266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7267 := params 2
abbrev ray7267 := rays 2
def bank7267 : Fin 2 → Cell := twoBank p7267 ray7267
theorem signs7267 : ∀ j, Signs p7267 (bank7267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7268 := params 3
abbrev ray7268 := rays 3
def bank7268 : Fin 2 → Cell := twoBank p7268 ray7268
theorem signs7268 : ∀ j, Signs p7268 (bank7268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7269 := params 4
abbrev ray7269 := rays 4
def bank7269 : Fin 2 → Cell := twoBank p7269 ray7269
theorem signs7269 : ∀ j, Signs p7269 (bank7269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7270 := params 5
abbrev ray7270 := rays 5
def bank7270 : Fin 2 → Cell := twoBank p7270 ray7270
theorem signs7270 : ∀ j, Signs p7270 (bank7270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7271 := params 6
abbrev ray7271 := rays 6
def bank7271 : Fin 2 → Cell := twoBank p7271 ray7271
theorem signs7271 : ∀ j, Signs p7271 (bank7271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7272 := params 7
abbrev ray7272 := rays 7
def bank7272 : Fin 2 → Cell := twoBank p7272 ray7272
theorem signs7272 : ∀ j, Signs p7272 (bank7272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7273 := params 8
abbrev ray7273 := rays 8
def bank7273 : Fin 2 → Cell := twoBank p7273 ray7273
theorem signs7273 : ∀ j, Signs p7273 (bank7273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7274 := params 9
abbrev ray7274 := rays 9
def bank7274 : Fin 2 → Cell := twoBank p7274 ray7274
theorem signs7274 : ∀ j, Signs p7274 (bank7274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7275 := params 10
abbrev ray7275 := rays 10
def bank7275 : Fin 2 → Cell := twoBank p7275 ray7275
theorem signs7275 : ∀ j, Signs p7275 (bank7275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7276 := params 11
abbrev ray7276 := rays 11
def bank7276 : Fin 2 → Cell := twoBank p7276 ray7276
theorem signs7276 : ∀ j, Signs p7276 (bank7276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7277 := params 12
abbrev ray7277 := rays 12
def bank7277 : Fin 2 → Cell := twoBank p7277 ray7277
theorem signs7277 : ∀ j, Signs p7277 (bank7277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7278 := params 13
abbrev ray7278 := rays 13
def bank7278 : Fin 2 → Cell := twoBank p7278 ray7278
theorem signs7278 : ∀ j, Signs p7278 (bank7278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7279 := params 14
abbrev ray7279 := rays 14
def bank7279 : Fin 2 → Cell := twoBank p7279 ray7279
theorem signs7279 : ∀ j, Signs p7279 (bank7279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7280 := params 15
abbrev ray7280 := rays 15
def bank7280 : Fin 2 → Cell := twoBank p7280 ray7280
theorem signs7280 : ∀ j, Signs p7280 (bank7280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7281 := params 16
abbrev ray7281 := rays 16
def bank7281 : Fin 2 → Cell := twoBank p7281 ray7281
theorem signs7281 : ∀ j, Signs p7281 (bank7281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7282 := params 17
abbrev ray7282 := rays 17
def bank7282 : Fin 2 → Cell := twoBank p7282 ray7282
theorem signs7282 : ∀ j, Signs p7282 (bank7282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7283 := params 18
abbrev ray7283 := rays 18
def bank7283 : Fin 2 → Cell := twoBank p7283 ray7283
theorem signs7283 : ∀ j, Signs p7283 (bank7283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7284 := params 19
abbrev ray7284 := rays 19
def bank7284 : Fin 2 → Cell := twoBank p7284 ray7284
theorem signs7284 : ∀ j, Signs p7284 (bank7284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7285 := params 20
abbrev ray7285 := rays 20
def bank7285 : Fin 2 → Cell := twoBank p7285 ray7285
theorem signs7285 : ∀ j, Signs p7285 (bank7285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7286 := params 21
abbrev ray7286 := rays 21
def bank7286 : Fin 2 → Cell := twoBank p7286 ray7286
theorem signs7286 : ∀ j, Signs p7286 (bank7286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7287 := params 22
abbrev ray7287 := rays 22
def bank7287 : Fin 2 → Cell := twoBank p7287 ray7287
theorem signs7287 : ∀ j, Signs p7287 (bank7287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7288 := params 23
abbrev ray7288 := rays 23
def bank7288 : Fin 2 → Cell := twoBank p7288 ray7288
theorem signs7288 : ∀ j, Signs p7288 (bank7288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7289 := params 24
abbrev ray7289 := rays 24
def bank7289 : Fin 2 → Cell := twoBank p7289 ray7289
theorem signs7289 : ∀ j, Signs p7289 (bank7289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7290 := params 25
abbrev ray7290 := rays 25
def bank7290 : Fin 2 → Cell := twoBank p7290 ray7290
theorem signs7290 : ∀ j, Signs p7290 (bank7290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7291 := params 26
abbrev ray7291 := rays 26
def bank7291 : Fin 2 → Cell := twoBank p7291 ray7291
theorem signs7291 : ∀ j, Signs p7291 (bank7291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7292 := params 27
abbrev ray7292 := rays 27
def bank7292 : Fin 2 → Cell := twoBank p7292 ray7292
theorem signs7292 : ∀ j, Signs p7292 (bank7292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7293 := params 28
abbrev ray7293 := rays 28
def bank7293 : Fin 2 → Cell := twoBank p7293 ray7293
theorem signs7293 : ∀ j, Signs p7293 (bank7293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7294 := params 29
abbrev ray7294 := rays 29
def bank7294 : Fin 2 → Cell := twoBank p7294 ray7294
theorem signs7294 : ∀ j, Signs p7294 (bank7294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7295 := params 30
abbrev ray7295 := rays 30
def bank7295 : Fin 2 → Cell := twoBank p7295 ray7295
theorem signs7295 : ∀ j, Signs p7295 (bank7295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7296 := params 31
abbrev ray7296 := rays 31
def bank7296 : Fin 2 → Cell := twoBank p7296 ray7296
theorem signs7296 : ∀ j, Signs p7296 (bank7296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07265_07296
