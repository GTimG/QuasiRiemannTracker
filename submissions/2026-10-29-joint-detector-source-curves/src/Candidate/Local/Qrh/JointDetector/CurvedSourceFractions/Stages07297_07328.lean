/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07297_07328
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98384776968444,98384467580900,98384158171257,98383848739515,98383539285676,98383229809740,98382920311708,98382610791580,98382301249358,98381991685042,98381682098633,98381372490132,98381062859539,98380753206855,98380443532081,98380133835218,98379824116267,98379514375228,98379204612102,98378894826890,98378585019592,98378275190209,98377965338743,98377655465193,98377345569561,98377035651847,98376725712052,98376415750177,98376105766223,98375795760190,98375485732079,98375175681891,98374865609627]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7296+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7297 := params 0
abbrev ray7297 := rays 0
def bank7297 : Fin 2 → Cell := twoBank p7297 ray7297
theorem signs7297 : ∀ j, Signs p7297 (bank7297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7298 := params 1
abbrev ray7298 := rays 1
def bank7298 : Fin 2 → Cell := twoBank p7298 ray7298
theorem signs7298 : ∀ j, Signs p7298 (bank7298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7299 := params 2
abbrev ray7299 := rays 2
def bank7299 : Fin 2 → Cell := twoBank p7299 ray7299
theorem signs7299 : ∀ j, Signs p7299 (bank7299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7300 := params 3
abbrev ray7300 := rays 3
def bank7300 : Fin 2 → Cell := twoBank p7300 ray7300
theorem signs7300 : ∀ j, Signs p7300 (bank7300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7301 := params 4
abbrev ray7301 := rays 4
def bank7301 : Fin 2 → Cell := twoBank p7301 ray7301
theorem signs7301 : ∀ j, Signs p7301 (bank7301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7302 := params 5
abbrev ray7302 := rays 5
def bank7302 : Fin 2 → Cell := twoBank p7302 ray7302
theorem signs7302 : ∀ j, Signs p7302 (bank7302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7303 := params 6
abbrev ray7303 := rays 6
def bank7303 : Fin 2 → Cell := twoBank p7303 ray7303
theorem signs7303 : ∀ j, Signs p7303 (bank7303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7304 := params 7
abbrev ray7304 := rays 7
def bank7304 : Fin 2 → Cell := twoBank p7304 ray7304
theorem signs7304 : ∀ j, Signs p7304 (bank7304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7305 := params 8
abbrev ray7305 := rays 8
def bank7305 : Fin 2 → Cell := twoBank p7305 ray7305
theorem signs7305 : ∀ j, Signs p7305 (bank7305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7306 := params 9
abbrev ray7306 := rays 9
def bank7306 : Fin 2 → Cell := twoBank p7306 ray7306
theorem signs7306 : ∀ j, Signs p7306 (bank7306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7307 := params 10
abbrev ray7307 := rays 10
def bank7307 : Fin 2 → Cell := twoBank p7307 ray7307
theorem signs7307 : ∀ j, Signs p7307 (bank7307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7308 := params 11
abbrev ray7308 := rays 11
def bank7308 : Fin 2 → Cell := twoBank p7308 ray7308
theorem signs7308 : ∀ j, Signs p7308 (bank7308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7309 := params 12
abbrev ray7309 := rays 12
def bank7309 : Fin 2 → Cell := twoBank p7309 ray7309
theorem signs7309 : ∀ j, Signs p7309 (bank7309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7310 := params 13
abbrev ray7310 := rays 13
def bank7310 : Fin 2 → Cell := twoBank p7310 ray7310
theorem signs7310 : ∀ j, Signs p7310 (bank7310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7311 := params 14
abbrev ray7311 := rays 14
def bank7311 : Fin 2 → Cell := twoBank p7311 ray7311
theorem signs7311 : ∀ j, Signs p7311 (bank7311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7312 := params 15
abbrev ray7312 := rays 15
def bank7312 : Fin 2 → Cell := twoBank p7312 ray7312
theorem signs7312 : ∀ j, Signs p7312 (bank7312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7313 := params 16
abbrev ray7313 := rays 16
def bank7313 : Fin 2 → Cell := twoBank p7313 ray7313
theorem signs7313 : ∀ j, Signs p7313 (bank7313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7314 := params 17
abbrev ray7314 := rays 17
def bank7314 : Fin 2 → Cell := twoBank p7314 ray7314
theorem signs7314 : ∀ j, Signs p7314 (bank7314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7315 := params 18
abbrev ray7315 := rays 18
def bank7315 : Fin 2 → Cell := twoBank p7315 ray7315
theorem signs7315 : ∀ j, Signs p7315 (bank7315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7316 := params 19
abbrev ray7316 := rays 19
def bank7316 : Fin 2 → Cell := twoBank p7316 ray7316
theorem signs7316 : ∀ j, Signs p7316 (bank7316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7317 := params 20
abbrev ray7317 := rays 20
def bank7317 : Fin 2 → Cell := twoBank p7317 ray7317
theorem signs7317 : ∀ j, Signs p7317 (bank7317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7318 := params 21
abbrev ray7318 := rays 21
def bank7318 : Fin 2 → Cell := twoBank p7318 ray7318
theorem signs7318 : ∀ j, Signs p7318 (bank7318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7319 := params 22
abbrev ray7319 := rays 22
def bank7319 : Fin 2 → Cell := twoBank p7319 ray7319
theorem signs7319 : ∀ j, Signs p7319 (bank7319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7320 := params 23
abbrev ray7320 := rays 23
def bank7320 : Fin 2 → Cell := twoBank p7320 ray7320
theorem signs7320 : ∀ j, Signs p7320 (bank7320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7321 := params 24
abbrev ray7321 := rays 24
def bank7321 : Fin 2 → Cell := twoBank p7321 ray7321
theorem signs7321 : ∀ j, Signs p7321 (bank7321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7322 := params 25
abbrev ray7322 := rays 25
def bank7322 : Fin 2 → Cell := twoBank p7322 ray7322
theorem signs7322 : ∀ j, Signs p7322 (bank7322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7323 := params 26
abbrev ray7323 := rays 26
def bank7323 : Fin 2 → Cell := twoBank p7323 ray7323
theorem signs7323 : ∀ j, Signs p7323 (bank7323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7324 := params 27
abbrev ray7324 := rays 27
def bank7324 : Fin 2 → Cell := twoBank p7324 ray7324
theorem signs7324 : ∀ j, Signs p7324 (bank7324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7325 := params 28
abbrev ray7325 := rays 28
def bank7325 : Fin 2 → Cell := twoBank p7325 ray7325
theorem signs7325 : ∀ j, Signs p7325 (bank7325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7326 := params 29
abbrev ray7326 := rays 29
def bank7326 : Fin 2 → Cell := twoBank p7326 ray7326
theorem signs7326 : ∀ j, Signs p7326 (bank7326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7327 := params 30
abbrev ray7327 := rays 30
def bank7327 : Fin 2 → Cell := twoBank p7327 ray7327
theorem signs7327 : ∀ j, Signs p7327 (bank7327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7328 := params 31
abbrev ray7328 := rays 31
def bank7328 : Fin 2 → Cell := twoBank p7328 ray7328
theorem signs7328 : ∀ j, Signs p7328 (bank7328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07297_07328
