/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15265_15296
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95277028125325,95276566534051,95276104926738,95275643303386,95275181663995,95274720008566,95274258337098,95273796649591,95273334946046,95272873226462,95272411490840,95271949739179,95271487971480,95271026187743,95270564387968,95270102572155,95269640740304,95269178892416,95268717028490,95268255148526,95267793252525,95267331340486,95266869412410,95266407468297,95265945508147,95265483531960,95265021539736,95264559531475,95264097507177,95263635466842,95263173410471,95262711338063,95262249249619]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15264+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15265 := params 0
abbrev ray15265 := rays 0
def bank15265 : Fin 1 → Cell := oneBank p15265 ray15265
theorem signs15265 : ∀ j, Signs p15265 (bank15265 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15266 := params 1
abbrev ray15266 := rays 1
def bank15266 : Fin 1 → Cell := oneBank p15266 ray15266
theorem signs15266 : ∀ j, Signs p15266 (bank15266 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15267 := params 2
abbrev ray15267 := rays 2
def bank15267 : Fin 1 → Cell := oneBank p15267 ray15267
theorem signs15267 : ∀ j, Signs p15267 (bank15267 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15268 := params 3
abbrev ray15268 := rays 3
def bank15268 : Fin 1 → Cell := oneBank p15268 ray15268
theorem signs15268 : ∀ j, Signs p15268 (bank15268 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15269 := params 4
abbrev ray15269 := rays 4
def bank15269 : Fin 1 → Cell := oneBank p15269 ray15269
theorem signs15269 : ∀ j, Signs p15269 (bank15269 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15270 := params 5
abbrev ray15270 := rays 5
def bank15270 : Fin 1 → Cell := oneBank p15270 ray15270
theorem signs15270 : ∀ j, Signs p15270 (bank15270 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15271 := params 6
abbrev ray15271 := rays 6
def bank15271 : Fin 1 → Cell := oneBank p15271 ray15271
theorem signs15271 : ∀ j, Signs p15271 (bank15271 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15272 := params 7
abbrev ray15272 := rays 7
def bank15272 : Fin 1 → Cell := oneBank p15272 ray15272
theorem signs15272 : ∀ j, Signs p15272 (bank15272 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15273 := params 8
abbrev ray15273 := rays 8
def bank15273 : Fin 1 → Cell := oneBank p15273 ray15273
theorem signs15273 : ∀ j, Signs p15273 (bank15273 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15274 := params 9
abbrev ray15274 := rays 9
def bank15274 : Fin 1 → Cell := oneBank p15274 ray15274
theorem signs15274 : ∀ j, Signs p15274 (bank15274 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15275 := params 10
abbrev ray15275 := rays 10
def bank15275 : Fin 1 → Cell := oneBank p15275 ray15275
theorem signs15275 : ∀ j, Signs p15275 (bank15275 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15276 := params 11
abbrev ray15276 := rays 11
def bank15276 : Fin 1 → Cell := oneBank p15276 ray15276
theorem signs15276 : ∀ j, Signs p15276 (bank15276 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15277 := params 12
abbrev ray15277 := rays 12
def bank15277 : Fin 1 → Cell := oneBank p15277 ray15277
theorem signs15277 : ∀ j, Signs p15277 (bank15277 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15278 := params 13
abbrev ray15278 := rays 13
def bank15278 : Fin 1 → Cell := oneBank p15278 ray15278
theorem signs15278 : ∀ j, Signs p15278 (bank15278 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15279 := params 14
abbrev ray15279 := rays 14
def bank15279 : Fin 1 → Cell := oneBank p15279 ray15279
theorem signs15279 : ∀ j, Signs p15279 (bank15279 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15280 := params 15
abbrev ray15280 := rays 15
def bank15280 : Fin 1 → Cell := oneBank p15280 ray15280
theorem signs15280 : ∀ j, Signs p15280 (bank15280 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15281 := params 16
abbrev ray15281 := rays 16
def bank15281 : Fin 1 → Cell := oneBank p15281 ray15281
theorem signs15281 : ∀ j, Signs p15281 (bank15281 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15282 := params 17
abbrev ray15282 := rays 17
def bank15282 : Fin 1 → Cell := oneBank p15282 ray15282
theorem signs15282 : ∀ j, Signs p15282 (bank15282 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15283 := params 18
abbrev ray15283 := rays 18
def bank15283 : Fin 1 → Cell := oneBank p15283 ray15283
theorem signs15283 : ∀ j, Signs p15283 (bank15283 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15284 := params 19
abbrev ray15284 := rays 19
def bank15284 : Fin 1 → Cell := oneBank p15284 ray15284
theorem signs15284 : ∀ j, Signs p15284 (bank15284 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15285 := params 20
abbrev ray15285 := rays 20
def bank15285 : Fin 1 → Cell := oneBank p15285 ray15285
theorem signs15285 : ∀ j, Signs p15285 (bank15285 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15286 := params 21
abbrev ray15286 := rays 21
def bank15286 : Fin 1 → Cell := oneBank p15286 ray15286
theorem signs15286 : ∀ j, Signs p15286 (bank15286 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15287 := params 22
abbrev ray15287 := rays 22
def bank15287 : Fin 1 → Cell := oneBank p15287 ray15287
theorem signs15287 : ∀ j, Signs p15287 (bank15287 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15288 := params 23
abbrev ray15288 := rays 23
def bank15288 : Fin 1 → Cell := oneBank p15288 ray15288
theorem signs15288 : ∀ j, Signs p15288 (bank15288 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15289 := params 24
abbrev ray15289 := rays 24
def bank15289 : Fin 1 → Cell := oneBank p15289 ray15289
theorem signs15289 : ∀ j, Signs p15289 (bank15289 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15290 := params 25
abbrev ray15290 := rays 25
def bank15290 : Fin 1 → Cell := oneBank p15290 ray15290
theorem signs15290 : ∀ j, Signs p15290 (bank15290 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15291 := params 26
abbrev ray15291 := rays 26
def bank15291 : Fin 1 → Cell := oneBank p15291 ray15291
theorem signs15291 : ∀ j, Signs p15291 (bank15291 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15292 := params 27
abbrev ray15292 := rays 27
def bank15292 : Fin 1 → Cell := oneBank p15292 ray15292
theorem signs15292 : ∀ j, Signs p15292 (bank15292 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15293 := params 28
abbrev ray15293 := rays 28
def bank15293 : Fin 1 → Cell := oneBank p15293 ray15293
theorem signs15293 : ∀ j, Signs p15293 (bank15293 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15294 := params 29
abbrev ray15294 := rays 29
def bank15294 : Fin 1 → Cell := oneBank p15294 ray15294
theorem signs15294 : ∀ j, Signs p15294 (bank15294 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15295 := params 30
abbrev ray15295 := rays 30
def bank15295 : Fin 1 → Cell := oneBank p15295 ray15295
theorem signs15295 : ∀ j, Signs p15295 (bank15295 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15296 := params 31
abbrev ray15296 := rays 31
def bank15296 : Fin 1 → Cell := oneBank p15296 ray15296
theorem signs15296 : ∀ j, Signs p15296 (bank15296 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15265_15296
