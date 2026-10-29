/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02305_02336
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99635434905536,99635247489152,99635060045482,99634872574527,99634685076288,99634497550767,99634309997965,99634122417884,99633934810525,99633747175889,99633559513978,99633371824793,99633184108336,99632996364608,99632808593610,99632620795344,99632432969811,99632245117012,99632057236949,99631869329623,99631681395036,99631493433189,99631305444084,99631117427721,99630929384103,99630741313230,99630553215104,99630365089727,99630176937099,99629988757223,99629800550099,99629612315729,99629424054114]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2304+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2305 := params 0
abbrev ray2305 := rays 0
def bank2305 : Fin 2 → Cell := twoBank p2305 ray2305
theorem signs2305 : ∀ j, Signs p2305 (bank2305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2306 := params 1
abbrev ray2306 := rays 1
def bank2306 : Fin 2 → Cell := twoBank p2306 ray2306
theorem signs2306 : ∀ j, Signs p2306 (bank2306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2307 := params 2
abbrev ray2307 := rays 2
def bank2307 : Fin 2 → Cell := twoBank p2307 ray2307
theorem signs2307 : ∀ j, Signs p2307 (bank2307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2308 := params 3
abbrev ray2308 := rays 3
def bank2308 : Fin 2 → Cell := twoBank p2308 ray2308
theorem signs2308 : ∀ j, Signs p2308 (bank2308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2309 := params 4
abbrev ray2309 := rays 4
def bank2309 : Fin 2 → Cell := twoBank p2309 ray2309
theorem signs2309 : ∀ j, Signs p2309 (bank2309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2310 := params 5
abbrev ray2310 := rays 5
def bank2310 : Fin 2 → Cell := twoBank p2310 ray2310
theorem signs2310 : ∀ j, Signs p2310 (bank2310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2311 := params 6
abbrev ray2311 := rays 6
def bank2311 : Fin 2 → Cell := twoBank p2311 ray2311
theorem signs2311 : ∀ j, Signs p2311 (bank2311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2312 := params 7
abbrev ray2312 := rays 7
def bank2312 : Fin 2 → Cell := twoBank p2312 ray2312
theorem signs2312 : ∀ j, Signs p2312 (bank2312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2313 := params 8
abbrev ray2313 := rays 8
def bank2313 : Fin 2 → Cell := twoBank p2313 ray2313
theorem signs2313 : ∀ j, Signs p2313 (bank2313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2314 := params 9
abbrev ray2314 := rays 9
def bank2314 : Fin 2 → Cell := twoBank p2314 ray2314
theorem signs2314 : ∀ j, Signs p2314 (bank2314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2315 := params 10
abbrev ray2315 := rays 10
def bank2315 : Fin 2 → Cell := twoBank p2315 ray2315
theorem signs2315 : ∀ j, Signs p2315 (bank2315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2316 := params 11
abbrev ray2316 := rays 11
def bank2316 : Fin 2 → Cell := twoBank p2316 ray2316
theorem signs2316 : ∀ j, Signs p2316 (bank2316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2317 := params 12
abbrev ray2317 := rays 12
def bank2317 : Fin 2 → Cell := twoBank p2317 ray2317
theorem signs2317 : ∀ j, Signs p2317 (bank2317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2318 := params 13
abbrev ray2318 := rays 13
def bank2318 : Fin 2 → Cell := twoBank p2318 ray2318
theorem signs2318 : ∀ j, Signs p2318 (bank2318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2319 := params 14
abbrev ray2319 := rays 14
def bank2319 : Fin 2 → Cell := twoBank p2319 ray2319
theorem signs2319 : ∀ j, Signs p2319 (bank2319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2320 := params 15
abbrev ray2320 := rays 15
def bank2320 : Fin 2 → Cell := twoBank p2320 ray2320
theorem signs2320 : ∀ j, Signs p2320 (bank2320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2321 := params 16
abbrev ray2321 := rays 16
def bank2321 : Fin 2 → Cell := twoBank p2321 ray2321
theorem signs2321 : ∀ j, Signs p2321 (bank2321 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2322 := params 17
abbrev ray2322 := rays 17
def bank2322 : Fin 2 → Cell := twoBank p2322 ray2322
theorem signs2322 : ∀ j, Signs p2322 (bank2322 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2323 := params 18
abbrev ray2323 := rays 18
def bank2323 : Fin 2 → Cell := twoBank p2323 ray2323
theorem signs2323 : ∀ j, Signs p2323 (bank2323 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2324 := params 19
abbrev ray2324 := rays 19
def bank2324 : Fin 2 → Cell := twoBank p2324 ray2324
theorem signs2324 : ∀ j, Signs p2324 (bank2324 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2325 := params 20
abbrev ray2325 := rays 20
def bank2325 : Fin 2 → Cell := twoBank p2325 ray2325
theorem signs2325 : ∀ j, Signs p2325 (bank2325 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2326 := params 21
abbrev ray2326 := rays 21
def bank2326 : Fin 2 → Cell := twoBank p2326 ray2326
theorem signs2326 : ∀ j, Signs p2326 (bank2326 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2327 := params 22
abbrev ray2327 := rays 22
def bank2327 : Fin 2 → Cell := twoBank p2327 ray2327
theorem signs2327 : ∀ j, Signs p2327 (bank2327 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2328 := params 23
abbrev ray2328 := rays 23
def bank2328 : Fin 2 → Cell := twoBank p2328 ray2328
theorem signs2328 : ∀ j, Signs p2328 (bank2328 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2329 := params 24
abbrev ray2329 := rays 24
def bank2329 : Fin 2 → Cell := twoBank p2329 ray2329
theorem signs2329 : ∀ j, Signs p2329 (bank2329 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2330 := params 25
abbrev ray2330 := rays 25
def bank2330 : Fin 2 → Cell := twoBank p2330 ray2330
theorem signs2330 : ∀ j, Signs p2330 (bank2330 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2331 := params 26
abbrev ray2331 := rays 26
def bank2331 : Fin 2 → Cell := twoBank p2331 ray2331
theorem signs2331 : ∀ j, Signs p2331 (bank2331 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2332 := params 27
abbrev ray2332 := rays 27
def bank2332 : Fin 2 → Cell := twoBank p2332 ray2332
theorem signs2332 : ∀ j, Signs p2332 (bank2332 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2333 := params 28
abbrev ray2333 := rays 28
def bank2333 : Fin 2 → Cell := twoBank p2333 ray2333
theorem signs2333 : ∀ j, Signs p2333 (bank2333 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2334 := params 29
abbrev ray2334 := rays 29
def bank2334 : Fin 2 → Cell := twoBank p2334 ray2334
theorem signs2334 : ∀ j, Signs p2334 (bank2334 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2335 := params 30
abbrev ray2335 := rays 30
def bank2335 : Fin 2 → Cell := twoBank p2335 ray2335
theorem signs2335 : ∀ j, Signs p2335 (bank2335 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2336 := params 31
abbrev ray2336 := rays 31
def bank2336 : Fin 2 → Cell := twoBank p2336 ray2336
theorem signs2336 : ∀ j, Signs p2336 (bank2336 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02305_02336
