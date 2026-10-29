/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02273_02304
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99641417814269,99641231271786,99641044701971,99640858104827,99640671480355,99640484828556,99640298149431,99640111442982,99639924709211,99639737948118,99639551159706,99639364343975,99639177500927,99638990630563,99638803732885,99638616807894,99638429855592,99638242875980,99638055869059,99637868834831,99637681773297,99637494684458,99637307568316,99637120424873,99636933254129,99636746056086,99636558830746,99636371578110,99636184298179,99635996990955,99635809656439,99635622294632,99635434905536]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2272+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2273 := params 0
abbrev ray2273 := rays 0
def bank2273 : Fin 2 → Cell := twoBank p2273 ray2273
theorem signs2273 : ∀ j, Signs p2273 (bank2273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2274 := params 1
abbrev ray2274 := rays 1
def bank2274 : Fin 2 → Cell := twoBank p2274 ray2274
theorem signs2274 : ∀ j, Signs p2274 (bank2274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2275 := params 2
abbrev ray2275 := rays 2
def bank2275 : Fin 2 → Cell := twoBank p2275 ray2275
theorem signs2275 : ∀ j, Signs p2275 (bank2275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2276 := params 3
abbrev ray2276 := rays 3
def bank2276 : Fin 2 → Cell := twoBank p2276 ray2276
theorem signs2276 : ∀ j, Signs p2276 (bank2276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2277 := params 4
abbrev ray2277 := rays 4
def bank2277 : Fin 2 → Cell := twoBank p2277 ray2277
theorem signs2277 : ∀ j, Signs p2277 (bank2277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2278 := params 5
abbrev ray2278 := rays 5
def bank2278 : Fin 2 → Cell := twoBank p2278 ray2278
theorem signs2278 : ∀ j, Signs p2278 (bank2278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2279 := params 6
abbrev ray2279 := rays 6
def bank2279 : Fin 2 → Cell := twoBank p2279 ray2279
theorem signs2279 : ∀ j, Signs p2279 (bank2279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2280 := params 7
abbrev ray2280 := rays 7
def bank2280 : Fin 2 → Cell := twoBank p2280 ray2280
theorem signs2280 : ∀ j, Signs p2280 (bank2280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2281 := params 8
abbrev ray2281 := rays 8
def bank2281 : Fin 2 → Cell := twoBank p2281 ray2281
theorem signs2281 : ∀ j, Signs p2281 (bank2281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2282 := params 9
abbrev ray2282 := rays 9
def bank2282 : Fin 2 → Cell := twoBank p2282 ray2282
theorem signs2282 : ∀ j, Signs p2282 (bank2282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2283 := params 10
abbrev ray2283 := rays 10
def bank2283 : Fin 2 → Cell := twoBank p2283 ray2283
theorem signs2283 : ∀ j, Signs p2283 (bank2283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2284 := params 11
abbrev ray2284 := rays 11
def bank2284 : Fin 2 → Cell := twoBank p2284 ray2284
theorem signs2284 : ∀ j, Signs p2284 (bank2284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2285 := params 12
abbrev ray2285 := rays 12
def bank2285 : Fin 2 → Cell := twoBank p2285 ray2285
theorem signs2285 : ∀ j, Signs p2285 (bank2285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2286 := params 13
abbrev ray2286 := rays 13
def bank2286 : Fin 2 → Cell := twoBank p2286 ray2286
theorem signs2286 : ∀ j, Signs p2286 (bank2286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2287 := params 14
abbrev ray2287 := rays 14
def bank2287 : Fin 2 → Cell := twoBank p2287 ray2287
theorem signs2287 : ∀ j, Signs p2287 (bank2287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2288 := params 15
abbrev ray2288 := rays 15
def bank2288 : Fin 2 → Cell := twoBank p2288 ray2288
theorem signs2288 : ∀ j, Signs p2288 (bank2288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2289 := params 16
abbrev ray2289 := rays 16
def bank2289 : Fin 2 → Cell := twoBank p2289 ray2289
theorem signs2289 : ∀ j, Signs p2289 (bank2289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2290 := params 17
abbrev ray2290 := rays 17
def bank2290 : Fin 2 → Cell := twoBank p2290 ray2290
theorem signs2290 : ∀ j, Signs p2290 (bank2290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2291 := params 18
abbrev ray2291 := rays 18
def bank2291 : Fin 2 → Cell := twoBank p2291 ray2291
theorem signs2291 : ∀ j, Signs p2291 (bank2291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2292 := params 19
abbrev ray2292 := rays 19
def bank2292 : Fin 2 → Cell := twoBank p2292 ray2292
theorem signs2292 : ∀ j, Signs p2292 (bank2292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2293 := params 20
abbrev ray2293 := rays 20
def bank2293 : Fin 2 → Cell := twoBank p2293 ray2293
theorem signs2293 : ∀ j, Signs p2293 (bank2293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2294 := params 21
abbrev ray2294 := rays 21
def bank2294 : Fin 2 → Cell := twoBank p2294 ray2294
theorem signs2294 : ∀ j, Signs p2294 (bank2294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2295 := params 22
abbrev ray2295 := rays 22
def bank2295 : Fin 2 → Cell := twoBank p2295 ray2295
theorem signs2295 : ∀ j, Signs p2295 (bank2295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2296 := params 23
abbrev ray2296 := rays 23
def bank2296 : Fin 2 → Cell := twoBank p2296 ray2296
theorem signs2296 : ∀ j, Signs p2296 (bank2296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2297 := params 24
abbrev ray2297 := rays 24
def bank2297 : Fin 2 → Cell := twoBank p2297 ray2297
theorem signs2297 : ∀ j, Signs p2297 (bank2297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2298 := params 25
abbrev ray2298 := rays 25
def bank2298 : Fin 2 → Cell := twoBank p2298 ray2298
theorem signs2298 : ∀ j, Signs p2298 (bank2298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2299 := params 26
abbrev ray2299 := rays 26
def bank2299 : Fin 2 → Cell := twoBank p2299 ray2299
theorem signs2299 : ∀ j, Signs p2299 (bank2299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2300 := params 27
abbrev ray2300 := rays 27
def bank2300 : Fin 2 → Cell := twoBank p2300 ray2300
theorem signs2300 : ∀ j, Signs p2300 (bank2300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2301 := params 28
abbrev ray2301 := rays 28
def bank2301 : Fin 2 → Cell := twoBank p2301 ray2301
theorem signs2301 : ∀ j, Signs p2301 (bank2301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2302 := params 29
abbrev ray2302 := rays 29
def bank2302 : Fin 2 → Cell := twoBank p2302 ray2302
theorem signs2302 : ∀ j, Signs p2302 (bank2302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2303 := params 30
abbrev ray2303 := rays 30
def bank2303 : Fin 2 → Cell := twoBank p2303 ray2303
theorem signs2303 : ∀ j, Signs p2303 (bank2303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2304 := params 31
abbrev ray2304 := rays 31
def bank2304 : Fin 2 → Cell := twoBank p2304 ray2304
theorem signs2304 : ∀ j, Signs p2304 (bank2304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02273_02304
