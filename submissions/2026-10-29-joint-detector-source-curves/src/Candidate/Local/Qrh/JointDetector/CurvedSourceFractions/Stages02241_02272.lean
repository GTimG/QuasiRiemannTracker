/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02241_02272
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99647372734582,99647187067431,99647001372904,99646815651002,99646629901727,99646444125081,99646258321064,99646072489679,99645886630926,99645700744807,99645514831323,99645328890476,99645142922267,99644956926698,99644770903770,99644584853484,99644398775842,99644212670845,99644026538495,99643840378793,99643654191740,99643467977338,99643281735588,99643095466492,99642909170051,99642722846266,99642536495139,99642350116671,99642163710864,99641977277719,99641790817237,99641604329420,99641417814269]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2240+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2241 := params 0
abbrev ray2241 := rays 0
def bank2241 : Fin 2 → Cell := twoBank p2241 ray2241
theorem signs2241 : ∀ j, Signs p2241 (bank2241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2242 := params 1
abbrev ray2242 := rays 1
def bank2242 : Fin 2 → Cell := twoBank p2242 ray2242
theorem signs2242 : ∀ j, Signs p2242 (bank2242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2243 := params 2
abbrev ray2243 := rays 2
def bank2243 : Fin 2 → Cell := twoBank p2243 ray2243
theorem signs2243 : ∀ j, Signs p2243 (bank2243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2244 := params 3
abbrev ray2244 := rays 3
def bank2244 : Fin 2 → Cell := twoBank p2244 ray2244
theorem signs2244 : ∀ j, Signs p2244 (bank2244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2245 := params 4
abbrev ray2245 := rays 4
def bank2245 : Fin 2 → Cell := twoBank p2245 ray2245
theorem signs2245 : ∀ j, Signs p2245 (bank2245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2246 := params 5
abbrev ray2246 := rays 5
def bank2246 : Fin 2 → Cell := twoBank p2246 ray2246
theorem signs2246 : ∀ j, Signs p2246 (bank2246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2247 := params 6
abbrev ray2247 := rays 6
def bank2247 : Fin 2 → Cell := twoBank p2247 ray2247
theorem signs2247 : ∀ j, Signs p2247 (bank2247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2248 := params 7
abbrev ray2248 := rays 7
def bank2248 : Fin 2 → Cell := twoBank p2248 ray2248
theorem signs2248 : ∀ j, Signs p2248 (bank2248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2249 := params 8
abbrev ray2249 := rays 8
def bank2249 : Fin 2 → Cell := twoBank p2249 ray2249
theorem signs2249 : ∀ j, Signs p2249 (bank2249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2250 := params 9
abbrev ray2250 := rays 9
def bank2250 : Fin 2 → Cell := twoBank p2250 ray2250
theorem signs2250 : ∀ j, Signs p2250 (bank2250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2251 := params 10
abbrev ray2251 := rays 10
def bank2251 : Fin 2 → Cell := twoBank p2251 ray2251
theorem signs2251 : ∀ j, Signs p2251 (bank2251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2252 := params 11
abbrev ray2252 := rays 11
def bank2252 : Fin 2 → Cell := twoBank p2252 ray2252
theorem signs2252 : ∀ j, Signs p2252 (bank2252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2253 := params 12
abbrev ray2253 := rays 12
def bank2253 : Fin 2 → Cell := twoBank p2253 ray2253
theorem signs2253 : ∀ j, Signs p2253 (bank2253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2254 := params 13
abbrev ray2254 := rays 13
def bank2254 : Fin 2 → Cell := twoBank p2254 ray2254
theorem signs2254 : ∀ j, Signs p2254 (bank2254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2255 := params 14
abbrev ray2255 := rays 14
def bank2255 : Fin 2 → Cell := twoBank p2255 ray2255
theorem signs2255 : ∀ j, Signs p2255 (bank2255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2256 := params 15
abbrev ray2256 := rays 15
def bank2256 : Fin 2 → Cell := twoBank p2256 ray2256
theorem signs2256 : ∀ j, Signs p2256 (bank2256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2257 := params 16
abbrev ray2257 := rays 16
def bank2257 : Fin 2 → Cell := twoBank p2257 ray2257
theorem signs2257 : ∀ j, Signs p2257 (bank2257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2258 := params 17
abbrev ray2258 := rays 17
def bank2258 : Fin 2 → Cell := twoBank p2258 ray2258
theorem signs2258 : ∀ j, Signs p2258 (bank2258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2259 := params 18
abbrev ray2259 := rays 18
def bank2259 : Fin 2 → Cell := twoBank p2259 ray2259
theorem signs2259 : ∀ j, Signs p2259 (bank2259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2260 := params 19
abbrev ray2260 := rays 19
def bank2260 : Fin 2 → Cell := twoBank p2260 ray2260
theorem signs2260 : ∀ j, Signs p2260 (bank2260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2261 := params 20
abbrev ray2261 := rays 20
def bank2261 : Fin 2 → Cell := twoBank p2261 ray2261
theorem signs2261 : ∀ j, Signs p2261 (bank2261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2262 := params 21
abbrev ray2262 := rays 21
def bank2262 : Fin 2 → Cell := twoBank p2262 ray2262
theorem signs2262 : ∀ j, Signs p2262 (bank2262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2263 := params 22
abbrev ray2263 := rays 22
def bank2263 : Fin 2 → Cell := twoBank p2263 ray2263
theorem signs2263 : ∀ j, Signs p2263 (bank2263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2264 := params 23
abbrev ray2264 := rays 23
def bank2264 : Fin 2 → Cell := twoBank p2264 ray2264
theorem signs2264 : ∀ j, Signs p2264 (bank2264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2265 := params 24
abbrev ray2265 := rays 24
def bank2265 : Fin 2 → Cell := twoBank p2265 ray2265
theorem signs2265 : ∀ j, Signs p2265 (bank2265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2266 := params 25
abbrev ray2266 := rays 25
def bank2266 : Fin 2 → Cell := twoBank p2266 ray2266
theorem signs2266 : ∀ j, Signs p2266 (bank2266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2267 := params 26
abbrev ray2267 := rays 26
def bank2267 : Fin 2 → Cell := twoBank p2267 ray2267
theorem signs2267 : ∀ j, Signs p2267 (bank2267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2268 := params 27
abbrev ray2268 := rays 27
def bank2268 : Fin 2 → Cell := twoBank p2268 ray2268
theorem signs2268 : ∀ j, Signs p2268 (bank2268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2269 := params 28
abbrev ray2269 := rays 28
def bank2269 : Fin 2 → Cell := twoBank p2269 ray2269
theorem signs2269 : ∀ j, Signs p2269 (bank2269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2270 := params 29
abbrev ray2270 := rays 29
def bank2270 : Fin 2 → Cell := twoBank p2270 ray2270
theorem signs2270 : ∀ j, Signs p2270 (bank2270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2271 := params 30
abbrev ray2271 := rays 30
def bank2271 : Fin 2 → Cell := twoBank p2271 ray2271
theorem signs2271 : ∀ j, Signs p2271 (bank2271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2272 := params 31
abbrev ray2272 := rays 31
def bank2272 : Fin 2 → Cell := twoBank p2272 ray2272
theorem signs2272 : ∀ j, Signs p2272 (bank2272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02241_02272
