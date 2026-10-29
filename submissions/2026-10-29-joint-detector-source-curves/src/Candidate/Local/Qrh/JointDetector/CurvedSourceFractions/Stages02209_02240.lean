/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02209_02240
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99653299620555,99653114830174,99652930012372,99652745167150,99652560294510,99652375394454,99652190466982,99652005512097,99651820529799,99651635520090,99651450482972,99651265418445,99651080326512,99650895207173,99650710060430,99650524886285,99650339684738,99650154455792,99649969199447,99649783915705,99649598604568,99649413266037,99649227900113,99649042506798,99648857086093,99648671637999,99648486162518,99648300659651,99648115129400,99647929571766,99647743986751,99647558374356,99647372734582]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2208+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2209 := params 0
abbrev ray2209 := rays 0
def bank2209 : Fin 2 → Cell := twoBank p2209 ray2209
theorem signs2209 : ∀ j, Signs p2209 (bank2209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2210 := params 1
abbrev ray2210 := rays 1
def bank2210 : Fin 2 → Cell := twoBank p2210 ray2210
theorem signs2210 : ∀ j, Signs p2210 (bank2210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2211 := params 2
abbrev ray2211 := rays 2
def bank2211 : Fin 2 → Cell := twoBank p2211 ray2211
theorem signs2211 : ∀ j, Signs p2211 (bank2211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2212 := params 3
abbrev ray2212 := rays 3
def bank2212 : Fin 2 → Cell := twoBank p2212 ray2212
theorem signs2212 : ∀ j, Signs p2212 (bank2212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2213 := params 4
abbrev ray2213 := rays 4
def bank2213 : Fin 2 → Cell := twoBank p2213 ray2213
theorem signs2213 : ∀ j, Signs p2213 (bank2213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2214 := params 5
abbrev ray2214 := rays 5
def bank2214 : Fin 2 → Cell := twoBank p2214 ray2214
theorem signs2214 : ∀ j, Signs p2214 (bank2214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2215 := params 6
abbrev ray2215 := rays 6
def bank2215 : Fin 2 → Cell := twoBank p2215 ray2215
theorem signs2215 : ∀ j, Signs p2215 (bank2215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2216 := params 7
abbrev ray2216 := rays 7
def bank2216 : Fin 2 → Cell := twoBank p2216 ray2216
theorem signs2216 : ∀ j, Signs p2216 (bank2216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2217 := params 8
abbrev ray2217 := rays 8
def bank2217 : Fin 2 → Cell := twoBank p2217 ray2217
theorem signs2217 : ∀ j, Signs p2217 (bank2217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2218 := params 9
abbrev ray2218 := rays 9
def bank2218 : Fin 2 → Cell := twoBank p2218 ray2218
theorem signs2218 : ∀ j, Signs p2218 (bank2218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2219 := params 10
abbrev ray2219 := rays 10
def bank2219 : Fin 2 → Cell := twoBank p2219 ray2219
theorem signs2219 : ∀ j, Signs p2219 (bank2219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2220 := params 11
abbrev ray2220 := rays 11
def bank2220 : Fin 2 → Cell := twoBank p2220 ray2220
theorem signs2220 : ∀ j, Signs p2220 (bank2220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2221 := params 12
abbrev ray2221 := rays 12
def bank2221 : Fin 2 → Cell := twoBank p2221 ray2221
theorem signs2221 : ∀ j, Signs p2221 (bank2221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2222 := params 13
abbrev ray2222 := rays 13
def bank2222 : Fin 2 → Cell := twoBank p2222 ray2222
theorem signs2222 : ∀ j, Signs p2222 (bank2222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2223 := params 14
abbrev ray2223 := rays 14
def bank2223 : Fin 2 → Cell := twoBank p2223 ray2223
theorem signs2223 : ∀ j, Signs p2223 (bank2223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2224 := params 15
abbrev ray2224 := rays 15
def bank2224 : Fin 2 → Cell := twoBank p2224 ray2224
theorem signs2224 : ∀ j, Signs p2224 (bank2224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2225 := params 16
abbrev ray2225 := rays 16
def bank2225 : Fin 2 → Cell := twoBank p2225 ray2225
theorem signs2225 : ∀ j, Signs p2225 (bank2225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2226 := params 17
abbrev ray2226 := rays 17
def bank2226 : Fin 2 → Cell := twoBank p2226 ray2226
theorem signs2226 : ∀ j, Signs p2226 (bank2226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2227 := params 18
abbrev ray2227 := rays 18
def bank2227 : Fin 2 → Cell := twoBank p2227 ray2227
theorem signs2227 : ∀ j, Signs p2227 (bank2227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2228 := params 19
abbrev ray2228 := rays 19
def bank2228 : Fin 2 → Cell := twoBank p2228 ray2228
theorem signs2228 : ∀ j, Signs p2228 (bank2228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2229 := params 20
abbrev ray2229 := rays 20
def bank2229 : Fin 2 → Cell := twoBank p2229 ray2229
theorem signs2229 : ∀ j, Signs p2229 (bank2229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2230 := params 21
abbrev ray2230 := rays 21
def bank2230 : Fin 2 → Cell := twoBank p2230 ray2230
theorem signs2230 : ∀ j, Signs p2230 (bank2230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2231 := params 22
abbrev ray2231 := rays 22
def bank2231 : Fin 2 → Cell := twoBank p2231 ray2231
theorem signs2231 : ∀ j, Signs p2231 (bank2231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2232 := params 23
abbrev ray2232 := rays 23
def bank2232 : Fin 2 → Cell := twoBank p2232 ray2232
theorem signs2232 : ∀ j, Signs p2232 (bank2232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2233 := params 24
abbrev ray2233 := rays 24
def bank2233 : Fin 2 → Cell := twoBank p2233 ray2233
theorem signs2233 : ∀ j, Signs p2233 (bank2233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2234 := params 25
abbrev ray2234 := rays 25
def bank2234 : Fin 2 → Cell := twoBank p2234 ray2234
theorem signs2234 : ∀ j, Signs p2234 (bank2234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2235 := params 26
abbrev ray2235 := rays 26
def bank2235 : Fin 2 → Cell := twoBank p2235 ray2235
theorem signs2235 : ∀ j, Signs p2235 (bank2235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2236 := params 27
abbrev ray2236 := rays 27
def bank2236 : Fin 2 → Cell := twoBank p2236 ray2236
theorem signs2236 : ∀ j, Signs p2236 (bank2236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2237 := params 28
abbrev ray2237 := rays 28
def bank2237 : Fin 2 → Cell := twoBank p2237 ray2237
theorem signs2237 : ∀ j, Signs p2237 (bank2237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2238 := params 29
abbrev ray2238 := rays 29
def bank2238 : Fin 2 → Cell := twoBank p2238 ray2238
theorem signs2238 : ∀ j, Signs p2238 (bank2238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2239 := params 30
abbrev ray2239 := rays 30
def bank2239 : Fin 2 → Cell := twoBank p2239 ray2239
theorem signs2239 : ∀ j, Signs p2239 (bank2239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2240 := params 31
abbrev ray2240 := rays 31
def bank2240 : Fin 2 → Cell := twoBank p2240 ray2240
theorem signs2240 : ∀ j, Signs p2240 (bank2240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02209_02240
