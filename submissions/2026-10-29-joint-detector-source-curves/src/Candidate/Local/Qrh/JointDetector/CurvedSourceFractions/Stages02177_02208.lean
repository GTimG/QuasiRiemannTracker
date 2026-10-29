/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02177_02208
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99659198426077,99659014513910,99658830574277,99658646607179,99658462612618,99658278590595,99658094541111,99657910464168,99657726359768,99657542227912,99657358068601,99657173881836,99656989667619,99656805425952,99656621156836,99656436860272,99656252536262,99656068184807,99655883805908,99655699399567,99655514965786,99655330504566,99655146015908,99654961499813,99654776956283,99654592385320,99654407786925,99654223161099,99654038507843,99653853827159,99653669119049,99653484383514,99653299620555]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2176+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2177 := params 0
abbrev ray2177 := rays 0
def bank2177 : Fin 2 → Cell := twoBank p2177 ray2177
theorem signs2177 : ∀ j, Signs p2177 (bank2177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2178 := params 1
abbrev ray2178 := rays 1
def bank2178 : Fin 2 → Cell := twoBank p2178 ray2178
theorem signs2178 : ∀ j, Signs p2178 (bank2178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2179 := params 2
abbrev ray2179 := rays 2
def bank2179 : Fin 2 → Cell := twoBank p2179 ray2179
theorem signs2179 : ∀ j, Signs p2179 (bank2179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2180 := params 3
abbrev ray2180 := rays 3
def bank2180 : Fin 2 → Cell := twoBank p2180 ray2180
theorem signs2180 : ∀ j, Signs p2180 (bank2180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2181 := params 4
abbrev ray2181 := rays 4
def bank2181 : Fin 2 → Cell := twoBank p2181 ray2181
theorem signs2181 : ∀ j, Signs p2181 (bank2181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2182 := params 5
abbrev ray2182 := rays 5
def bank2182 : Fin 2 → Cell := twoBank p2182 ray2182
theorem signs2182 : ∀ j, Signs p2182 (bank2182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2183 := params 6
abbrev ray2183 := rays 6
def bank2183 : Fin 2 → Cell := twoBank p2183 ray2183
theorem signs2183 : ∀ j, Signs p2183 (bank2183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2184 := params 7
abbrev ray2184 := rays 7
def bank2184 : Fin 2 → Cell := twoBank p2184 ray2184
theorem signs2184 : ∀ j, Signs p2184 (bank2184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2185 := params 8
abbrev ray2185 := rays 8
def bank2185 : Fin 2 → Cell := twoBank p2185 ray2185
theorem signs2185 : ∀ j, Signs p2185 (bank2185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2186 := params 9
abbrev ray2186 := rays 9
def bank2186 : Fin 2 → Cell := twoBank p2186 ray2186
theorem signs2186 : ∀ j, Signs p2186 (bank2186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2187 := params 10
abbrev ray2187 := rays 10
def bank2187 : Fin 2 → Cell := twoBank p2187 ray2187
theorem signs2187 : ∀ j, Signs p2187 (bank2187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2188 := params 11
abbrev ray2188 := rays 11
def bank2188 : Fin 2 → Cell := twoBank p2188 ray2188
theorem signs2188 : ∀ j, Signs p2188 (bank2188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2189 := params 12
abbrev ray2189 := rays 12
def bank2189 : Fin 2 → Cell := twoBank p2189 ray2189
theorem signs2189 : ∀ j, Signs p2189 (bank2189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2190 := params 13
abbrev ray2190 := rays 13
def bank2190 : Fin 2 → Cell := twoBank p2190 ray2190
theorem signs2190 : ∀ j, Signs p2190 (bank2190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2191 := params 14
abbrev ray2191 := rays 14
def bank2191 : Fin 2 → Cell := twoBank p2191 ray2191
theorem signs2191 : ∀ j, Signs p2191 (bank2191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2192 := params 15
abbrev ray2192 := rays 15
def bank2192 : Fin 2 → Cell := twoBank p2192 ray2192
theorem signs2192 : ∀ j, Signs p2192 (bank2192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2193 := params 16
abbrev ray2193 := rays 16
def bank2193 : Fin 2 → Cell := twoBank p2193 ray2193
theorem signs2193 : ∀ j, Signs p2193 (bank2193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2194 := params 17
abbrev ray2194 := rays 17
def bank2194 : Fin 2 → Cell := twoBank p2194 ray2194
theorem signs2194 : ∀ j, Signs p2194 (bank2194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2195 := params 18
abbrev ray2195 := rays 18
def bank2195 : Fin 2 → Cell := twoBank p2195 ray2195
theorem signs2195 : ∀ j, Signs p2195 (bank2195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2196 := params 19
abbrev ray2196 := rays 19
def bank2196 : Fin 2 → Cell := twoBank p2196 ray2196
theorem signs2196 : ∀ j, Signs p2196 (bank2196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2197 := params 20
abbrev ray2197 := rays 20
def bank2197 : Fin 2 → Cell := twoBank p2197 ray2197
theorem signs2197 : ∀ j, Signs p2197 (bank2197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2198 := params 21
abbrev ray2198 := rays 21
def bank2198 : Fin 2 → Cell := twoBank p2198 ray2198
theorem signs2198 : ∀ j, Signs p2198 (bank2198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2199 := params 22
abbrev ray2199 := rays 22
def bank2199 : Fin 2 → Cell := twoBank p2199 ray2199
theorem signs2199 : ∀ j, Signs p2199 (bank2199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2200 := params 23
abbrev ray2200 := rays 23
def bank2200 : Fin 2 → Cell := twoBank p2200 ray2200
theorem signs2200 : ∀ j, Signs p2200 (bank2200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2201 := params 24
abbrev ray2201 := rays 24
def bank2201 : Fin 2 → Cell := twoBank p2201 ray2201
theorem signs2201 : ∀ j, Signs p2201 (bank2201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2202 := params 25
abbrev ray2202 := rays 25
def bank2202 : Fin 2 → Cell := twoBank p2202 ray2202
theorem signs2202 : ∀ j, Signs p2202 (bank2202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2203 := params 26
abbrev ray2203 := rays 26
def bank2203 : Fin 2 → Cell := twoBank p2203 ray2203
theorem signs2203 : ∀ j, Signs p2203 (bank2203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2204 := params 27
abbrev ray2204 := rays 27
def bank2204 : Fin 2 → Cell := twoBank p2204 ray2204
theorem signs2204 : ∀ j, Signs p2204 (bank2204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2205 := params 28
abbrev ray2205 := rays 28
def bank2205 : Fin 2 → Cell := twoBank p2205 ray2205
theorem signs2205 : ∀ j, Signs p2205 (bank2205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2206 := params 29
abbrev ray2206 := rays 29
def bank2206 : Fin 2 → Cell := twoBank p2206 ray2206
theorem signs2206 : ∀ j, Signs p2206 (bank2206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2207 := params 30
abbrev ray2207 := rays 30
def bank2207 : Fin 2 → Cell := twoBank p2207 ray2207
theorem signs2207 : ∀ j, Signs p2207 (bank2207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2208 := params 31
abbrev ray2208 := rays 31
def bank2208 : Fin 2 → Cell := twoBank p2208 ray2208
theorem signs2208 : ∀ j, Signs p2208 (bank2208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02177_02208
