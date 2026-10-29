/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages11201_11232
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97015309237477,97014918576882,97014527896568,97014137196536,97013746476786,97013355737319,97012964978135,97012574199235,97012183400619,97011792582288,97011401744242,97011010886482,97010620009008,97010229111820,97009838194920,97009447258307,97009056301982,97008665325946,97008274330199,97007883314741,97007492279573,97007101224695,97006710150108,97006319055813,97005927941809,97005536808098,97005145654680,97004754481555,97004363288724,97003972076187,97003580843945,97003189591998,97002798320346]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (11200+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p11201 := params 0
abbrev ray11201 := rays 0
def bank11201 : Fin 2 → Cell := twoBank p11201 ray11201
theorem signs11201 : ∀ j, Signs p11201 (bank11201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11202 := params 1
abbrev ray11202 := rays 1
def bank11202 : Fin 2 → Cell := twoBank p11202 ray11202
theorem signs11202 : ∀ j, Signs p11202 (bank11202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11203 := params 2
abbrev ray11203 := rays 2
def bank11203 : Fin 2 → Cell := twoBank p11203 ray11203
theorem signs11203 : ∀ j, Signs p11203 (bank11203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11204 := params 3
abbrev ray11204 := rays 3
def bank11204 : Fin 2 → Cell := twoBank p11204 ray11204
theorem signs11204 : ∀ j, Signs p11204 (bank11204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11205 := params 4
abbrev ray11205 := rays 4
def bank11205 : Fin 2 → Cell := twoBank p11205 ray11205
theorem signs11205 : ∀ j, Signs p11205 (bank11205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11206 := params 5
abbrev ray11206 := rays 5
def bank11206 : Fin 2 → Cell := twoBank p11206 ray11206
theorem signs11206 : ∀ j, Signs p11206 (bank11206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11207 := params 6
abbrev ray11207 := rays 6
def bank11207 : Fin 2 → Cell := twoBank p11207 ray11207
theorem signs11207 : ∀ j, Signs p11207 (bank11207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11208 := params 7
abbrev ray11208 := rays 7
def bank11208 : Fin 2 → Cell := twoBank p11208 ray11208
theorem signs11208 : ∀ j, Signs p11208 (bank11208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11209 := params 8
abbrev ray11209 := rays 8
def bank11209 : Fin 2 → Cell := twoBank p11209 ray11209
theorem signs11209 : ∀ j, Signs p11209 (bank11209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11210 := params 9
abbrev ray11210 := rays 9
def bank11210 : Fin 2 → Cell := twoBank p11210 ray11210
theorem signs11210 : ∀ j, Signs p11210 (bank11210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11211 := params 10
abbrev ray11211 := rays 10
def bank11211 : Fin 2 → Cell := twoBank p11211 ray11211
theorem signs11211 : ∀ j, Signs p11211 (bank11211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11212 := params 11
abbrev ray11212 := rays 11
def bank11212 : Fin 2 → Cell := twoBank p11212 ray11212
theorem signs11212 : ∀ j, Signs p11212 (bank11212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11213 := params 12
abbrev ray11213 := rays 12
def bank11213 : Fin 2 → Cell := twoBank p11213 ray11213
theorem signs11213 : ∀ j, Signs p11213 (bank11213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11214 := params 13
abbrev ray11214 := rays 13
def bank11214 : Fin 2 → Cell := twoBank p11214 ray11214
theorem signs11214 : ∀ j, Signs p11214 (bank11214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11215 := params 14
abbrev ray11215 := rays 14
def bank11215 : Fin 2 → Cell := twoBank p11215 ray11215
theorem signs11215 : ∀ j, Signs p11215 (bank11215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11216 := params 15
abbrev ray11216 := rays 15
def bank11216 : Fin 2 → Cell := twoBank p11216 ray11216
theorem signs11216 : ∀ j, Signs p11216 (bank11216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11217 := params 16
abbrev ray11217 := rays 16
def bank11217 : Fin 2 → Cell := twoBank p11217 ray11217
theorem signs11217 : ∀ j, Signs p11217 (bank11217 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11218 := params 17
abbrev ray11218 := rays 17
def bank11218 : Fin 2 → Cell := twoBank p11218 ray11218
theorem signs11218 : ∀ j, Signs p11218 (bank11218 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11219 := params 18
abbrev ray11219 := rays 18
def bank11219 : Fin 2 → Cell := twoBank p11219 ray11219
theorem signs11219 : ∀ j, Signs p11219 (bank11219 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11220 := params 19
abbrev ray11220 := rays 19
def bank11220 : Fin 2 → Cell := twoBank p11220 ray11220
theorem signs11220 : ∀ j, Signs p11220 (bank11220 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11221 := params 20
abbrev ray11221 := rays 20
def bank11221 : Fin 2 → Cell := twoBank p11221 ray11221
theorem signs11221 : ∀ j, Signs p11221 (bank11221 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11222 := params 21
abbrev ray11222 := rays 21
def bank11222 : Fin 2 → Cell := twoBank p11222 ray11222
theorem signs11222 : ∀ j, Signs p11222 (bank11222 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11223 := params 22
abbrev ray11223 := rays 22
def bank11223 : Fin 2 → Cell := twoBank p11223 ray11223
theorem signs11223 : ∀ j, Signs p11223 (bank11223 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11224 := params 23
abbrev ray11224 := rays 23
def bank11224 : Fin 2 → Cell := twoBank p11224 ray11224
theorem signs11224 : ∀ j, Signs p11224 (bank11224 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11225 := params 24
abbrev ray11225 := rays 24
def bank11225 : Fin 2 → Cell := twoBank p11225 ray11225
theorem signs11225 : ∀ j, Signs p11225 (bank11225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11226 := params 25
abbrev ray11226 := rays 25
def bank11226 : Fin 2 → Cell := twoBank p11226 ray11226
theorem signs11226 : ∀ j, Signs p11226 (bank11226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11227 := params 26
abbrev ray11227 := rays 26
def bank11227 : Fin 2 → Cell := twoBank p11227 ray11227
theorem signs11227 : ∀ j, Signs p11227 (bank11227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11228 := params 27
abbrev ray11228 := rays 27
def bank11228 : Fin 2 → Cell := twoBank p11228 ray11228
theorem signs11228 : ∀ j, Signs p11228 (bank11228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11229 := params 28
abbrev ray11229 := rays 28
def bank11229 : Fin 2 → Cell := twoBank p11229 ray11229
theorem signs11229 : ∀ j, Signs p11229 (bank11229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11230 := params 29
abbrev ray11230 := rays 29
def bank11230 : Fin 2 → Cell := twoBank p11230 ray11230
theorem signs11230 : ∀ j, Signs p11230 (bank11230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11231 := params 30
abbrev ray11231 := rays 30
def bank11231 : Fin 2 → Cell := twoBank p11231 ray11231
theorem signs11231 : ∀ j, Signs p11231 (bank11231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p11232 := params 31
abbrev ray11232 := rays 31
def bank11232 : Fin 2 → Cell := twoBank p11232 ray11232
theorem signs11232 : ∀ j, Signs p11232 (bank11232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages11201_11232
