/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08225_08256
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98088258127658,98087928547616,98087598946143,98087269323240,98086939678908,98086610013148,98086280325960,98085950617345,98085620887303,98085291135836,98084961362944,98084631568627,98084301752886,98083971915722,98083642057136,98083312177128,98082982275700,98082652352851,98082322408583,98081992442896,98081662455790,98081332447267,98081002417327,98080672365971,98080342293199,98080012199012,98079682083411,98079351946397,98079021787970,98078691608131,98078361406880,98078031184219,98077700940148]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8224+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8225 := params 0
abbrev ray8225 := rays 0
def bank8225 : Fin 2 → Cell := twoBank p8225 ray8225
theorem signs8225 : ∀ j, Signs p8225 (bank8225 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8226 := params 1
abbrev ray8226 := rays 1
def bank8226 : Fin 2 → Cell := twoBank p8226 ray8226
theorem signs8226 : ∀ j, Signs p8226 (bank8226 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8227 := params 2
abbrev ray8227 := rays 2
def bank8227 : Fin 2 → Cell := twoBank p8227 ray8227
theorem signs8227 : ∀ j, Signs p8227 (bank8227 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8228 := params 3
abbrev ray8228 := rays 3
def bank8228 : Fin 2 → Cell := twoBank p8228 ray8228
theorem signs8228 : ∀ j, Signs p8228 (bank8228 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8229 := params 4
abbrev ray8229 := rays 4
def bank8229 : Fin 2 → Cell := twoBank p8229 ray8229
theorem signs8229 : ∀ j, Signs p8229 (bank8229 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8230 := params 5
abbrev ray8230 := rays 5
def bank8230 : Fin 2 → Cell := twoBank p8230 ray8230
theorem signs8230 : ∀ j, Signs p8230 (bank8230 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8231 := params 6
abbrev ray8231 := rays 6
def bank8231 : Fin 2 → Cell := twoBank p8231 ray8231
theorem signs8231 : ∀ j, Signs p8231 (bank8231 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8232 := params 7
abbrev ray8232 := rays 7
def bank8232 : Fin 2 → Cell := twoBank p8232 ray8232
theorem signs8232 : ∀ j, Signs p8232 (bank8232 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8233 := params 8
abbrev ray8233 := rays 8
def bank8233 : Fin 2 → Cell := twoBank p8233 ray8233
theorem signs8233 : ∀ j, Signs p8233 (bank8233 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8234 := params 9
abbrev ray8234 := rays 9
def bank8234 : Fin 2 → Cell := twoBank p8234 ray8234
theorem signs8234 : ∀ j, Signs p8234 (bank8234 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8235 := params 10
abbrev ray8235 := rays 10
def bank8235 : Fin 2 → Cell := twoBank p8235 ray8235
theorem signs8235 : ∀ j, Signs p8235 (bank8235 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8236 := params 11
abbrev ray8236 := rays 11
def bank8236 : Fin 2 → Cell := twoBank p8236 ray8236
theorem signs8236 : ∀ j, Signs p8236 (bank8236 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8237 := params 12
abbrev ray8237 := rays 12
def bank8237 : Fin 2 → Cell := twoBank p8237 ray8237
theorem signs8237 : ∀ j, Signs p8237 (bank8237 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8238 := params 13
abbrev ray8238 := rays 13
def bank8238 : Fin 2 → Cell := twoBank p8238 ray8238
theorem signs8238 : ∀ j, Signs p8238 (bank8238 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8239 := params 14
abbrev ray8239 := rays 14
def bank8239 : Fin 2 → Cell := twoBank p8239 ray8239
theorem signs8239 : ∀ j, Signs p8239 (bank8239 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8240 := params 15
abbrev ray8240 := rays 15
def bank8240 : Fin 2 → Cell := twoBank p8240 ray8240
theorem signs8240 : ∀ j, Signs p8240 (bank8240 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8241 := params 16
abbrev ray8241 := rays 16
def bank8241 : Fin 2 → Cell := twoBank p8241 ray8241
theorem signs8241 : ∀ j, Signs p8241 (bank8241 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8242 := params 17
abbrev ray8242 := rays 17
def bank8242 : Fin 2 → Cell := twoBank p8242 ray8242
theorem signs8242 : ∀ j, Signs p8242 (bank8242 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8243 := params 18
abbrev ray8243 := rays 18
def bank8243 : Fin 2 → Cell := twoBank p8243 ray8243
theorem signs8243 : ∀ j, Signs p8243 (bank8243 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8244 := params 19
abbrev ray8244 := rays 19
def bank8244 : Fin 2 → Cell := twoBank p8244 ray8244
theorem signs8244 : ∀ j, Signs p8244 (bank8244 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8245 := params 20
abbrev ray8245 := rays 20
def bank8245 : Fin 2 → Cell := twoBank p8245 ray8245
theorem signs8245 : ∀ j, Signs p8245 (bank8245 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8246 := params 21
abbrev ray8246 := rays 21
def bank8246 : Fin 2 → Cell := twoBank p8246 ray8246
theorem signs8246 : ∀ j, Signs p8246 (bank8246 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8247 := params 22
abbrev ray8247 := rays 22
def bank8247 : Fin 2 → Cell := twoBank p8247 ray8247
theorem signs8247 : ∀ j, Signs p8247 (bank8247 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8248 := params 23
abbrev ray8248 := rays 23
def bank8248 : Fin 2 → Cell := twoBank p8248 ray8248
theorem signs8248 : ∀ j, Signs p8248 (bank8248 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8249 := params 24
abbrev ray8249 := rays 24
def bank8249 : Fin 2 → Cell := twoBank p8249 ray8249
theorem signs8249 : ∀ j, Signs p8249 (bank8249 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8250 := params 25
abbrev ray8250 := rays 25
def bank8250 : Fin 2 → Cell := twoBank p8250 ray8250
theorem signs8250 : ∀ j, Signs p8250 (bank8250 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8251 := params 26
abbrev ray8251 := rays 26
def bank8251 : Fin 2 → Cell := twoBank p8251 ray8251
theorem signs8251 : ∀ j, Signs p8251 (bank8251 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8252 := params 27
abbrev ray8252 := rays 27
def bank8252 : Fin 2 → Cell := twoBank p8252 ray8252
theorem signs8252 : ∀ j, Signs p8252 (bank8252 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8253 := params 28
abbrev ray8253 := rays 28
def bank8253 : Fin 2 → Cell := twoBank p8253 ray8253
theorem signs8253 : ∀ j, Signs p8253 (bank8253 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8254 := params 29
abbrev ray8254 := rays 29
def bank8254 : Fin 2 → Cell := twoBank p8254 ray8254
theorem signs8254 : ∀ j, Signs p8254 (bank8254 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8255 := params 30
abbrev ray8255 := rays 30
def bank8255 : Fin 2 → Cell := twoBank p8255 ray8255
theorem signs8255 : ∀ j, Signs p8255 (bank8255 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8256 := params 31
abbrev ray8256 := rays 31
def bank8256 : Fin 2 → Cell := twoBank p8256 ray8256
theorem signs8256 : ∀ j, Signs p8256 (bank8256 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08225_08256
