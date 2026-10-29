/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13249_13280
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96174810480098,96174381510693,96173952524914,96173523522761,96173094504234,96172665469333,96172236418059,96171807350412,96171378266392,96170949165999,96170520049234,96170090916097,96169661766588,96169232600707,96168803418455,96168374219831,96167945004836,96167515773471,96167086525735,96166657261629,96166227981153,96165798684307,96165369371092,96164940041508,96164510695554,96164081333232,96163651954541,96163222559482,96162793148055,96162363720260,96161934276097,96161504815567,96161075338670]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13248+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13249 := params 0
abbrev ray13249 := rays 0
def bank13249 : Fin 1 → Cell := oneBank p13249 ray13249
theorem signs13249 : ∀ j, Signs p13249 (bank13249 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13250 := params 1
abbrev ray13250 := rays 1
def bank13250 : Fin 1 → Cell := oneBank p13250 ray13250
theorem signs13250 : ∀ j, Signs p13250 (bank13250 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13251 := params 2
abbrev ray13251 := rays 2
def bank13251 : Fin 1 → Cell := oneBank p13251 ray13251
theorem signs13251 : ∀ j, Signs p13251 (bank13251 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13252 := params 3
abbrev ray13252 := rays 3
def bank13252 : Fin 1 → Cell := oneBank p13252 ray13252
theorem signs13252 : ∀ j, Signs p13252 (bank13252 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13253 := params 4
abbrev ray13253 := rays 4
def bank13253 : Fin 1 → Cell := oneBank p13253 ray13253
theorem signs13253 : ∀ j, Signs p13253 (bank13253 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13254 := params 5
abbrev ray13254 := rays 5
def bank13254 : Fin 1 → Cell := oneBank p13254 ray13254
theorem signs13254 : ∀ j, Signs p13254 (bank13254 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13255 := params 6
abbrev ray13255 := rays 6
def bank13255 : Fin 1 → Cell := oneBank p13255 ray13255
theorem signs13255 : ∀ j, Signs p13255 (bank13255 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13256 := params 7
abbrev ray13256 := rays 7
def bank13256 : Fin 1 → Cell := oneBank p13256 ray13256
theorem signs13256 : ∀ j, Signs p13256 (bank13256 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13257 := params 8
abbrev ray13257 := rays 8
def bank13257 : Fin 1 → Cell := oneBank p13257 ray13257
theorem signs13257 : ∀ j, Signs p13257 (bank13257 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13258 := params 9
abbrev ray13258 := rays 9
def bank13258 : Fin 1 → Cell := oneBank p13258 ray13258
theorem signs13258 : ∀ j, Signs p13258 (bank13258 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13259 := params 10
abbrev ray13259 := rays 10
def bank13259 : Fin 1 → Cell := oneBank p13259 ray13259
theorem signs13259 : ∀ j, Signs p13259 (bank13259 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13260 := params 11
abbrev ray13260 := rays 11
def bank13260 : Fin 1 → Cell := oneBank p13260 ray13260
theorem signs13260 : ∀ j, Signs p13260 (bank13260 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13261 := params 12
abbrev ray13261 := rays 12
def bank13261 : Fin 1 → Cell := oneBank p13261 ray13261
theorem signs13261 : ∀ j, Signs p13261 (bank13261 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13262 := params 13
abbrev ray13262 := rays 13
def bank13262 : Fin 1 → Cell := oneBank p13262 ray13262
theorem signs13262 : ∀ j, Signs p13262 (bank13262 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13263 := params 14
abbrev ray13263 := rays 14
def bank13263 : Fin 1 → Cell := oneBank p13263 ray13263
theorem signs13263 : ∀ j, Signs p13263 (bank13263 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13264 := params 15
abbrev ray13264 := rays 15
def bank13264 : Fin 1 → Cell := oneBank p13264 ray13264
theorem signs13264 : ∀ j, Signs p13264 (bank13264 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13265 := params 16
abbrev ray13265 := rays 16
def bank13265 : Fin 1 → Cell := oneBank p13265 ray13265
theorem signs13265 : ∀ j, Signs p13265 (bank13265 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13266 := params 17
abbrev ray13266 := rays 17
def bank13266 : Fin 1 → Cell := oneBank p13266 ray13266
theorem signs13266 : ∀ j, Signs p13266 (bank13266 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13267 := params 18
abbrev ray13267 := rays 18
def bank13267 : Fin 1 → Cell := oneBank p13267 ray13267
theorem signs13267 : ∀ j, Signs p13267 (bank13267 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13268 := params 19
abbrev ray13268 := rays 19
def bank13268 : Fin 1 → Cell := oneBank p13268 ray13268
theorem signs13268 : ∀ j, Signs p13268 (bank13268 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13269 := params 20
abbrev ray13269 := rays 20
def bank13269 : Fin 1 → Cell := oneBank p13269 ray13269
theorem signs13269 : ∀ j, Signs p13269 (bank13269 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13270 := params 21
abbrev ray13270 := rays 21
def bank13270 : Fin 1 → Cell := oneBank p13270 ray13270
theorem signs13270 : ∀ j, Signs p13270 (bank13270 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13271 := params 22
abbrev ray13271 := rays 22
def bank13271 : Fin 1 → Cell := oneBank p13271 ray13271
theorem signs13271 : ∀ j, Signs p13271 (bank13271 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13272 := params 23
abbrev ray13272 := rays 23
def bank13272 : Fin 1 → Cell := oneBank p13272 ray13272
theorem signs13272 : ∀ j, Signs p13272 (bank13272 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13273 := params 24
abbrev ray13273 := rays 24
def bank13273 : Fin 1 → Cell := oneBank p13273 ray13273
theorem signs13273 : ∀ j, Signs p13273 (bank13273 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13274 := params 25
abbrev ray13274 := rays 25
def bank13274 : Fin 1 → Cell := oneBank p13274 ray13274
theorem signs13274 : ∀ j, Signs p13274 (bank13274 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13275 := params 26
abbrev ray13275 := rays 26
def bank13275 : Fin 1 → Cell := oneBank p13275 ray13275
theorem signs13275 : ∀ j, Signs p13275 (bank13275 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13276 := params 27
abbrev ray13276 := rays 27
def bank13276 : Fin 1 → Cell := oneBank p13276 ray13276
theorem signs13276 : ∀ j, Signs p13276 (bank13276 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13277 := params 28
abbrev ray13277 := rays 28
def bank13277 : Fin 1 → Cell := oneBank p13277 ray13277
theorem signs13277 : ∀ j, Signs p13277 (bank13277 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13278 := params 29
abbrev ray13278 := rays 29
def bank13278 : Fin 1 → Cell := oneBank p13278 ray13278
theorem signs13278 : ∀ j, Signs p13278 (bank13278 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13279 := params 30
abbrev ray13279 := rays 30
def bank13279 : Fin 1 → Cell := oneBank p13279 ray13279
theorem signs13279 : ∀ j, Signs p13279 (bank13279 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13280 := params 31
abbrev ray13280 := rays 31
def bank13280 : Fin 1 → Cell := oneBank p13280 ray13280
theorem signs13280 : ∀ j, Signs p13280 (bank13280 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13249_13280
