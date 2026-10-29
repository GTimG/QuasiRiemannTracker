/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13185_13216
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96202230452255,96201802531315,96201374593985,96200946640265,96200518670156,96200090683657,96199662680769,96199234661493,96198806625828,96198378573775,96197950505334,96197522420505,96197094319288,96196666201684,96196238067693,96195809917315,96195381750551,96194953567400,96194525367863,96194097151941,96193668919633,96193240670940,96192812405862,96192384124399,96191955826551,96191527512319,96191099181703,96190670834703,96190242471319,96189814091552,96189385695402,96188957282869,96188528853954]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13184+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13185 := params 0
abbrev ray13185 := rays 0
def bank13185 : Fin 1 → Cell := oneBank p13185 ray13185
theorem signs13185 : ∀ j, Signs p13185 (bank13185 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13186 := params 1
abbrev ray13186 := rays 1
def bank13186 : Fin 1 → Cell := oneBank p13186 ray13186
theorem signs13186 : ∀ j, Signs p13186 (bank13186 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13187 := params 2
abbrev ray13187 := rays 2
def bank13187 : Fin 1 → Cell := oneBank p13187 ray13187
theorem signs13187 : ∀ j, Signs p13187 (bank13187 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13188 := params 3
abbrev ray13188 := rays 3
def bank13188 : Fin 1 → Cell := oneBank p13188 ray13188
theorem signs13188 : ∀ j, Signs p13188 (bank13188 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13189 := params 4
abbrev ray13189 := rays 4
def bank13189 : Fin 1 → Cell := oneBank p13189 ray13189
theorem signs13189 : ∀ j, Signs p13189 (bank13189 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13190 := params 5
abbrev ray13190 := rays 5
def bank13190 : Fin 1 → Cell := oneBank p13190 ray13190
theorem signs13190 : ∀ j, Signs p13190 (bank13190 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13191 := params 6
abbrev ray13191 := rays 6
def bank13191 : Fin 1 → Cell := oneBank p13191 ray13191
theorem signs13191 : ∀ j, Signs p13191 (bank13191 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13192 := params 7
abbrev ray13192 := rays 7
def bank13192 : Fin 1 → Cell := oneBank p13192 ray13192
theorem signs13192 : ∀ j, Signs p13192 (bank13192 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13193 := params 8
abbrev ray13193 := rays 8
def bank13193 : Fin 1 → Cell := oneBank p13193 ray13193
theorem signs13193 : ∀ j, Signs p13193 (bank13193 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13194 := params 9
abbrev ray13194 := rays 9
def bank13194 : Fin 1 → Cell := oneBank p13194 ray13194
theorem signs13194 : ∀ j, Signs p13194 (bank13194 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13195 := params 10
abbrev ray13195 := rays 10
def bank13195 : Fin 1 → Cell := oneBank p13195 ray13195
theorem signs13195 : ∀ j, Signs p13195 (bank13195 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13196 := params 11
abbrev ray13196 := rays 11
def bank13196 : Fin 1 → Cell := oneBank p13196 ray13196
theorem signs13196 : ∀ j, Signs p13196 (bank13196 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13197 := params 12
abbrev ray13197 := rays 12
def bank13197 : Fin 1 → Cell := oneBank p13197 ray13197
theorem signs13197 : ∀ j, Signs p13197 (bank13197 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13198 := params 13
abbrev ray13198 := rays 13
def bank13198 : Fin 1 → Cell := oneBank p13198 ray13198
theorem signs13198 : ∀ j, Signs p13198 (bank13198 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13199 := params 14
abbrev ray13199 := rays 14
def bank13199 : Fin 1 → Cell := oneBank p13199 ray13199
theorem signs13199 : ∀ j, Signs p13199 (bank13199 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13200 := params 15
abbrev ray13200 := rays 15
def bank13200 : Fin 1 → Cell := oneBank p13200 ray13200
theorem signs13200 : ∀ j, Signs p13200 (bank13200 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13201 := params 16
abbrev ray13201 := rays 16
def bank13201 : Fin 1 → Cell := oneBank p13201 ray13201
theorem signs13201 : ∀ j, Signs p13201 (bank13201 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13202 := params 17
abbrev ray13202 := rays 17
def bank13202 : Fin 1 → Cell := oneBank p13202 ray13202
theorem signs13202 : ∀ j, Signs p13202 (bank13202 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13203 := params 18
abbrev ray13203 := rays 18
def bank13203 : Fin 1 → Cell := oneBank p13203 ray13203
theorem signs13203 : ∀ j, Signs p13203 (bank13203 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13204 := params 19
abbrev ray13204 := rays 19
def bank13204 : Fin 1 → Cell := oneBank p13204 ray13204
theorem signs13204 : ∀ j, Signs p13204 (bank13204 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13205 := params 20
abbrev ray13205 := rays 20
def bank13205 : Fin 1 → Cell := oneBank p13205 ray13205
theorem signs13205 : ∀ j, Signs p13205 (bank13205 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13206 := params 21
abbrev ray13206 := rays 21
def bank13206 : Fin 1 → Cell := oneBank p13206 ray13206
theorem signs13206 : ∀ j, Signs p13206 (bank13206 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13207 := params 22
abbrev ray13207 := rays 22
def bank13207 : Fin 1 → Cell := oneBank p13207 ray13207
theorem signs13207 : ∀ j, Signs p13207 (bank13207 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13208 := params 23
abbrev ray13208 := rays 23
def bank13208 : Fin 1 → Cell := oneBank p13208 ray13208
theorem signs13208 : ∀ j, Signs p13208 (bank13208 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13209 := params 24
abbrev ray13209 := rays 24
def bank13209 : Fin 1 → Cell := oneBank p13209 ray13209
theorem signs13209 : ∀ j, Signs p13209 (bank13209 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13210 := params 25
abbrev ray13210 := rays 25
def bank13210 : Fin 1 → Cell := oneBank p13210 ray13210
theorem signs13210 : ∀ j, Signs p13210 (bank13210 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13211 := params 26
abbrev ray13211 := rays 26
def bank13211 : Fin 1 → Cell := oneBank p13211 ray13211
theorem signs13211 : ∀ j, Signs p13211 (bank13211 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13212 := params 27
abbrev ray13212 := rays 27
def bank13212 : Fin 1 → Cell := oneBank p13212 ray13212
theorem signs13212 : ∀ j, Signs p13212 (bank13212 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13213 := params 28
abbrev ray13213 := rays 28
def bank13213 : Fin 1 → Cell := oneBank p13213 ray13213
theorem signs13213 : ∀ j, Signs p13213 (bank13213 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13214 := params 29
abbrev ray13214 := rays 29
def bank13214 : Fin 1 → Cell := oneBank p13214 ray13214
theorem signs13214 : ∀ j, Signs p13214 (bank13214 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13215 := params 30
abbrev ray13215 := rays 30
def bank13215 : Fin 1 → Cell := oneBank p13215 ray13215
theorem signs13215 : ∀ j, Signs p13215 (bank13215 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13216 := params 31
abbrev ray13216 := rays 31
def bank13216 : Fin 1 → Cell := oneBank p13216 ray13216
theorem signs13216 : ∀ j, Signs p13216 (bank13216 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13185_13216
