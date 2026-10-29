/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10177_10208
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97404908748528,97404538541629,97404168314490,97403798067111,97403427799493,97403057511636,97402687203541,97402316875208,97401946526638,97401576157832,97401205768790,97400835359512,97400464929999,97400094480252,97399724010271,97399353520057,97398983009610,97398612478931,97398241928020,97397871356878,97397500765505,97397130153902,97396759522070,97396388870009,97396018197719,97395647505201,97395276792456,97394906059484,97394535306286,97394164532862,97393793739213,97393422925339,97393052091241]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10176+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10177 := params 0
abbrev ray10177 := rays 0
def bank10177 : Fin 2 → Cell := twoBank p10177 ray10177
theorem signs10177 : ∀ j, Signs p10177 (bank10177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10178 := params 1
abbrev ray10178 := rays 1
def bank10178 : Fin 2 → Cell := twoBank p10178 ray10178
theorem signs10178 : ∀ j, Signs p10178 (bank10178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10179 := params 2
abbrev ray10179 := rays 2
def bank10179 : Fin 2 → Cell := twoBank p10179 ray10179
theorem signs10179 : ∀ j, Signs p10179 (bank10179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10180 := params 3
abbrev ray10180 := rays 3
def bank10180 : Fin 2 → Cell := twoBank p10180 ray10180
theorem signs10180 : ∀ j, Signs p10180 (bank10180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10181 := params 4
abbrev ray10181 := rays 4
def bank10181 : Fin 2 → Cell := twoBank p10181 ray10181
theorem signs10181 : ∀ j, Signs p10181 (bank10181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10182 := params 5
abbrev ray10182 := rays 5
def bank10182 : Fin 2 → Cell := twoBank p10182 ray10182
theorem signs10182 : ∀ j, Signs p10182 (bank10182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10183 := params 6
abbrev ray10183 := rays 6
def bank10183 : Fin 2 → Cell := twoBank p10183 ray10183
theorem signs10183 : ∀ j, Signs p10183 (bank10183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10184 := params 7
abbrev ray10184 := rays 7
def bank10184 : Fin 2 → Cell := twoBank p10184 ray10184
theorem signs10184 : ∀ j, Signs p10184 (bank10184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10185 := params 8
abbrev ray10185 := rays 8
def bank10185 : Fin 2 → Cell := twoBank p10185 ray10185
theorem signs10185 : ∀ j, Signs p10185 (bank10185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10186 := params 9
abbrev ray10186 := rays 9
def bank10186 : Fin 2 → Cell := twoBank p10186 ray10186
theorem signs10186 : ∀ j, Signs p10186 (bank10186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10187 := params 10
abbrev ray10187 := rays 10
def bank10187 : Fin 2 → Cell := twoBank p10187 ray10187
theorem signs10187 : ∀ j, Signs p10187 (bank10187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10188 := params 11
abbrev ray10188 := rays 11
def bank10188 : Fin 2 → Cell := twoBank p10188 ray10188
theorem signs10188 : ∀ j, Signs p10188 (bank10188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10189 := params 12
abbrev ray10189 := rays 12
def bank10189 : Fin 2 → Cell := twoBank p10189 ray10189
theorem signs10189 : ∀ j, Signs p10189 (bank10189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10190 := params 13
abbrev ray10190 := rays 13
def bank10190 : Fin 2 → Cell := twoBank p10190 ray10190
theorem signs10190 : ∀ j, Signs p10190 (bank10190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10191 := params 14
abbrev ray10191 := rays 14
def bank10191 : Fin 2 → Cell := twoBank p10191 ray10191
theorem signs10191 : ∀ j, Signs p10191 (bank10191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10192 := params 15
abbrev ray10192 := rays 15
def bank10192 : Fin 2 → Cell := twoBank p10192 ray10192
theorem signs10192 : ∀ j, Signs p10192 (bank10192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10193 := params 16
abbrev ray10193 := rays 16
def bank10193 : Fin 2 → Cell := twoBank p10193 ray10193
theorem signs10193 : ∀ j, Signs p10193 (bank10193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10194 := params 17
abbrev ray10194 := rays 17
def bank10194 : Fin 2 → Cell := twoBank p10194 ray10194
theorem signs10194 : ∀ j, Signs p10194 (bank10194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10195 := params 18
abbrev ray10195 := rays 18
def bank10195 : Fin 2 → Cell := twoBank p10195 ray10195
theorem signs10195 : ∀ j, Signs p10195 (bank10195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10196 := params 19
abbrev ray10196 := rays 19
def bank10196 : Fin 2 → Cell := twoBank p10196 ray10196
theorem signs10196 : ∀ j, Signs p10196 (bank10196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10197 := params 20
abbrev ray10197 := rays 20
def bank10197 : Fin 2 → Cell := twoBank p10197 ray10197
theorem signs10197 : ∀ j, Signs p10197 (bank10197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10198 := params 21
abbrev ray10198 := rays 21
def bank10198 : Fin 2 → Cell := twoBank p10198 ray10198
theorem signs10198 : ∀ j, Signs p10198 (bank10198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10199 := params 22
abbrev ray10199 := rays 22
def bank10199 : Fin 2 → Cell := twoBank p10199 ray10199
theorem signs10199 : ∀ j, Signs p10199 (bank10199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10200 := params 23
abbrev ray10200 := rays 23
def bank10200 : Fin 2 → Cell := twoBank p10200 ray10200
theorem signs10200 : ∀ j, Signs p10200 (bank10200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10201 := params 24
abbrev ray10201 := rays 24
def bank10201 : Fin 2 → Cell := twoBank p10201 ray10201
theorem signs10201 : ∀ j, Signs p10201 (bank10201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10202 := params 25
abbrev ray10202 := rays 25
def bank10202 : Fin 2 → Cell := twoBank p10202 ray10202
theorem signs10202 : ∀ j, Signs p10202 (bank10202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10203 := params 26
abbrev ray10203 := rays 26
def bank10203 : Fin 2 → Cell := twoBank p10203 ray10203
theorem signs10203 : ∀ j, Signs p10203 (bank10203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10204 := params 27
abbrev ray10204 := rays 27
def bank10204 : Fin 2 → Cell := twoBank p10204 ray10204
theorem signs10204 : ∀ j, Signs p10204 (bank10204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10205 := params 28
abbrev ray10205 := rays 28
def bank10205 : Fin 2 → Cell := twoBank p10205 ray10205
theorem signs10205 : ∀ j, Signs p10205 (bank10205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10206 := params 29
abbrev ray10206 := rays 29
def bank10206 : Fin 2 → Cell := twoBank p10206 ray10206
theorem signs10206 : ∀ j, Signs p10206 (bank10206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10207 := params 30
abbrev ray10207 := rays 30
def bank10207 : Fin 2 → Cell := twoBank p10207 ray10207
theorem signs10207 : ∀ j, Signs p10207 (bank10207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10208 := params 31
abbrev ray10208 := rays 31
def bank10208 : Fin 2 → Cell := twoBank p10208 ray10208
theorem signs10208 : ∀ j, Signs p10208 (bank10208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10177_10208
