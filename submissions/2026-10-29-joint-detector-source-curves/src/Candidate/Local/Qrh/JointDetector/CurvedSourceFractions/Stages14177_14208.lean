/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14177_14208
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95769713622696,95769269551962,95768825465046,95768381361947,95767937242667,95767493107205,95767048955561,95766604787736,95766160603730,95765716403542,95765272187174,95764827954625,95764383705895,95763939440985,95763495159895,95763050862625,95762606549175,95762162219545,95761717873735,95761273511746,95760829133578,95760384739231,95759940328705,95759495902000,95759051459117,95758607000056,95758162524816,95757718033398,95757273525803,95756829002030,95756384462079,95755939905951,95755495333646]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14176+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14177 := params 0
abbrev ray14177 := rays 0
def bank14177 : Fin 1 → Cell := oneBank p14177 ray14177
theorem signs14177 : ∀ j, Signs p14177 (bank14177 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14178 := params 1
abbrev ray14178 := rays 1
def bank14178 : Fin 1 → Cell := oneBank p14178 ray14178
theorem signs14178 : ∀ j, Signs p14178 (bank14178 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14179 := params 2
abbrev ray14179 := rays 2
def bank14179 : Fin 1 → Cell := oneBank p14179 ray14179
theorem signs14179 : ∀ j, Signs p14179 (bank14179 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14180 := params 3
abbrev ray14180 := rays 3
def bank14180 : Fin 1 → Cell := oneBank p14180 ray14180
theorem signs14180 : ∀ j, Signs p14180 (bank14180 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14181 := params 4
abbrev ray14181 := rays 4
def bank14181 : Fin 1 → Cell := oneBank p14181 ray14181
theorem signs14181 : ∀ j, Signs p14181 (bank14181 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14182 := params 5
abbrev ray14182 := rays 5
def bank14182 : Fin 1 → Cell := oneBank p14182 ray14182
theorem signs14182 : ∀ j, Signs p14182 (bank14182 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14183 := params 6
abbrev ray14183 := rays 6
def bank14183 : Fin 1 → Cell := oneBank p14183 ray14183
theorem signs14183 : ∀ j, Signs p14183 (bank14183 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14184 := params 7
abbrev ray14184 := rays 7
def bank14184 : Fin 1 → Cell := oneBank p14184 ray14184
theorem signs14184 : ∀ j, Signs p14184 (bank14184 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14185 := params 8
abbrev ray14185 := rays 8
def bank14185 : Fin 1 → Cell := oneBank p14185 ray14185
theorem signs14185 : ∀ j, Signs p14185 (bank14185 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14186 := params 9
abbrev ray14186 := rays 9
def bank14186 : Fin 1 → Cell := oneBank p14186 ray14186
theorem signs14186 : ∀ j, Signs p14186 (bank14186 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14187 := params 10
abbrev ray14187 := rays 10
def bank14187 : Fin 1 → Cell := oneBank p14187 ray14187
theorem signs14187 : ∀ j, Signs p14187 (bank14187 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14188 := params 11
abbrev ray14188 := rays 11
def bank14188 : Fin 1 → Cell := oneBank p14188 ray14188
theorem signs14188 : ∀ j, Signs p14188 (bank14188 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14189 := params 12
abbrev ray14189 := rays 12
def bank14189 : Fin 1 → Cell := oneBank p14189 ray14189
theorem signs14189 : ∀ j, Signs p14189 (bank14189 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14190 := params 13
abbrev ray14190 := rays 13
def bank14190 : Fin 1 → Cell := oneBank p14190 ray14190
theorem signs14190 : ∀ j, Signs p14190 (bank14190 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14191 := params 14
abbrev ray14191 := rays 14
def bank14191 : Fin 1 → Cell := oneBank p14191 ray14191
theorem signs14191 : ∀ j, Signs p14191 (bank14191 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14192 := params 15
abbrev ray14192 := rays 15
def bank14192 : Fin 1 → Cell := oneBank p14192 ray14192
theorem signs14192 : ∀ j, Signs p14192 (bank14192 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14193 := params 16
abbrev ray14193 := rays 16
def bank14193 : Fin 1 → Cell := oneBank p14193 ray14193
theorem signs14193 : ∀ j, Signs p14193 (bank14193 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14194 := params 17
abbrev ray14194 := rays 17
def bank14194 : Fin 1 → Cell := oneBank p14194 ray14194
theorem signs14194 : ∀ j, Signs p14194 (bank14194 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14195 := params 18
abbrev ray14195 := rays 18
def bank14195 : Fin 1 → Cell := oneBank p14195 ray14195
theorem signs14195 : ∀ j, Signs p14195 (bank14195 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14196 := params 19
abbrev ray14196 := rays 19
def bank14196 : Fin 1 → Cell := oneBank p14196 ray14196
theorem signs14196 : ∀ j, Signs p14196 (bank14196 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14197 := params 20
abbrev ray14197 := rays 20
def bank14197 : Fin 1 → Cell := oneBank p14197 ray14197
theorem signs14197 : ∀ j, Signs p14197 (bank14197 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14198 := params 21
abbrev ray14198 := rays 21
def bank14198 : Fin 1 → Cell := oneBank p14198 ray14198
theorem signs14198 : ∀ j, Signs p14198 (bank14198 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14199 := params 22
abbrev ray14199 := rays 22
def bank14199 : Fin 1 → Cell := oneBank p14199 ray14199
theorem signs14199 : ∀ j, Signs p14199 (bank14199 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14200 := params 23
abbrev ray14200 := rays 23
def bank14200 : Fin 1 → Cell := oneBank p14200 ray14200
theorem signs14200 : ∀ j, Signs p14200 (bank14200 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14201 := params 24
abbrev ray14201 := rays 24
def bank14201 : Fin 1 → Cell := oneBank p14201 ray14201
theorem signs14201 : ∀ j, Signs p14201 (bank14201 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14202 := params 25
abbrev ray14202 := rays 25
def bank14202 : Fin 1 → Cell := oneBank p14202 ray14202
theorem signs14202 : ∀ j, Signs p14202 (bank14202 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14203 := params 26
abbrev ray14203 := rays 26
def bank14203 : Fin 1 → Cell := oneBank p14203 ray14203
theorem signs14203 : ∀ j, Signs p14203 (bank14203 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14204 := params 27
abbrev ray14204 := rays 27
def bank14204 : Fin 1 → Cell := oneBank p14204 ray14204
theorem signs14204 : ∀ j, Signs p14204 (bank14204 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14205 := params 28
abbrev ray14205 := rays 28
def bank14205 : Fin 1 → Cell := oneBank p14205 ray14205
theorem signs14205 : ∀ j, Signs p14205 (bank14205 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14206 := params 29
abbrev ray14206 := rays 29
def bank14206 : Fin 1 → Cell := oneBank p14206 ray14206
theorem signs14206 : ∀ j, Signs p14206 (bank14206 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14207 := params 30
abbrev ray14207 := rays 30
def bank14207 : Fin 1 → Cell := oneBank p14207 ray14207
theorem signs14207 : ∀ j, Signs p14207 (bank14207 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14208 := params 31
abbrev ray14208 := rays 31
def bank14208 : Fin 1 → Cell := oneBank p14208 ray14208
theorem signs14208 : ∀ j, Signs p14208 (bank14208 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14177_14208
