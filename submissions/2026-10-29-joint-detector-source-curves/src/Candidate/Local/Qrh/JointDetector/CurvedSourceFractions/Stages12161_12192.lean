/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12161_12192
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96631266358273,96630856979145,96630447580731,96630038163030,96629628726043,96629219269771,96628809794214,96628400299372,96627990785246,96627581251836,96627171699143,96626762127167,96626352535909,96625942925369,96625533295547,96625123646444,96624713978060,96624304290396,96623894583452,96623484857228,96623075111725,96622665346943,96622255562883,96621845759545,96621435936930,96621026095038,96620616233869,96620206353424,96619796453703,96619386534707,96618976596436,96618566638891,96618156662072]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12160+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12161 := params 0
abbrev ray12161 := rays 0
def bank12161 : Fin 2 → Cell := twoBank p12161 ray12161
theorem signs12161 : ∀ j, Signs p12161 (bank12161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12162 := params 1
abbrev ray12162 := rays 1
def bank12162 : Fin 2 → Cell := twoBank p12162 ray12162
theorem signs12162 : ∀ j, Signs p12162 (bank12162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12163 := params 2
abbrev ray12163 := rays 2
def bank12163 : Fin 2 → Cell := twoBank p12163 ray12163
theorem signs12163 : ∀ j, Signs p12163 (bank12163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12164 := params 3
abbrev ray12164 := rays 3
def bank12164 : Fin 2 → Cell := twoBank p12164 ray12164
theorem signs12164 : ∀ j, Signs p12164 (bank12164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12165 := params 4
abbrev ray12165 := rays 4
def bank12165 : Fin 2 → Cell := twoBank p12165 ray12165
theorem signs12165 : ∀ j, Signs p12165 (bank12165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12166 := params 5
abbrev ray12166 := rays 5
def bank12166 : Fin 2 → Cell := twoBank p12166 ray12166
theorem signs12166 : ∀ j, Signs p12166 (bank12166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12167 := params 6
abbrev ray12167 := rays 6
def bank12167 : Fin 2 → Cell := twoBank p12167 ray12167
theorem signs12167 : ∀ j, Signs p12167 (bank12167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12168 := params 7
abbrev ray12168 := rays 7
def bank12168 : Fin 2 → Cell := twoBank p12168 ray12168
theorem signs12168 : ∀ j, Signs p12168 (bank12168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12169 := params 8
abbrev ray12169 := rays 8
def bank12169 : Fin 2 → Cell := twoBank p12169 ray12169
theorem signs12169 : ∀ j, Signs p12169 (bank12169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12170 := params 9
abbrev ray12170 := rays 9
def bank12170 : Fin 2 → Cell := twoBank p12170 ray12170
theorem signs12170 : ∀ j, Signs p12170 (bank12170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12171 := params 10
abbrev ray12171 := rays 10
def bank12171 : Fin 2 → Cell := twoBank p12171 ray12171
theorem signs12171 : ∀ j, Signs p12171 (bank12171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12172 := params 11
abbrev ray12172 := rays 11
def bank12172 : Fin 2 → Cell := twoBank p12172 ray12172
theorem signs12172 : ∀ j, Signs p12172 (bank12172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12173 := params 12
abbrev ray12173 := rays 12
def bank12173 : Fin 2 → Cell := twoBank p12173 ray12173
theorem signs12173 : ∀ j, Signs p12173 (bank12173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12174 := params 13
abbrev ray12174 := rays 13
def bank12174 : Fin 2 → Cell := twoBank p12174 ray12174
theorem signs12174 : ∀ j, Signs p12174 (bank12174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12175 := params 14
abbrev ray12175 := rays 14
def bank12175 : Fin 2 → Cell := twoBank p12175 ray12175
theorem signs12175 : ∀ j, Signs p12175 (bank12175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12176 := params 15
abbrev ray12176 := rays 15
def bank12176 : Fin 2 → Cell := twoBank p12176 ray12176
theorem signs12176 : ∀ j, Signs p12176 (bank12176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12177 := params 16
abbrev ray12177 := rays 16
def bank12177 : Fin 2 → Cell := twoBank p12177 ray12177
theorem signs12177 : ∀ j, Signs p12177 (bank12177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12178 := params 17
abbrev ray12178 := rays 17
def bank12178 : Fin 2 → Cell := twoBank p12178 ray12178
theorem signs12178 : ∀ j, Signs p12178 (bank12178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12179 := params 18
abbrev ray12179 := rays 18
def bank12179 : Fin 2 → Cell := twoBank p12179 ray12179
theorem signs12179 : ∀ j, Signs p12179 (bank12179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12180 := params 19
abbrev ray12180 := rays 19
def bank12180 : Fin 2 → Cell := twoBank p12180 ray12180
theorem signs12180 : ∀ j, Signs p12180 (bank12180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12181 := params 20
abbrev ray12181 := rays 20
def bank12181 : Fin 2 → Cell := twoBank p12181 ray12181
theorem signs12181 : ∀ j, Signs p12181 (bank12181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12182 := params 21
abbrev ray12182 := rays 21
def bank12182 : Fin 2 → Cell := twoBank p12182 ray12182
theorem signs12182 : ∀ j, Signs p12182 (bank12182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12183 := params 22
abbrev ray12183 := rays 22
def bank12183 : Fin 2 → Cell := twoBank p12183 ray12183
theorem signs12183 : ∀ j, Signs p12183 (bank12183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12184 := params 23
abbrev ray12184 := rays 23
def bank12184 : Fin 2 → Cell := twoBank p12184 ray12184
theorem signs12184 : ∀ j, Signs p12184 (bank12184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12185 := params 24
abbrev ray12185 := rays 24
def bank12185 : Fin 2 → Cell := twoBank p12185 ray12185
theorem signs12185 : ∀ j, Signs p12185 (bank12185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12186 := params 25
abbrev ray12186 := rays 25
def bank12186 : Fin 2 → Cell := twoBank p12186 ray12186
theorem signs12186 : ∀ j, Signs p12186 (bank12186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12187 := params 26
abbrev ray12187 := rays 26
def bank12187 : Fin 2 → Cell := twoBank p12187 ray12187
theorem signs12187 : ∀ j, Signs p12187 (bank12187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12188 := params 27
abbrev ray12188 := rays 27
def bank12188 : Fin 2 → Cell := twoBank p12188 ray12188
theorem signs12188 : ∀ j, Signs p12188 (bank12188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12189 := params 28
abbrev ray12189 := rays 28
def bank12189 : Fin 2 → Cell := twoBank p12189 ray12189
theorem signs12189 : ∀ j, Signs p12189 (bank12189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12190 := params 29
abbrev ray12190 := rays 29
def bank12190 : Fin 2 → Cell := twoBank p12190 ray12190
theorem signs12190 : ∀ j, Signs p12190 (bank12190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12191 := params 30
abbrev ray12191 := rays 30
def bank12191 : Fin 2 → Cell := twoBank p12191 ray12191
theorem signs12191 : ∀ j, Signs p12191 (bank12191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12192 := params 31
abbrev ray12192 := rays 31
def bank12192 : Fin 2 → Cell := twoBank p12192 ray12192
theorem signs12192 : ∀ j, Signs p12192 (bank12192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12161_12192
