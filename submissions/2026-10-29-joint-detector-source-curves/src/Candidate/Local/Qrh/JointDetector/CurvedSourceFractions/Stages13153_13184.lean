/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages13153_13184
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96215915266942,96215487870613,96215060457886,96214633028761,96214205583238,96213778121318,96213350643001,96212923148288,96212495637178,96212068109672,96211640565770,96211213005472,96210785428779,96210357835691,96209930226208,96209502600330,96209074958058,96208647299391,96208219624330,96207791932876,96207364225028,96206936500787,96206508760153,96206081003126,96205653229707,96205225439896,96204797633693,96204369811098,96203941972111,96203514116733,96203086244964,96202658356805,96202230452255]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (13152+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p13153 := params 0
abbrev ray13153 := rays 0
def bank13153 : Fin 1 → Cell := oneBank p13153 ray13153
theorem signs13153 : ∀ j, Signs p13153 (bank13153 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13154 := params 1
abbrev ray13154 := rays 1
def bank13154 : Fin 1 → Cell := oneBank p13154 ray13154
theorem signs13154 : ∀ j, Signs p13154 (bank13154 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13155 := params 2
abbrev ray13155 := rays 2
def bank13155 : Fin 1 → Cell := oneBank p13155 ray13155
theorem signs13155 : ∀ j, Signs p13155 (bank13155 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13156 := params 3
abbrev ray13156 := rays 3
def bank13156 : Fin 1 → Cell := oneBank p13156 ray13156
theorem signs13156 : ∀ j, Signs p13156 (bank13156 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13157 := params 4
abbrev ray13157 := rays 4
def bank13157 : Fin 1 → Cell := oneBank p13157 ray13157
theorem signs13157 : ∀ j, Signs p13157 (bank13157 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13158 := params 5
abbrev ray13158 := rays 5
def bank13158 : Fin 1 → Cell := oneBank p13158 ray13158
theorem signs13158 : ∀ j, Signs p13158 (bank13158 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13159 := params 6
abbrev ray13159 := rays 6
def bank13159 : Fin 1 → Cell := oneBank p13159 ray13159
theorem signs13159 : ∀ j, Signs p13159 (bank13159 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13160 := params 7
abbrev ray13160 := rays 7
def bank13160 : Fin 1 → Cell := oneBank p13160 ray13160
theorem signs13160 : ∀ j, Signs p13160 (bank13160 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13161 := params 8
abbrev ray13161 := rays 8
def bank13161 : Fin 1 → Cell := oneBank p13161 ray13161
theorem signs13161 : ∀ j, Signs p13161 (bank13161 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13162 := params 9
abbrev ray13162 := rays 9
def bank13162 : Fin 1 → Cell := oneBank p13162 ray13162
theorem signs13162 : ∀ j, Signs p13162 (bank13162 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13163 := params 10
abbrev ray13163 := rays 10
def bank13163 : Fin 1 → Cell := oneBank p13163 ray13163
theorem signs13163 : ∀ j, Signs p13163 (bank13163 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13164 := params 11
abbrev ray13164 := rays 11
def bank13164 : Fin 1 → Cell := oneBank p13164 ray13164
theorem signs13164 : ∀ j, Signs p13164 (bank13164 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13165 := params 12
abbrev ray13165 := rays 12
def bank13165 : Fin 1 → Cell := oneBank p13165 ray13165
theorem signs13165 : ∀ j, Signs p13165 (bank13165 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13166 := params 13
abbrev ray13166 := rays 13
def bank13166 : Fin 1 → Cell := oneBank p13166 ray13166
theorem signs13166 : ∀ j, Signs p13166 (bank13166 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13167 := params 14
abbrev ray13167 := rays 14
def bank13167 : Fin 1 → Cell := oneBank p13167 ray13167
theorem signs13167 : ∀ j, Signs p13167 (bank13167 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13168 := params 15
abbrev ray13168 := rays 15
def bank13168 : Fin 1 → Cell := oneBank p13168 ray13168
theorem signs13168 : ∀ j, Signs p13168 (bank13168 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13169 := params 16
abbrev ray13169 := rays 16
def bank13169 : Fin 1 → Cell := oneBank p13169 ray13169
theorem signs13169 : ∀ j, Signs p13169 (bank13169 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13170 := params 17
abbrev ray13170 := rays 17
def bank13170 : Fin 1 → Cell := oneBank p13170 ray13170
theorem signs13170 : ∀ j, Signs p13170 (bank13170 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13171 := params 18
abbrev ray13171 := rays 18
def bank13171 : Fin 1 → Cell := oneBank p13171 ray13171
theorem signs13171 : ∀ j, Signs p13171 (bank13171 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13172 := params 19
abbrev ray13172 := rays 19
def bank13172 : Fin 1 → Cell := oneBank p13172 ray13172
theorem signs13172 : ∀ j, Signs p13172 (bank13172 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13173 := params 20
abbrev ray13173 := rays 20
def bank13173 : Fin 1 → Cell := oneBank p13173 ray13173
theorem signs13173 : ∀ j, Signs p13173 (bank13173 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13174 := params 21
abbrev ray13174 := rays 21
def bank13174 : Fin 1 → Cell := oneBank p13174 ray13174
theorem signs13174 : ∀ j, Signs p13174 (bank13174 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13175 := params 22
abbrev ray13175 := rays 22
def bank13175 : Fin 1 → Cell := oneBank p13175 ray13175
theorem signs13175 : ∀ j, Signs p13175 (bank13175 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13176 := params 23
abbrev ray13176 := rays 23
def bank13176 : Fin 1 → Cell := oneBank p13176 ray13176
theorem signs13176 : ∀ j, Signs p13176 (bank13176 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13177 := params 24
abbrev ray13177 := rays 24
def bank13177 : Fin 1 → Cell := oneBank p13177 ray13177
theorem signs13177 : ∀ j, Signs p13177 (bank13177 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13178 := params 25
abbrev ray13178 := rays 25
def bank13178 : Fin 1 → Cell := oneBank p13178 ray13178
theorem signs13178 : ∀ j, Signs p13178 (bank13178 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13179 := params 26
abbrev ray13179 := rays 26
def bank13179 : Fin 1 → Cell := oneBank p13179 ray13179
theorem signs13179 : ∀ j, Signs p13179 (bank13179 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13180 := params 27
abbrev ray13180 := rays 27
def bank13180 : Fin 1 → Cell := oneBank p13180 ray13180
theorem signs13180 : ∀ j, Signs p13180 (bank13180 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13181 := params 28
abbrev ray13181 := rays 28
def bank13181 : Fin 1 → Cell := oneBank p13181 ray13181
theorem signs13181 : ∀ j, Signs p13181 (bank13181 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13182 := params 29
abbrev ray13182 := rays 29
def bank13182 : Fin 1 → Cell := oneBank p13182 ray13182
theorem signs13182 : ∀ j, Signs p13182 (bank13182 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13183 := params 30
abbrev ray13183 := rays 30
def bank13183 : Fin 1 → Cell := oneBank p13183 ray13183
theorem signs13183 : ∀ j, Signs p13183 (bank13183 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13184 := params 31
abbrev ray13184 := rays 31
def bank13184 : Fin 1 → Cell := oneBank p13184 ray13184
theorem signs13184 : ∀ j, Signs p13184 (bank13184 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages13153_13184
