/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages10145_10176
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97416744679130,97416375120209,97416005541031,97415635941595,97415266321903,97414896681955,97414527021751,97414157341292,97413787640579,97413417919612,97413048178391,97412678416917,97412308635191,97411938833213,97411569010984,97411199168505,97410829305775,97410459422796,97410089519568,97409719596091,97409349652366,97408979688394,97408609704175,97408239699710,97407869674999,97407499630043,97407129564842,97406759479397,97406389373708,97406019247776,97405649101602,97405278935186,97404908748528]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (10144+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p10145 := params 0
abbrev ray10145 := rays 0
def bank10145 : Fin 2 → Cell := twoBank p10145 ray10145
theorem signs10145 : ∀ j, Signs p10145 (bank10145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10146 := params 1
abbrev ray10146 := rays 1
def bank10146 : Fin 2 → Cell := twoBank p10146 ray10146
theorem signs10146 : ∀ j, Signs p10146 (bank10146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10147 := params 2
abbrev ray10147 := rays 2
def bank10147 : Fin 2 → Cell := twoBank p10147 ray10147
theorem signs10147 : ∀ j, Signs p10147 (bank10147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10148 := params 3
abbrev ray10148 := rays 3
def bank10148 : Fin 2 → Cell := twoBank p10148 ray10148
theorem signs10148 : ∀ j, Signs p10148 (bank10148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10149 := params 4
abbrev ray10149 := rays 4
def bank10149 : Fin 2 → Cell := twoBank p10149 ray10149
theorem signs10149 : ∀ j, Signs p10149 (bank10149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10150 := params 5
abbrev ray10150 := rays 5
def bank10150 : Fin 2 → Cell := twoBank p10150 ray10150
theorem signs10150 : ∀ j, Signs p10150 (bank10150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10151 := params 6
abbrev ray10151 := rays 6
def bank10151 : Fin 2 → Cell := twoBank p10151 ray10151
theorem signs10151 : ∀ j, Signs p10151 (bank10151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10152 := params 7
abbrev ray10152 := rays 7
def bank10152 : Fin 2 → Cell := twoBank p10152 ray10152
theorem signs10152 : ∀ j, Signs p10152 (bank10152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10153 := params 8
abbrev ray10153 := rays 8
def bank10153 : Fin 2 → Cell := twoBank p10153 ray10153
theorem signs10153 : ∀ j, Signs p10153 (bank10153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10154 := params 9
abbrev ray10154 := rays 9
def bank10154 : Fin 2 → Cell := twoBank p10154 ray10154
theorem signs10154 : ∀ j, Signs p10154 (bank10154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10155 := params 10
abbrev ray10155 := rays 10
def bank10155 : Fin 2 → Cell := twoBank p10155 ray10155
theorem signs10155 : ∀ j, Signs p10155 (bank10155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10156 := params 11
abbrev ray10156 := rays 11
def bank10156 : Fin 2 → Cell := twoBank p10156 ray10156
theorem signs10156 : ∀ j, Signs p10156 (bank10156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10157 := params 12
abbrev ray10157 := rays 12
def bank10157 : Fin 2 → Cell := twoBank p10157 ray10157
theorem signs10157 : ∀ j, Signs p10157 (bank10157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10158 := params 13
abbrev ray10158 := rays 13
def bank10158 : Fin 2 → Cell := twoBank p10158 ray10158
theorem signs10158 : ∀ j, Signs p10158 (bank10158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10159 := params 14
abbrev ray10159 := rays 14
def bank10159 : Fin 2 → Cell := twoBank p10159 ray10159
theorem signs10159 : ∀ j, Signs p10159 (bank10159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10160 := params 15
abbrev ray10160 := rays 15
def bank10160 : Fin 2 → Cell := twoBank p10160 ray10160
theorem signs10160 : ∀ j, Signs p10160 (bank10160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10161 := params 16
abbrev ray10161 := rays 16
def bank10161 : Fin 2 → Cell := twoBank p10161 ray10161
theorem signs10161 : ∀ j, Signs p10161 (bank10161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10162 := params 17
abbrev ray10162 := rays 17
def bank10162 : Fin 2 → Cell := twoBank p10162 ray10162
theorem signs10162 : ∀ j, Signs p10162 (bank10162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10163 := params 18
abbrev ray10163 := rays 18
def bank10163 : Fin 2 → Cell := twoBank p10163 ray10163
theorem signs10163 : ∀ j, Signs p10163 (bank10163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10164 := params 19
abbrev ray10164 := rays 19
def bank10164 : Fin 2 → Cell := twoBank p10164 ray10164
theorem signs10164 : ∀ j, Signs p10164 (bank10164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10165 := params 20
abbrev ray10165 := rays 20
def bank10165 : Fin 2 → Cell := twoBank p10165 ray10165
theorem signs10165 : ∀ j, Signs p10165 (bank10165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10166 := params 21
abbrev ray10166 := rays 21
def bank10166 : Fin 2 → Cell := twoBank p10166 ray10166
theorem signs10166 : ∀ j, Signs p10166 (bank10166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10167 := params 22
abbrev ray10167 := rays 22
def bank10167 : Fin 2 → Cell := twoBank p10167 ray10167
theorem signs10167 : ∀ j, Signs p10167 (bank10167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10168 := params 23
abbrev ray10168 := rays 23
def bank10168 : Fin 2 → Cell := twoBank p10168 ray10168
theorem signs10168 : ∀ j, Signs p10168 (bank10168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10169 := params 24
abbrev ray10169 := rays 24
def bank10169 : Fin 2 → Cell := twoBank p10169 ray10169
theorem signs10169 : ∀ j, Signs p10169 (bank10169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10170 := params 25
abbrev ray10170 := rays 25
def bank10170 : Fin 2 → Cell := twoBank p10170 ray10170
theorem signs10170 : ∀ j, Signs p10170 (bank10170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10171 := params 26
abbrev ray10171 := rays 26
def bank10171 : Fin 2 → Cell := twoBank p10171 ray10171
theorem signs10171 : ∀ j, Signs p10171 (bank10171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10172 := params 27
abbrev ray10172 := rays 27
def bank10172 : Fin 2 → Cell := twoBank p10172 ray10172
theorem signs10172 : ∀ j, Signs p10172 (bank10172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10173 := params 28
abbrev ray10173 := rays 28
def bank10173 : Fin 2 → Cell := twoBank p10173 ray10173
theorem signs10173 : ∀ j, Signs p10173 (bank10173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10174 := params 29
abbrev ray10174 := rays 29
def bank10174 : Fin 2 → Cell := twoBank p10174 ray10174
theorem signs10174 : ∀ j, Signs p10174 (bank10174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10175 := params 30
abbrev ray10175 := rays 30
def bank10175 : Fin 2 → Cell := twoBank p10175 ray10175
theorem signs10175 : ∀ j, Signs p10175 (bank10175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p10176 := params 31
abbrev ray10176 := rays 31
def bank10176 : Fin 2 → Cell := twoBank p10176 ray10176
theorem signs10176 : ∀ j, Signs p10176 (bank10176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages10145_10176
