/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages07169_07200
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98424195850715,98423889298167,98423582723421,98423276126479,98422969507341,98422662866009,98422356202483,98422049516763,98421742808851,98421436078747,98421129326452,98420822551967,98420515755292,98420208936429,98419902095378,98419595232140,98419288346715,98418981439105,98418674509310,98418367557331,98418060583168,98417753586823,98417446568296,98417139527588,98416832464700,98416525379633,98416218272387,98415911142963,98415603991362,98415296817585,98414989621632,98414682403504,98414375163202]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (7168+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p7169 := params 0
abbrev ray7169 := rays 0
def bank7169 : Fin 2 → Cell := twoBank p7169 ray7169
theorem signs7169 : ∀ j, Signs p7169 (bank7169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7170 := params 1
abbrev ray7170 := rays 1
def bank7170 : Fin 2 → Cell := twoBank p7170 ray7170
theorem signs7170 : ∀ j, Signs p7170 (bank7170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7171 := params 2
abbrev ray7171 := rays 2
def bank7171 : Fin 2 → Cell := twoBank p7171 ray7171
theorem signs7171 : ∀ j, Signs p7171 (bank7171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7172 := params 3
abbrev ray7172 := rays 3
def bank7172 : Fin 2 → Cell := twoBank p7172 ray7172
theorem signs7172 : ∀ j, Signs p7172 (bank7172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7173 := params 4
abbrev ray7173 := rays 4
def bank7173 : Fin 2 → Cell := twoBank p7173 ray7173
theorem signs7173 : ∀ j, Signs p7173 (bank7173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7174 := params 5
abbrev ray7174 := rays 5
def bank7174 : Fin 2 → Cell := twoBank p7174 ray7174
theorem signs7174 : ∀ j, Signs p7174 (bank7174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7175 := params 6
abbrev ray7175 := rays 6
def bank7175 : Fin 2 → Cell := twoBank p7175 ray7175
theorem signs7175 : ∀ j, Signs p7175 (bank7175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7176 := params 7
abbrev ray7176 := rays 7
def bank7176 : Fin 2 → Cell := twoBank p7176 ray7176
theorem signs7176 : ∀ j, Signs p7176 (bank7176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7177 := params 8
abbrev ray7177 := rays 8
def bank7177 : Fin 2 → Cell := twoBank p7177 ray7177
theorem signs7177 : ∀ j, Signs p7177 (bank7177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7178 := params 9
abbrev ray7178 := rays 9
def bank7178 : Fin 2 → Cell := twoBank p7178 ray7178
theorem signs7178 : ∀ j, Signs p7178 (bank7178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7179 := params 10
abbrev ray7179 := rays 10
def bank7179 : Fin 2 → Cell := twoBank p7179 ray7179
theorem signs7179 : ∀ j, Signs p7179 (bank7179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7180 := params 11
abbrev ray7180 := rays 11
def bank7180 : Fin 2 → Cell := twoBank p7180 ray7180
theorem signs7180 : ∀ j, Signs p7180 (bank7180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7181 := params 12
abbrev ray7181 := rays 12
def bank7181 : Fin 2 → Cell := twoBank p7181 ray7181
theorem signs7181 : ∀ j, Signs p7181 (bank7181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7182 := params 13
abbrev ray7182 := rays 13
def bank7182 : Fin 2 → Cell := twoBank p7182 ray7182
theorem signs7182 : ∀ j, Signs p7182 (bank7182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7183 := params 14
abbrev ray7183 := rays 14
def bank7183 : Fin 2 → Cell := twoBank p7183 ray7183
theorem signs7183 : ∀ j, Signs p7183 (bank7183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7184 := params 15
abbrev ray7184 := rays 15
def bank7184 : Fin 2 → Cell := twoBank p7184 ray7184
theorem signs7184 : ∀ j, Signs p7184 (bank7184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7185 := params 16
abbrev ray7185 := rays 16
def bank7185 : Fin 2 → Cell := twoBank p7185 ray7185
theorem signs7185 : ∀ j, Signs p7185 (bank7185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7186 := params 17
abbrev ray7186 := rays 17
def bank7186 : Fin 2 → Cell := twoBank p7186 ray7186
theorem signs7186 : ∀ j, Signs p7186 (bank7186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7187 := params 18
abbrev ray7187 := rays 18
def bank7187 : Fin 2 → Cell := twoBank p7187 ray7187
theorem signs7187 : ∀ j, Signs p7187 (bank7187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7188 := params 19
abbrev ray7188 := rays 19
def bank7188 : Fin 2 → Cell := twoBank p7188 ray7188
theorem signs7188 : ∀ j, Signs p7188 (bank7188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7189 := params 20
abbrev ray7189 := rays 20
def bank7189 : Fin 2 → Cell := twoBank p7189 ray7189
theorem signs7189 : ∀ j, Signs p7189 (bank7189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7190 := params 21
abbrev ray7190 := rays 21
def bank7190 : Fin 2 → Cell := twoBank p7190 ray7190
theorem signs7190 : ∀ j, Signs p7190 (bank7190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7191 := params 22
abbrev ray7191 := rays 22
def bank7191 : Fin 2 → Cell := twoBank p7191 ray7191
theorem signs7191 : ∀ j, Signs p7191 (bank7191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7192 := params 23
abbrev ray7192 := rays 23
def bank7192 : Fin 2 → Cell := twoBank p7192 ray7192
theorem signs7192 : ∀ j, Signs p7192 (bank7192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7193 := params 24
abbrev ray7193 := rays 24
def bank7193 : Fin 2 → Cell := twoBank p7193 ray7193
theorem signs7193 : ∀ j, Signs p7193 (bank7193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7194 := params 25
abbrev ray7194 := rays 25
def bank7194 : Fin 2 → Cell := twoBank p7194 ray7194
theorem signs7194 : ∀ j, Signs p7194 (bank7194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7195 := params 26
abbrev ray7195 := rays 26
def bank7195 : Fin 2 → Cell := twoBank p7195 ray7195
theorem signs7195 : ∀ j, Signs p7195 (bank7195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7196 := params 27
abbrev ray7196 := rays 27
def bank7196 : Fin 2 → Cell := twoBank p7196 ray7196
theorem signs7196 : ∀ j, Signs p7196 (bank7196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7197 := params 28
abbrev ray7197 := rays 28
def bank7197 : Fin 2 → Cell := twoBank p7197 ray7197
theorem signs7197 : ∀ j, Signs p7197 (bank7197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7198 := params 29
abbrev ray7198 := rays 29
def bank7198 : Fin 2 → Cell := twoBank p7198 ray7198
theorem signs7198 : ∀ j, Signs p7198 (bank7198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7199 := params 30
abbrev ray7199 := rays 30
def bank7199 : Fin 2 → Cell := twoBank p7199 ray7199
theorem signs7199 : ∀ j, Signs p7199 (bank7199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p7200 := params 31
abbrev ray7200 := rays 31
def bank7200 : Fin 2 → Cell := twoBank p7200 ray7200
theorem signs7200 : ∀ j, Signs p7200 (bank7200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages07169_07200
