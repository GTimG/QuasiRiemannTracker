/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02145_02176
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99665069104848,99664886072345,99664703012330,99664519924805,99664336809771,99664153667230,99663970497183,99663787299632,99663604074578,99663420822022,99663237541966,99663054234412,99662870899360,99662687536812,99662504146770,99662320729235,99662137284208,99661953811691,99661770311685,99661586784192,99661403229213,99661219646749,99661036036802,99660852399374,99660668734465,99660485042078,99660301322213,99660117574872,99659933800057,99659749997768,99659566168008,99659382310777,99659198426077]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2144+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2145 := params 0
abbrev ray2145 := rays 0
def bank2145 : Fin 2 → Cell := twoBank p2145 ray2145
theorem signs2145 : ∀ j, Signs p2145 (bank2145 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2146 := params 1
abbrev ray2146 := rays 1
def bank2146 : Fin 2 → Cell := twoBank p2146 ray2146
theorem signs2146 : ∀ j, Signs p2146 (bank2146 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2147 := params 2
abbrev ray2147 := rays 2
def bank2147 : Fin 2 → Cell := twoBank p2147 ray2147
theorem signs2147 : ∀ j, Signs p2147 (bank2147 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2148 := params 3
abbrev ray2148 := rays 3
def bank2148 : Fin 2 → Cell := twoBank p2148 ray2148
theorem signs2148 : ∀ j, Signs p2148 (bank2148 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2149 := params 4
abbrev ray2149 := rays 4
def bank2149 : Fin 2 → Cell := twoBank p2149 ray2149
theorem signs2149 : ∀ j, Signs p2149 (bank2149 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2150 := params 5
abbrev ray2150 := rays 5
def bank2150 : Fin 2 → Cell := twoBank p2150 ray2150
theorem signs2150 : ∀ j, Signs p2150 (bank2150 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2151 := params 6
abbrev ray2151 := rays 6
def bank2151 : Fin 2 → Cell := twoBank p2151 ray2151
theorem signs2151 : ∀ j, Signs p2151 (bank2151 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2152 := params 7
abbrev ray2152 := rays 7
def bank2152 : Fin 2 → Cell := twoBank p2152 ray2152
theorem signs2152 : ∀ j, Signs p2152 (bank2152 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2153 := params 8
abbrev ray2153 := rays 8
def bank2153 : Fin 2 → Cell := twoBank p2153 ray2153
theorem signs2153 : ∀ j, Signs p2153 (bank2153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2154 := params 9
abbrev ray2154 := rays 9
def bank2154 : Fin 2 → Cell := twoBank p2154 ray2154
theorem signs2154 : ∀ j, Signs p2154 (bank2154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2155 := params 10
abbrev ray2155 := rays 10
def bank2155 : Fin 2 → Cell := twoBank p2155 ray2155
theorem signs2155 : ∀ j, Signs p2155 (bank2155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2156 := params 11
abbrev ray2156 := rays 11
def bank2156 : Fin 2 → Cell := twoBank p2156 ray2156
theorem signs2156 : ∀ j, Signs p2156 (bank2156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2157 := params 12
abbrev ray2157 := rays 12
def bank2157 : Fin 2 → Cell := twoBank p2157 ray2157
theorem signs2157 : ∀ j, Signs p2157 (bank2157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2158 := params 13
abbrev ray2158 := rays 13
def bank2158 : Fin 2 → Cell := twoBank p2158 ray2158
theorem signs2158 : ∀ j, Signs p2158 (bank2158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2159 := params 14
abbrev ray2159 := rays 14
def bank2159 : Fin 2 → Cell := twoBank p2159 ray2159
theorem signs2159 : ∀ j, Signs p2159 (bank2159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2160 := params 15
abbrev ray2160 := rays 15
def bank2160 : Fin 2 → Cell := twoBank p2160 ray2160
theorem signs2160 : ∀ j, Signs p2160 (bank2160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2161 := params 16
abbrev ray2161 := rays 16
def bank2161 : Fin 2 → Cell := twoBank p2161 ray2161
theorem signs2161 : ∀ j, Signs p2161 (bank2161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2162 := params 17
abbrev ray2162 := rays 17
def bank2162 : Fin 2 → Cell := twoBank p2162 ray2162
theorem signs2162 : ∀ j, Signs p2162 (bank2162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2163 := params 18
abbrev ray2163 := rays 18
def bank2163 : Fin 2 → Cell := twoBank p2163 ray2163
theorem signs2163 : ∀ j, Signs p2163 (bank2163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2164 := params 19
abbrev ray2164 := rays 19
def bank2164 : Fin 2 → Cell := twoBank p2164 ray2164
theorem signs2164 : ∀ j, Signs p2164 (bank2164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2165 := params 20
abbrev ray2165 := rays 20
def bank2165 : Fin 2 → Cell := twoBank p2165 ray2165
theorem signs2165 : ∀ j, Signs p2165 (bank2165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2166 := params 21
abbrev ray2166 := rays 21
def bank2166 : Fin 2 → Cell := twoBank p2166 ray2166
theorem signs2166 : ∀ j, Signs p2166 (bank2166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2167 := params 22
abbrev ray2167 := rays 22
def bank2167 : Fin 2 → Cell := twoBank p2167 ray2167
theorem signs2167 : ∀ j, Signs p2167 (bank2167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2168 := params 23
abbrev ray2168 := rays 23
def bank2168 : Fin 2 → Cell := twoBank p2168 ray2168
theorem signs2168 : ∀ j, Signs p2168 (bank2168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2169 := params 24
abbrev ray2169 := rays 24
def bank2169 : Fin 2 → Cell := twoBank p2169 ray2169
theorem signs2169 : ∀ j, Signs p2169 (bank2169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2170 := params 25
abbrev ray2170 := rays 25
def bank2170 : Fin 2 → Cell := twoBank p2170 ray2170
theorem signs2170 : ∀ j, Signs p2170 (bank2170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2171 := params 26
abbrev ray2171 := rays 26
def bank2171 : Fin 2 → Cell := twoBank p2171 ray2171
theorem signs2171 : ∀ j, Signs p2171 (bank2171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2172 := params 27
abbrev ray2172 := rays 27
def bank2172 : Fin 2 → Cell := twoBank p2172 ray2172
theorem signs2172 : ∀ j, Signs p2172 (bank2172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2173 := params 28
abbrev ray2173 := rays 28
def bank2173 : Fin 2 → Cell := twoBank p2173 ray2173
theorem signs2173 : ∀ j, Signs p2173 (bank2173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2174 := params 29
abbrev ray2174 := rays 29
def bank2174 : Fin 2 → Cell := twoBank p2174 ray2174
theorem signs2174 : ∀ j, Signs p2174 (bank2174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2175 := params 30
abbrev ray2175 := rays 30
def bank2175 : Fin 2 → Cell := twoBank p2175 ray2175
theorem signs2175 : ∀ j, Signs p2175 (bank2175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2176 := params 31
abbrev ray2176 := rays 31
def bank2176 : Fin 2 → Cell := twoBank p2176 ray2176
theorem signs2176 : ∀ j, Signs p2176 (bank2176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02145_02176
