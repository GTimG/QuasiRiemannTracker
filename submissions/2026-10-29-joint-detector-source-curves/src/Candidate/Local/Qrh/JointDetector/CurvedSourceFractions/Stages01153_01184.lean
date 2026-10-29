/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01153_01184
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99834458814001,99834300133748,99834141428483,99833982698207,99833823942923,99833665162634,99833506357342,99833347527049,99833188671757,99833029791469,99832870886187,99832711955913,99832553000650,99832394020400,99832235015166,99832075984949,99831916929752,99831757849577,99831598744427,99831439614304,99831280459211,99831121279150,99830962074122,99830802844130,99830643589177,99830484309265,99830325004396,99830165674573,99830006319797,99829846940072,99829687535399,99829528105781,99829368651220]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1152+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(3160959834359764130887/4182100972966232356185:Fraction),(7374924864956412666992/9758041159143625497765:Fraction),(2458092299400089581364/3252615571566458499255:Fraction),(9480380028688059338096/12545552918899447068555:Fraction),(66356829354050773022381/87817120432297879479885:Fraction),(22116999847853319516532/29271790144099876493295:Fraction),(66345169550979862524472/87813620432301379479885:Fraction),(66339339376321306074137/87811870432303129479885:Fraction),(3158738582763850777202/4181434306300232356185:Fraction),(13265536427238599252666/17561674086461325895977:Fraction),(1792482503618454987313/2373151903575902148105:Fraction),(22105341795514481781758/29268290144103376493295:Fraction),(13262039591453388437500/17560624086462375895977:Fraction),(13260874069212827063600/17560274086462725895977:Fraction),(7366504863497522976176/9755513381368375497765:Fraction),(9470388319079971902857/12542552918902447068555:Fraction),(22095630431748917369138/29265373477439626493295:Fraction),(490970863794270424091/650328669869041699851:Fraction),(22091747249140410188477/29264206810774126493295:Fraction),(22089805566947240482418/29263623477441376493295:Fraction),(490841427341597072072/650289780980191699851:Fraction),(490798294209601106000/650276818017241699851:Fraction),(358118630074548540560/474516867201780429621:Fraction),(4416408215174235399080/5852258028822075298659:Fraction),(66240300928446545241727/87782120432332879479885:Fraction),(13246895689531462592176/17556074086466925895977:Fraction),(22076219001319080557408/29259540144112126493295:Fraction),(66222836597400721428931/87776870432338129479885:Fraction),(4414467733954061885530/5851674695489325298659:Fraction),(2452266490359293546458/3250865571568208499255:Fraction),(36517030064720124821/48412366482263309145:Fraction),(22066518937425095371544/29256623477448376493295:Fraction)]
abbrev p1153 := params 0
abbrev ray1153 := rays 0
def bank1153 : Fin 1 → Cell := oneBank p1153 ray1153
theorem signs1153 : ∀ j, Signs p1153 (bank1153 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1154 := params 1
abbrev ray1154 := rays 1
def bank1154 : Fin 1 → Cell := oneBank p1154 ray1154
theorem signs1154 : ∀ j, Signs p1154 (bank1154 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1155 := params 2
abbrev ray1155 := rays 2
def bank1155 : Fin 1 → Cell := oneBank p1155 ray1155
theorem signs1155 : ∀ j, Signs p1155 (bank1155 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1156 := params 3
abbrev ray1156 := rays 3
def bank1156 : Fin 1 → Cell := oneBank p1156 ray1156
theorem signs1156 : ∀ j, Signs p1156 (bank1156 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1157 := params 4
abbrev ray1157 := rays 4
def bank1157 : Fin 1 → Cell := oneBank p1157 ray1157
theorem signs1157 : ∀ j, Signs p1157 (bank1157 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1158 := params 5
abbrev ray1158 := rays 5
def bank1158 : Fin 1 → Cell := oneBank p1158 ray1158
theorem signs1158 : ∀ j, Signs p1158 (bank1158 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1159 := params 6
abbrev ray1159 := rays 6
def bank1159 : Fin 1 → Cell := oneBank p1159 ray1159
theorem signs1159 : ∀ j, Signs p1159 (bank1159 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1160 := params 7
abbrev ray1160 := rays 7
def bank1160 : Fin 1 → Cell := oneBank p1160 ray1160
theorem signs1160 : ∀ j, Signs p1160 (bank1160 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1161 := params 8
abbrev ray1161 := rays 8
def bank1161 : Fin 1 → Cell := oneBank p1161 ray1161
theorem signs1161 : ∀ j, Signs p1161 (bank1161 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1162 := params 9
abbrev ray1162 := rays 9
def bank1162 : Fin 1 → Cell := oneBank p1162 ray1162
theorem signs1162 : ∀ j, Signs p1162 (bank1162 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1163 := params 10
abbrev ray1163 := rays 10
def bank1163 : Fin 1 → Cell := oneBank p1163 ray1163
theorem signs1163 : ∀ j, Signs p1163 (bank1163 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1164 := params 11
abbrev ray1164 := rays 11
def bank1164 : Fin 1 → Cell := oneBank p1164 ray1164
theorem signs1164 : ∀ j, Signs p1164 (bank1164 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1165 := params 12
abbrev ray1165 := rays 12
def bank1165 : Fin 1 → Cell := oneBank p1165 ray1165
theorem signs1165 : ∀ j, Signs p1165 (bank1165 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1166 := params 13
abbrev ray1166 := rays 13
def bank1166 : Fin 1 → Cell := oneBank p1166 ray1166
theorem signs1166 : ∀ j, Signs p1166 (bank1166 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1167 := params 14
abbrev ray1167 := rays 14
def bank1167 : Fin 1 → Cell := oneBank p1167 ray1167
theorem signs1167 : ∀ j, Signs p1167 (bank1167 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1168 := params 15
abbrev ray1168 := rays 15
def bank1168 : Fin 1 → Cell := oneBank p1168 ray1168
theorem signs1168 : ∀ j, Signs p1168 (bank1168 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1169 := params 16
abbrev ray1169 := rays 16
def bank1169 : Fin 1 → Cell := oneBank p1169 ray1169
theorem signs1169 : ∀ j, Signs p1169 (bank1169 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1170 := params 17
abbrev ray1170 := rays 17
def bank1170 : Fin 1 → Cell := oneBank p1170 ray1170
theorem signs1170 : ∀ j, Signs p1170 (bank1170 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1171 := params 18
abbrev ray1171 := rays 18
def bank1171 : Fin 1 → Cell := oneBank p1171 ray1171
theorem signs1171 : ∀ j, Signs p1171 (bank1171 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1172 := params 19
abbrev ray1172 := rays 19
def bank1172 : Fin 1 → Cell := oneBank p1172 ray1172
theorem signs1172 : ∀ j, Signs p1172 (bank1172 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1173 := params 20
abbrev ray1173 := rays 20
def bank1173 : Fin 1 → Cell := oneBank p1173 ray1173
theorem signs1173 : ∀ j, Signs p1173 (bank1173 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1174 := params 21
abbrev ray1174 := rays 21
def bank1174 : Fin 1 → Cell := oneBank p1174 ray1174
theorem signs1174 : ∀ j, Signs p1174 (bank1174 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1175 := params 22
abbrev ray1175 := rays 22
def bank1175 : Fin 1 → Cell := oneBank p1175 ray1175
theorem signs1175 : ∀ j, Signs p1175 (bank1175 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1176 := params 23
abbrev ray1176 := rays 23
def bank1176 : Fin 1 → Cell := oneBank p1176 ray1176
theorem signs1176 : ∀ j, Signs p1176 (bank1176 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1177 := params 24
abbrev ray1177 := rays 24
def bank1177 : Fin 1 → Cell := oneBank p1177 ray1177
theorem signs1177 : ∀ j, Signs p1177 (bank1177 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1178 := params 25
abbrev ray1178 := rays 25
def bank1178 : Fin 1 → Cell := oneBank p1178 ray1178
theorem signs1178 : ∀ j, Signs p1178 (bank1178 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1179 := params 26
abbrev ray1179 := rays 26
def bank1179 : Fin 1 → Cell := oneBank p1179 ray1179
theorem signs1179 : ∀ j, Signs p1179 (bank1179 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1180 := params 27
abbrev ray1180 := rays 27
def bank1180 : Fin 1 → Cell := oneBank p1180 ray1180
theorem signs1180 : ∀ j, Signs p1180 (bank1180 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1181 := params 28
abbrev ray1181 := rays 28
def bank1181 : Fin 1 → Cell := oneBank p1181 ray1181
theorem signs1181 : ∀ j, Signs p1181 (bank1181 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1182 := params 29
abbrev ray1182 := rays 29
def bank1182 : Fin 1 → Cell := oneBank p1182 ray1182
theorem signs1182 : ∀ j, Signs p1182 (bank1182 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1183 := params 30
abbrev ray1183 := rays 30
def bank1183 : Fin 1 → Cell := oneBank p1183 ray1183
theorem signs1183 : ∀ j, Signs p1183 (bank1183 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1184 := params 31
abbrev ray1184 := rays 31
def bank1184 : Fin 1 → Cell := oneBank p1184 ray1184
theorem signs1184 : ∀ j, Signs p1184 (bank1184 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01153_01184
