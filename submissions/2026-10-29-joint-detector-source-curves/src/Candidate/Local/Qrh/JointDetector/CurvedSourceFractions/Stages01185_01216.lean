/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01185_01216
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99829368651220,99829209171718,99829049667278,99828890137902,99828730583593,99828571004352,99828411400182,99828251771085,99828092117064,99827932438121,99827772734258,99827613005477,99827453251781,99827293473172,99827133669653,99826973841226,99826813987892,99826654109655,99826494206517,99826334278479,99826174325544,99826014347715,99825854344994,99825694317383,99825534264884,99825374187500,99825214085233,99825053958085,99824893806059,99824733629157,99824573427381,99824413200733,99824252949216]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1184+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(7106144575093524788/9422235151083937679:Fraction),(66187918877867661890816/87766370432348629479885:Fraction),(66182100857358863685584/87764620432350379479885:Fraction),(2450973431684465161744/3250476682679708499255:Fraction),(7352273943454088416237/9751235603594875497765:Fraction),(1350298966616931587522/1791007559843992438365:Fraction),(22052944352031010790768/29252540144119126493295:Fraction),(4410201104445847531145/5850391362157275298659:Fraction),(9449600159274903002968/12536302918908697068555:Fraction),(22047128900285352691388/29250790144120876493295:Fraction),(9447938698097439597772/12535802918909197068555:Fraction),(66129757329194201366068/87748870432366129479885:Fraction),(1469420968679523815059/1949936009608175099553:Fraction),(66118129670845940754772/87745370432369629479885:Fraction),(3148205561380561958824/4178267639636732356185:Fraction),(349769867434229281004/464242700700386928465:Fraction),(3147652043815175697988/4178100972970232356185:Fraction),(629475054420503722517/835603527927396471237:Fraction),(22029689848740951715949/29245540144126126493295:Fraction),(45795744571296335438/60800326009965439695:Fraction),(66077449105612008370294/87733120432381879479885:Fraction),(69917077898337482252/92837429028977385693:Fraction),(66065829160438822334008/87729620432385379479885:Fraction),(66060019526083992257864/87727870432387129479885:Fraction),(44480950121212241522/59074828573999245441:Fraction),(13209680674448333452010/17544874086478125895977:Fraction),(22014198544569437035051/29240873477464126493295:Fraction),(1467484171431351951137/1949352676275425099553:Fraction),(66030980833542676135832/87719120432395879479885:Fraction),(22008391663718986806202/29239123477465876493295:Fraction),(2445161813633221635004/3248726682681458499255:Fraction),(66013562764373467824074/87713870432401129479885:Fraction)]
abbrev p1185 := params 0
abbrev ray1185 := rays 0
def bank1185 : Fin 1 → Cell := oneBank p1185 ray1185
theorem signs1185 : ∀ j, Signs p1185 (bank1185 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1186 := params 1
abbrev ray1186 := rays 1
def bank1186 : Fin 1 → Cell := oneBank p1186 ray1186
theorem signs1186 : ∀ j, Signs p1186 (bank1186 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1187 := params 2
abbrev ray1187 := rays 2
def bank1187 : Fin 1 → Cell := oneBank p1187 ray1187
theorem signs1187 : ∀ j, Signs p1187 (bank1187 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1188 := params 3
abbrev ray1188 := rays 3
def bank1188 : Fin 1 → Cell := oneBank p1188 ray1188
theorem signs1188 : ∀ j, Signs p1188 (bank1188 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1189 := params 4
abbrev ray1189 := rays 4
def bank1189 : Fin 1 → Cell := oneBank p1189 ray1189
theorem signs1189 : ∀ j, Signs p1189 (bank1189 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1190 := params 5
abbrev ray1190 := rays 5
def bank1190 : Fin 1 → Cell := oneBank p1190 ray1190
theorem signs1190 : ∀ j, Signs p1190 (bank1190 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1191 := params 6
abbrev ray1191 := rays 6
def bank1191 : Fin 1 → Cell := oneBank p1191 ray1191
theorem signs1191 : ∀ j, Signs p1191 (bank1191 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1192 := params 7
abbrev ray1192 := rays 7
def bank1192 : Fin 1 → Cell := oneBank p1192 ray1192
theorem signs1192 : ∀ j, Signs p1192 (bank1192 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1193 := params 8
abbrev ray1193 := rays 8
def bank1193 : Fin 1 → Cell := oneBank p1193 ray1193
theorem signs1193 : ∀ j, Signs p1193 (bank1193 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1194 := params 9
abbrev ray1194 := rays 9
def bank1194 : Fin 1 → Cell := oneBank p1194 ray1194
theorem signs1194 : ∀ j, Signs p1194 (bank1194 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1195 := params 10
abbrev ray1195 := rays 10
def bank1195 : Fin 1 → Cell := oneBank p1195 ray1195
theorem signs1195 : ∀ j, Signs p1195 (bank1195 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1196 := params 11
abbrev ray1196 := rays 11
def bank1196 : Fin 1 → Cell := oneBank p1196 ray1196
theorem signs1196 : ∀ j, Signs p1196 (bank1196 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1197 := params 12
abbrev ray1197 := rays 12
def bank1197 : Fin 1 → Cell := oneBank p1197 ray1197
theorem signs1197 : ∀ j, Signs p1197 (bank1197 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1198 := params 13
abbrev ray1198 := rays 13
def bank1198 : Fin 1 → Cell := oneBank p1198 ray1198
theorem signs1198 : ∀ j, Signs p1198 (bank1198 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1199 := params 14
abbrev ray1199 := rays 14
def bank1199 : Fin 1 → Cell := oneBank p1199 ray1199
theorem signs1199 : ∀ j, Signs p1199 (bank1199 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1200 := params 15
abbrev ray1200 := rays 15
def bank1200 : Fin 1 → Cell := oneBank p1200 ray1200
theorem signs1200 : ∀ j, Signs p1200 (bank1200 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1201 := params 16
abbrev ray1201 := rays 16
def bank1201 : Fin 1 → Cell := oneBank p1201 ray1201
theorem signs1201 : ∀ j, Signs p1201 (bank1201 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1202 := params 17
abbrev ray1202 := rays 17
def bank1202 : Fin 1 → Cell := oneBank p1202 ray1202
theorem signs1202 : ∀ j, Signs p1202 (bank1202 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1203 := params 18
abbrev ray1203 := rays 18
def bank1203 : Fin 1 → Cell := oneBank p1203 ray1203
theorem signs1203 : ∀ j, Signs p1203 (bank1203 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1204 := params 19
abbrev ray1204 := rays 19
def bank1204 : Fin 1 → Cell := oneBank p1204 ray1204
theorem signs1204 : ∀ j, Signs p1204 (bank1204 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1205 := params 20
abbrev ray1205 := rays 20
def bank1205 : Fin 1 → Cell := oneBank p1205 ray1205
theorem signs1205 : ∀ j, Signs p1205 (bank1205 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1206 := params 21
abbrev ray1206 := rays 21
def bank1206 : Fin 1 → Cell := oneBank p1206 ray1206
theorem signs1206 : ∀ j, Signs p1206 (bank1206 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1207 := params 22
abbrev ray1207 := rays 22
def bank1207 : Fin 1 → Cell := oneBank p1207 ray1207
theorem signs1207 : ∀ j, Signs p1207 (bank1207 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1208 := params 23
abbrev ray1208 := rays 23
def bank1208 : Fin 1 → Cell := oneBank p1208 ray1208
theorem signs1208 : ∀ j, Signs p1208 (bank1208 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1209 := params 24
abbrev ray1209 := rays 24
def bank1209 : Fin 1 → Cell := oneBank p1209 ray1209
theorem signs1209 : ∀ j, Signs p1209 (bank1209 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1210 := params 25
abbrev ray1210 := rays 25
def bank1210 : Fin 1 → Cell := oneBank p1210 ray1210
theorem signs1210 : ∀ j, Signs p1210 (bank1210 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1211 := params 26
abbrev ray1211 := rays 26
def bank1211 : Fin 1 → Cell := oneBank p1211 ray1211
theorem signs1211 : ∀ j, Signs p1211 (bank1211 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1212 := params 27
abbrev ray1212 := rays 27
def bank1212 : Fin 1 → Cell := oneBank p1212 ray1212
theorem signs1212 : ∀ j, Signs p1212 (bank1212 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1213 := params 28
abbrev ray1213 := rays 28
def bank1213 : Fin 1 → Cell := oneBank p1213 ray1213
theorem signs1213 : ∀ j, Signs p1213 (bank1213 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1214 := params 29
abbrev ray1214 := rays 29
def bank1214 : Fin 1 → Cell := oneBank p1214 ray1214
theorem signs1214 : ∀ j, Signs p1214 (bank1214 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1215 := params 30
abbrev ray1215 := rays 30
def bank1215 : Fin 1 → Cell := oneBank p1215 ray1215
theorem signs1215 : ∀ j, Signs p1215 (bank1215 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1216 := params 31
abbrev ray1216 := rays 31
def bank1216 : Fin 1 → Cell := oneBank p1216 ray1216
theorem signs1216 : ∀ j, Signs p1216 (bank1216 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01185_01216
