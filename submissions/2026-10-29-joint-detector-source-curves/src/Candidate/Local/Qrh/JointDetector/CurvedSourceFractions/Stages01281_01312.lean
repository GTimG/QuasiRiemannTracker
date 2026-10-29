/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01281_01312
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99813945228430,99813783365296,99813621477443,99813459564872,99813297627587,99813135665589,99812973678880,99812811667463,99812649631341,99812487570515,99812325484987,99812163374761,99812001239837,99811839080218,99811676895907,99811514686906,99811352453217,99811190194842,99811027911784,99810865604044,99810703271626,99810540914531,99810378532761,99810216126319,99810053695207,99809891239427,99809728758982,99809566253873,99809403724103,99809241169674,99809078590588,99808915986848,99808753358456]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1280+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(118265075899626392720/157838054833360143207:Fraction),(65631340521993457674724/87598370432516629479885:Fraction),(21875187913575501431858/29198873477506126493295:Fraction),(21873262260167086018508/29198290144173376493295:Fraction),(1773351644906178957587/2367381633311402148105:Fraction),(1988128363147283610199/2654283952500716044845:Fraction),(4373497395154874618858/5839308028835025298659:Fraction),(13119337138385724728401/17517574086505425895977:Fraction),(65590911497943029694152/87586120432528879479885:Fraction),(161938610185554458147/216257704771680566617:Fraction),(21859787931280473157093/29194206810844126493295:Fraction),(65573591504073752797856/87580870432534129479885:Fraction),(624455419386536645395/834086861262246471237:Fraction),(21854015462796971691224/29192456810845876493295:Fraction),(65556274782838173680428/87575620432539379479885:Fraction),(118109016610776548500/157790757536110143207:Fraction),(13108946451227562294635/17514424086508575895977:Fraction),(65538962555420818886164/87570370432544629479885:Fraction),(809051761433771611226/1081094079414152833085:Fraction),(2849018374708317399578/3807255236197744759995:Fraction),(3120078742967838435784/4169767639645232356185:Fraction),(7279542847587459426032/9729263381394625497765:Fraction),(21836705825259992116934/29187206810851126493295:Fraction),(21834783048271607834068/29186623477518376493295:Fraction),(21832860618627387383149/29186040144185626493295:Fraction),(1770076064555157008546/2366388390069152148105:Fraction),(65487047963310550619264/87554620432560379479885:Fraction),(346461812593878732593/463242700701386928465:Fraction),(65475517018856069763388/87551120432563879479885:Fraction),(65469751279160072504132/87549370432565629479885:Fraction),(7273776286858898551202/9727513381396375497765:Fraction),(7273135745115724106738/9727318936952125497765:Fraction)]
abbrev p1281 := params 0
abbrev ray1281 := rays 0
def bank1281 : Fin 1 → Cell := oneBank p1281 ray1281
theorem signs1281 : ∀ j, Signs p1281 (bank1281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1282 := params 1
abbrev ray1282 := rays 1
def bank1282 : Fin 1 → Cell := oneBank p1282 ray1282
theorem signs1282 : ∀ j, Signs p1282 (bank1282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1283 := params 2
abbrev ray1283 := rays 2
def bank1283 : Fin 1 → Cell := oneBank p1283 ray1283
theorem signs1283 : ∀ j, Signs p1283 (bank1283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1284 := params 3
abbrev ray1284 := rays 3
def bank1284 : Fin 1 → Cell := oneBank p1284 ray1284
theorem signs1284 : ∀ j, Signs p1284 (bank1284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1285 := params 4
abbrev ray1285 := rays 4
def bank1285 : Fin 1 → Cell := oneBank p1285 ray1285
theorem signs1285 : ∀ j, Signs p1285 (bank1285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1286 := params 5
abbrev ray1286 := rays 5
def bank1286 : Fin 1 → Cell := oneBank p1286 ray1286
theorem signs1286 : ∀ j, Signs p1286 (bank1286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1287 := params 6
abbrev ray1287 := rays 6
def bank1287 : Fin 1 → Cell := oneBank p1287 ray1287
theorem signs1287 : ∀ j, Signs p1287 (bank1287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1288 := params 7
abbrev ray1288 := rays 7
def bank1288 : Fin 1 → Cell := oneBank p1288 ray1288
theorem signs1288 : ∀ j, Signs p1288 (bank1288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1289 := params 8
abbrev ray1289 := rays 8
def bank1289 : Fin 1 → Cell := oneBank p1289 ray1289
theorem signs1289 : ∀ j, Signs p1289 (bank1289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1290 := params 9
abbrev ray1290 := rays 9
def bank1290 : Fin 1 → Cell := oneBank p1290 ray1290
theorem signs1290 : ∀ j, Signs p1290 (bank1290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1291 := params 10
abbrev ray1291 := rays 10
def bank1291 : Fin 1 → Cell := oneBank p1291 ray1291
theorem signs1291 : ∀ j, Signs p1291 (bank1291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1292 := params 11
abbrev ray1292 := rays 11
def bank1292 : Fin 1 → Cell := oneBank p1292 ray1292
theorem signs1292 : ∀ j, Signs p1292 (bank1292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1293 := params 12
abbrev ray1293 := rays 12
def bank1293 : Fin 1 → Cell := oneBank p1293 ray1293
theorem signs1293 : ∀ j, Signs p1293 (bank1293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1294 := params 13
abbrev ray1294 := rays 13
def bank1294 : Fin 1 → Cell := oneBank p1294 ray1294
theorem signs1294 : ∀ j, Signs p1294 (bank1294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1295 := params 14
abbrev ray1295 := rays 14
def bank1295 : Fin 1 → Cell := oneBank p1295 ray1295
theorem signs1295 : ∀ j, Signs p1295 (bank1295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1296 := params 15
abbrev ray1296 := rays 15
def bank1296 : Fin 1 → Cell := oneBank p1296 ray1296
theorem signs1296 : ∀ j, Signs p1296 (bank1296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1297 := params 16
abbrev ray1297 := rays 16
def bank1297 : Fin 1 → Cell := oneBank p1297 ray1297
theorem signs1297 : ∀ j, Signs p1297 (bank1297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1298 := params 17
abbrev ray1298 := rays 17
def bank1298 : Fin 1 → Cell := oneBank p1298 ray1298
theorem signs1298 : ∀ j, Signs p1298 (bank1298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1299 := params 18
abbrev ray1299 := rays 18
def bank1299 : Fin 1 → Cell := oneBank p1299 ray1299
theorem signs1299 : ∀ j, Signs p1299 (bank1299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1300 := params 19
abbrev ray1300 := rays 19
def bank1300 : Fin 1 → Cell := oneBank p1300 ray1300
theorem signs1300 : ∀ j, Signs p1300 (bank1300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1301 := params 20
abbrev ray1301 := rays 20
def bank1301 : Fin 1 → Cell := oneBank p1301 ray1301
theorem signs1301 : ∀ j, Signs p1301 (bank1301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1302 := params 21
abbrev ray1302 := rays 21
def bank1302 : Fin 1 → Cell := oneBank p1302 ray1302
theorem signs1302 : ∀ j, Signs p1302 (bank1302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1303 := params 22
abbrev ray1303 := rays 22
def bank1303 : Fin 1 → Cell := oneBank p1303 ray1303
theorem signs1303 : ∀ j, Signs p1303 (bank1303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1304 := params 23
abbrev ray1304 := rays 23
def bank1304 : Fin 1 → Cell := oneBank p1304 ray1304
theorem signs1304 : ∀ j, Signs p1304 (bank1304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1305 := params 24
abbrev ray1305 := rays 24
def bank1305 : Fin 1 → Cell := oneBank p1305 ray1305
theorem signs1305 : ∀ j, Signs p1305 (bank1305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1306 := params 25
abbrev ray1306 := rays 25
def bank1306 : Fin 1 → Cell := oneBank p1306 ray1306
theorem signs1306 : ∀ j, Signs p1306 (bank1306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1307 := params 26
abbrev ray1307 := rays 26
def bank1307 : Fin 1 → Cell := oneBank p1307 ray1307
theorem signs1307 : ∀ j, Signs p1307 (bank1307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1308 := params 27
abbrev ray1308 := rays 27
def bank1308 : Fin 1 → Cell := oneBank p1308 ray1308
theorem signs1308 : ∀ j, Signs p1308 (bank1308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1309 := params 28
abbrev ray1309 := rays 28
def bank1309 : Fin 1 → Cell := oneBank p1309 ray1309
theorem signs1309 : ∀ j, Signs p1309 (bank1309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1310 := params 29
abbrev ray1310 := rays 29
def bank1310 : Fin 1 → Cell := oneBank p1310 ray1310
theorem signs1310 : ∀ j, Signs p1310 (bank1310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1311 := params 30
abbrev ray1311 := rays 30
def bank1311 : Fin 1 → Cell := oneBank p1311 ray1311
theorem signs1311 : ∀ j, Signs p1311 (bank1311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1312 := params 31
abbrev ray1312 := rays 31
def bank1312 : Fin 1 → Cell := oneBank p1312 ray1312
theorem signs1312 : ∀ j, Signs p1312 (bank1312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01281_01312
