/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00257_00288
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99966285978103,99966150729639,99966015453786,99965880150546,99965744819923,99965609461920,99965474076539,99965338663784,99965203223658,99965067756164,99964932261304,99964796739082,99964661189501,99964525612563,99964390008272,99964254376631,99964118717642,99963983031309,99963847317635,99963711576623,99963575808275,99963440012595,99963304189586,99963168339251,99963032461592,99962896556613,99962760624317,99962624664707,99962488677785,99962352663554,99962216622018,99962080553179,99961944457041]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (256+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(23925120925301510022233/29797373476907626493295:Fraction),(23923052452787522593273/29796790143574876493295:Fraction),(71762951734415116332124/89388620430726379479885:Fraction),(7972971767119423111268/9931874492303125497765:Fraction),(7972282341426245550032/9931680047858875497765:Fraction),(14348867448151434798644/17876674086146325895977:Fraction),(931664067563448661412/1160800265334199733505:Fraction),(885579369848598168444/1103455190502902833085:Fraction),(10246532244623117445068/12768302918676697068555:Fraction),(71719522260766776214472/89376370430738629479885:Fraction),(43071062948066849152/53678450709153381069:Fraction),(71707118355714481839716/89372870430742129479885:Fraction),(379369929612579116054/472863071062136928465:Fraction),(2655359808582697304381/3309976682620208499255:Fraction),(23896171322073898721662/29789206810249126493295:Fraction),(3413443528585803378028/4255517639559482356185:Fraction),(884890296646600264956/1103260746058652833085:Fraction),(1405292426479510705562/1752203341779463323135:Fraction),(14332742894448316210378/17872124086150875895977:Fraction),(12780010022078120489/15937019873507424555:Fraction),(14330263541889804567700/17871424086151575895977:Fraction),(14329023803845534644745/17871074086151925895977:Fraction),(23879640442961664746636/29784540143587126493295:Fraction),(71632724638478764560722/89351870430763129479885:Fraction),(23875509247431011327974/29783373476921626493295:Fraction),(4774688709356192071112/5956558028717775298659:Fraction),(4774275635896260205940/5956441362051225298659:Fraction),(23869313145551287496459/29781623476923376493295:Fraction),(1591149869537738061866/1985402676239375099553:Fraction),(23865182872030258613644/29780456810257876493295:Fraction),(71589355309067306499448/89339620430775379479885:Fraction),(7953684510067030309208/9926430047864125497765:Fraction)]
abbrev p257 := params 0
abbrev ray257 := rays 0
def bank257 : Fin 1 → Cell := oneBank p257 ray257
theorem signs257 : ∀ j, Signs p257 (bank257 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p258 := params 1
abbrev ray258 := rays 1
def bank258 : Fin 1 → Cell := oneBank p258 ray258
theorem signs258 : ∀ j, Signs p258 (bank258 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p259 := params 2
abbrev ray259 := rays 2
def bank259 : Fin 1 → Cell := oneBank p259 ray259
theorem signs259 : ∀ j, Signs p259 (bank259 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p260 := params 3
abbrev ray260 := rays 3
def bank260 : Fin 1 → Cell := oneBank p260 ray260
theorem signs260 : ∀ j, Signs p260 (bank260 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p261 := params 4
abbrev ray261 := rays 4
def bank261 : Fin 1 → Cell := oneBank p261 ray261
theorem signs261 : ∀ j, Signs p261 (bank261 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p262 := params 5
abbrev ray262 := rays 5
def bank262 : Fin 1 → Cell := oneBank p262 ray262
theorem signs262 : ∀ j, Signs p262 (bank262 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p263 := params 6
abbrev ray263 := rays 6
def bank263 : Fin 1 → Cell := oneBank p263 ray263
theorem signs263 : ∀ j, Signs p263 (bank263 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p264 := params 7
abbrev ray264 := rays 7
def bank264 : Fin 1 → Cell := oneBank p264 ray264
theorem signs264 : ∀ j, Signs p264 (bank264 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p265 := params 8
abbrev ray265 := rays 8
def bank265 : Fin 1 → Cell := oneBank p265 ray265
theorem signs265 : ∀ j, Signs p265 (bank265 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p266 := params 9
abbrev ray266 := rays 9
def bank266 : Fin 1 → Cell := oneBank p266 ray266
theorem signs266 : ∀ j, Signs p266 (bank266 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p267 := params 10
abbrev ray267 := rays 10
def bank267 : Fin 1 → Cell := oneBank p267 ray267
theorem signs267 : ∀ j, Signs p267 (bank267 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p268 := params 11
abbrev ray268 := rays 11
def bank268 : Fin 1 → Cell := oneBank p268 ray268
theorem signs268 : ∀ j, Signs p268 (bank268 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p269 := params 12
abbrev ray269 := rays 12
def bank269 : Fin 1 → Cell := oneBank p269 ray269
theorem signs269 : ∀ j, Signs p269 (bank269 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p270 := params 13
abbrev ray270 := rays 13
def bank270 : Fin 1 → Cell := oneBank p270 ray270
theorem signs270 : ∀ j, Signs p270 (bank270 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p271 := params 14
abbrev ray271 := rays 14
def bank271 : Fin 1 → Cell := oneBank p271 ray271
theorem signs271 : ∀ j, Signs p271 (bank271 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p272 := params 15
abbrev ray272 := rays 15
def bank272 : Fin 1 → Cell := oneBank p272 ray272
theorem signs272 : ∀ j, Signs p272 (bank272 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p273 := params 16
abbrev ray273 := rays 16
def bank273 : Fin 1 → Cell := oneBank p273 ray273
theorem signs273 : ∀ j, Signs p273 (bank273 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p274 := params 17
abbrev ray274 := rays 17
def bank274 : Fin 1 → Cell := oneBank p274 ray274
theorem signs274 : ∀ j, Signs p274 (bank274 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p275 := params 18
abbrev ray275 := rays 18
def bank275 : Fin 1 → Cell := oneBank p275 ray275
theorem signs275 : ∀ j, Signs p275 (bank275 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p276 := params 19
abbrev ray276 := rays 19
def bank276 : Fin 1 → Cell := oneBank p276 ray276
theorem signs276 : ∀ j, Signs p276 (bank276 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p277 := params 20
abbrev ray277 := rays 20
def bank277 : Fin 1 → Cell := oneBank p277 ray277
theorem signs277 : ∀ j, Signs p277 (bank277 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p278 := params 21
abbrev ray278 := rays 21
def bank278 : Fin 1 → Cell := oneBank p278 ray278
theorem signs278 : ∀ j, Signs p278 (bank278 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p279 := params 22
abbrev ray279 := rays 22
def bank279 : Fin 1 → Cell := oneBank p279 ray279
theorem signs279 : ∀ j, Signs p279 (bank279 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p280 := params 23
abbrev ray280 := rays 23
def bank280 : Fin 1 → Cell := oneBank p280 ray280
theorem signs280 : ∀ j, Signs p280 (bank280 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p281 := params 24
abbrev ray281 := rays 24
def bank281 : Fin 1 → Cell := oneBank p281 ray281
theorem signs281 : ∀ j, Signs p281 (bank281 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p282 := params 25
abbrev ray282 := rays 25
def bank282 : Fin 1 → Cell := oneBank p282 ray282
theorem signs282 : ∀ j, Signs p282 (bank282 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p283 := params 26
abbrev ray283 := rays 26
def bank283 : Fin 1 → Cell := oneBank p283 ray283
theorem signs283 : ∀ j, Signs p283 (bank283 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p284 := params 27
abbrev ray284 := rays 27
def bank284 : Fin 1 → Cell := oneBank p284 ray284
theorem signs284 : ∀ j, Signs p284 (bank284 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p285 := params 28
abbrev ray285 := rays 28
def bank285 : Fin 1 → Cell := oneBank p285 ray285
theorem signs285 : ∀ j, Signs p285 (bank285 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p286 := params 29
abbrev ray286 := rays 29
def bank286 : Fin 1 → Cell := oneBank p286 ray286
theorem signs286 : ∀ j, Signs p286 (bank286 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p287 := params 30
abbrev ray287 := rays 30
def bank287 : Fin 1 → Cell := oneBank p287 ray287
theorem signs287 : ∀ j, Signs p287 (bank287 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p288 := params 31
abbrev ray288 := rays 31
def bank288 : Fin 1 → Cell := oneBank p288 ray288
theorem signs288 : ∀ j, Signs p288 (bank288 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00257_00288
