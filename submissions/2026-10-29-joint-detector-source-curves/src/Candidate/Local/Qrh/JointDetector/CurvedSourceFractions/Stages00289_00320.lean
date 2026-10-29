/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00289_00320
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99961944457041,99961808333607,99961672182879,99961536004861,99961399799556,99961263566966,99961127307094,99960991019944,99960854705518,99960718363820,99960581994852,99960445598618,99960309175120,99960172724361,99960036246344,99959899741073,99959763208550,99959626648778,99959490061760,99959353447500,99959216805999,99959080137262,99958943441290,99958806718088,99958669967658,99958533190002,99958396385125,99958259553029,99958122693716,99957985807190,99957848893454,99957711952510,99957574984362]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (288+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(71576966872449066019361/89336120430778879479885:Fraction),(14314154830932484861223/17866874086156125895977:Fraction),(3407837201494329712031/4253934306227732356185:Fraction),(71558388102619618920773/89330870430784129479885:Fraction),(3407247427349547895568/4253767639561232356185:Fraction),(23848668282200020208288/29775790143595876493295:Fraction),(14307962702695706492096/17865124086157875895977:Fraction),(71533623180983071661558/89323870430791129479885:Fraction),(23842477547721132658864/29774040143597626493295:Fraction),(2043464054286701446322/2552010583736989413711:Fraction),(10216436022520727576554/12759802918685197068555:Fraction),(882825474272271213304/1102677412725902833085:Fraction),(1588948321538940811502/1984780454017775099553:Fraction),(418108108323590083477/522300411876032920935:Fraction),(882596276200762969078/1102612597911152833085:Fraction),(7942678890672338850859/9923318936756125497765:Fraction),(14295584532167601485440/17861624086161375895977:Fraction),(1588260806815118831824/1984586009573525099553:Fraction),(14293109949496530459544/17860924086162075895977:Fraction),(14291872837885530775550/17860574086162425895977:Fraction),(23817726142129392220274/29767040143604626493295:Fraction),(3402237793551307254464/4252350972895982356185:Fraction),(332282831152739713816/415337769445662230139:Fraction),(4762308235079278926856/5953058028721275298659:Fraction),(71428440562122132695648/89294120430820879479885:Fraction),(71422256186971690330772/89292370430822629479885:Fraction),(680153074411909081565/850386861245946471237:Fraction),(71409890441014812023636/89288870430826129479885:Fraction),(7933745318224642173094/9920791158980875497765:Fraction),(6868448897412250448/8589261224707035063:Fraction),(71391344508479502176968/89283620430831379479885:Fraction),(2039576106571857186976/2550910583738089413711:Fraction)]
abbrev p289 := params 0
abbrev ray289 := rays 0
def bank289 : Fin 1 → Cell := oneBank p289 ray289
theorem signs289 : ∀ j, Signs p289 (bank289 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p290 := params 1
abbrev ray290 := rays 1
def bank290 : Fin 1 → Cell := oneBank p290 ray290
theorem signs290 : ∀ j, Signs p290 (bank290 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p291 := params 2
abbrev ray291 := rays 2
def bank291 : Fin 1 → Cell := oneBank p291 ray291
theorem signs291 : ∀ j, Signs p291 (bank291 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p292 := params 3
abbrev ray292 := rays 3
def bank292 : Fin 1 → Cell := oneBank p292 ray292
theorem signs292 : ∀ j, Signs p292 (bank292 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p293 := params 4
abbrev ray293 := rays 4
def bank293 : Fin 1 → Cell := oneBank p293 ray293
theorem signs293 : ∀ j, Signs p293 (bank293 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p294 := params 5
abbrev ray294 := rays 5
def bank294 : Fin 1 → Cell := oneBank p294 ray294
theorem signs294 : ∀ j, Signs p294 (bank294 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p295 := params 6
abbrev ray295 := rays 6
def bank295 : Fin 1 → Cell := oneBank p295 ray295
theorem signs295 : ∀ j, Signs p295 (bank295 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p296 := params 7
abbrev ray296 := rays 7
def bank296 : Fin 1 → Cell := oneBank p296 ray296
theorem signs296 : ∀ j, Signs p296 (bank296 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p297 := params 8
abbrev ray297 := rays 8
def bank297 : Fin 1 → Cell := oneBank p297 ray297
theorem signs297 : ∀ j, Signs p297 (bank297 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p298 := params 9
abbrev ray298 := rays 9
def bank298 : Fin 1 → Cell := oneBank p298 ray298
theorem signs298 : ∀ j, Signs p298 (bank298 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p299 := params 10
abbrev ray299 := rays 10
def bank299 : Fin 1 → Cell := oneBank p299 ray299
theorem signs299 : ∀ j, Signs p299 (bank299 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p300 := params 11
abbrev ray300 := rays 11
def bank300 : Fin 1 → Cell := oneBank p300 ray300
theorem signs300 : ∀ j, Signs p300 (bank300 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p301 := params 12
abbrev ray301 := rays 12
def bank301 : Fin 1 → Cell := oneBank p301 ray301
theorem signs301 : ∀ j, Signs p301 (bank301 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p302 := params 13
abbrev ray302 := rays 13
def bank302 : Fin 1 → Cell := oneBank p302 ray302
theorem signs302 : ∀ j, Signs p302 (bank302 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p303 := params 14
abbrev ray303 := rays 14
def bank303 : Fin 1 → Cell := oneBank p303 ray303
theorem signs303 : ∀ j, Signs p303 (bank303 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p304 := params 15
abbrev ray304 := rays 15
def bank304 : Fin 1 → Cell := oneBank p304 ray304
theorem signs304 : ∀ j, Signs p304 (bank304 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p305 := params 16
abbrev ray305 := rays 16
def bank305 : Fin 1 → Cell := oneBank p305 ray305
theorem signs305 : ∀ j, Signs p305 (bank305 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p306 := params 17
abbrev ray306 := rays 17
def bank306 : Fin 1 → Cell := oneBank p306 ray306
theorem signs306 : ∀ j, Signs p306 (bank306 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p307 := params 18
abbrev ray307 := rays 18
def bank307 : Fin 1 → Cell := oneBank p307 ray307
theorem signs307 : ∀ j, Signs p307 (bank307 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p308 := params 19
abbrev ray308 := rays 19
def bank308 : Fin 1 → Cell := oneBank p308 ray308
theorem signs308 : ∀ j, Signs p308 (bank308 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p309 := params 20
abbrev ray309 := rays 20
def bank309 : Fin 1 → Cell := oneBank p309 ray309
theorem signs309 : ∀ j, Signs p309 (bank309 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p310 := params 21
abbrev ray310 := rays 21
def bank310 : Fin 1 → Cell := oneBank p310 ray310
theorem signs310 : ∀ j, Signs p310 (bank310 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p311 := params 22
abbrev ray311 := rays 22
def bank311 : Fin 1 → Cell := oneBank p311 ray311
theorem signs311 : ∀ j, Signs p311 (bank311 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p312 := params 23
abbrev ray312 := rays 23
def bank312 : Fin 1 → Cell := oneBank p312 ray312
theorem signs312 : ∀ j, Signs p312 (bank312 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p313 := params 24
abbrev ray313 := rays 24
def bank313 : Fin 1 → Cell := oneBank p313 ray313
theorem signs313 : ∀ j, Signs p313 (bank313 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p314 := params 25
abbrev ray314 := rays 25
def bank314 : Fin 1 → Cell := oneBank p314 ray314
theorem signs314 : ∀ j, Signs p314 (bank314 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p315 := params 26
abbrev ray315 := rays 26
def bank315 : Fin 1 → Cell := oneBank p315 ray315
theorem signs315 : ∀ j, Signs p315 (bank315 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p316 := params 27
abbrev ray316 := rays 27
def bank316 : Fin 1 → Cell := oneBank p316 ray316
theorem signs316 : ∀ j, Signs p316 (bank316 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p317 := params 28
abbrev ray317 := rays 28
def bank317 : Fin 1 → Cell := oneBank p317 ray317
theorem signs317 : ∀ j, Signs p317 (bank317 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p318 := params 29
abbrev ray318 := rays 29
def bank318 : Fin 1 → Cell := oneBank p318 ray318
theorem signs318 : ∀ j, Signs p318 (bank318 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p319 := params 30
abbrev ray319 := rays 30
def bank319 : Fin 1 → Cell := oneBank p319 ray319
theorem signs319 : ∀ j, Signs p319 (bank319 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p320 := params 31
abbrev ray320 := rays 31
def bank320 : Fin 1 → Cell := oneBank p320 ray320
theorem signs320 : ∀ j, Signs p320 (bank320 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00289_00320
