/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00353_00384
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99953177657383,99953039793145,99952901901803,99952763983359,99952626037817,99952488065180,99952350065450,99952212038630,99952073984723,99951935903732,99951797795660,99951659660510,99951521498285,99951383308988,99951245092622,99951106849190,99950968578694,99950830281138,99950691956524,99950553604856,99950415226136,99950276820367,99950138387552,99949999927694,99949861440796,99949722926861,99949584385891,99949445817890,99949307222860,99949168600805,99949029951727,99948891275630,99948752572516]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (352+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(1581809146094009029067/1982758231797575099553:Fraction),(4745016291054477271283/5948158028726175298659:Fraction),(71169076953721424466091/89220620430894379479885:Fraction),(71162910544824962255876/89218870430896129479885:Fraction),(3388416377728692232687/4248434306233232356185:Fraction),(14230115664613269490714/17843074086179925895977:Fraction),(42729376883038720340/53581754012553381069:Fraction),(677507120960221913216/849636861246696471237:Fraction),(71132083894815293808608/89210120430904879479885:Fraction),(71125919885335946262232/89208370430906629479885:Fraction),(175604334993577533552/220263260323230566617:Fraction),(4740906164200263155368/5946991362060675298659:Fraction),(14221485810041554882366/17840624086182375895977:Fraction),(225718306796950359856/283178953748932157079:Fraction),(71095104028526200052144/89199620430915379479885:Fraction),(14217788483945291046560/17839574086183425895977:Fraction),(30494543893048610816/38265173930038129335:Fraction),(71076621006420690718924/89194370430920629479885:Fraction),(71070459994911979812838/89192620430922379479885:Fraction),(7896033331920884343548/9910096714547125497765:Fraction),(2631782954684714123026/3303300756700958499255:Fraction),(7894664507739519231469/9909707825658625497765:Fraction),(100774216123192241416/126504426143162240397:Fraction),(71039663960967950335448/89183870430931129479885:Fraction),(3382547873905787821244/4246767639568232356185:Fraction),(23675782582405132493254/29726790143644876493295:Fraction),(14204237987880117484298/17835724086187275895977:Fraction),(14203006627162322279332/17835374086187625895977:Fraction),(4733925155766973726586/5945008028729325298659:Fraction),(1577838251873096395501/1981630454020925099553:Fraction),(70996565129178168983333/89171620430943379479885:Fraction),(47804989850817469120/60047050795249245441:Fraction)]
abbrev p353 := params 0
abbrev ray353 := rays 0
def bank353 : Fin 1 → Cell := oneBank p353 ray353
theorem signs353 : ∀ j, Signs p353 (bank353 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p354 := params 1
abbrev ray354 := rays 1
def bank354 : Fin 1 → Cell := oneBank p354 ray354
theorem signs354 : ∀ j, Signs p354 (bank354 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p355 := params 2
abbrev ray355 := rays 2
def bank355 : Fin 1 → Cell := oneBank p355 ray355
theorem signs355 : ∀ j, Signs p355 (bank355 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p356 := params 3
abbrev ray356 := rays 3
def bank356 : Fin 1 → Cell := oneBank p356 ray356
theorem signs356 : ∀ j, Signs p356 (bank356 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p357 := params 4
abbrev ray357 := rays 4
def bank357 : Fin 1 → Cell := oneBank p357 ray357
theorem signs357 : ∀ j, Signs p357 (bank357 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p358 := params 5
abbrev ray358 := rays 5
def bank358 : Fin 1 → Cell := oneBank p358 ray358
theorem signs358 : ∀ j, Signs p358 (bank358 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p359 := params 6
abbrev ray359 := rays 6
def bank359 : Fin 1 → Cell := oneBank p359 ray359
theorem signs359 : ∀ j, Signs p359 (bank359 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p360 := params 7
abbrev ray360 := rays 7
def bank360 : Fin 1 → Cell := oneBank p360 ray360
theorem signs360 : ∀ j, Signs p360 (bank360 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p361 := params 8
abbrev ray361 := rays 8
def bank361 : Fin 1 → Cell := oneBank p361 ray361
theorem signs361 : ∀ j, Signs p361 (bank361 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p362 := params 9
abbrev ray362 := rays 9
def bank362 : Fin 1 → Cell := oneBank p362 ray362
theorem signs362 : ∀ j, Signs p362 (bank362 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p363 := params 10
abbrev ray363 := rays 10
def bank363 : Fin 1 → Cell := oneBank p363 ray363
theorem signs363 : ∀ j, Signs p363 (bank363 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p364 := params 11
abbrev ray364 := rays 11
def bank364 : Fin 1 → Cell := oneBank p364 ray364
theorem signs364 : ∀ j, Signs p364 (bank364 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p365 := params 12
abbrev ray365 := rays 12
def bank365 : Fin 1 → Cell := oneBank p365 ray365
theorem signs365 : ∀ j, Signs p365 (bank365 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p366 := params 13
abbrev ray366 := rays 13
def bank366 : Fin 1 → Cell := oneBank p366 ray366
theorem signs366 : ∀ j, Signs p366 (bank366 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p367 := params 14
abbrev ray367 := rays 14
def bank367 : Fin 1 → Cell := oneBank p367 ray367
theorem signs367 : ∀ j, Signs p367 (bank367 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p368 := params 15
abbrev ray368 := rays 15
def bank368 : Fin 1 → Cell := oneBank p368 ray368
theorem signs368 : ∀ j, Signs p368 (bank368 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p369 := params 16
abbrev ray369 := rays 16
def bank369 : Fin 1 → Cell := oneBank p369 ray369
theorem signs369 : ∀ j, Signs p369 (bank369 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p370 := params 17
abbrev ray370 := rays 17
def bank370 : Fin 1 → Cell := oneBank p370 ray370
theorem signs370 : ∀ j, Signs p370 (bank370 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p371 := params 18
abbrev ray371 := rays 18
def bank371 : Fin 1 → Cell := oneBank p371 ray371
theorem signs371 : ∀ j, Signs p371 (bank371 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p372 := params 19
abbrev ray372 := rays 19
def bank372 : Fin 1 → Cell := oneBank p372 ray372
theorem signs372 : ∀ j, Signs p372 (bank372 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p373 := params 20
abbrev ray373 := rays 20
def bank373 : Fin 1 → Cell := oneBank p373 ray373
theorem signs373 : ∀ j, Signs p373 (bank373 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p374 := params 21
abbrev ray374 := rays 21
def bank374 : Fin 1 → Cell := oneBank p374 ray374
theorem signs374 : ∀ j, Signs p374 (bank374 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p375 := params 22
abbrev ray375 := rays 22
def bank375 : Fin 1 → Cell := oneBank p375 ray375
theorem signs375 : ∀ j, Signs p375 (bank375 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p376 := params 23
abbrev ray376 := rays 23
def bank376 : Fin 1 → Cell := oneBank p376 ray376
theorem signs376 : ∀ j, Signs p376 (bank376 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p377 := params 24
abbrev ray377 := rays 24
def bank377 : Fin 1 → Cell := oneBank p377 ray377
theorem signs377 : ∀ j, Signs p377 (bank377 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p378 := params 25
abbrev ray378 := rays 25
def bank378 : Fin 1 → Cell := oneBank p378 ray378
theorem signs378 : ∀ j, Signs p378 (bank378 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p379 := params 26
abbrev ray379 := rays 26
def bank379 : Fin 1 → Cell := oneBank p379 ray379
theorem signs379 : ∀ j, Signs p379 (bank379 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p380 := params 27
abbrev ray380 := rays 27
def bank380 : Fin 1 → Cell := oneBank p380 ray380
theorem signs380 : ∀ j, Signs p380 (bank380 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p381 := params 28
abbrev ray381 := rays 28
def bank381 : Fin 1 → Cell := oneBank p381 ray381
theorem signs381 : ∀ j, Signs p381 (bank381 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p382 := params 29
abbrev ray382 := rays 29
def bank382 : Fin 1 → Cell := oneBank p382 ray382
theorem signs382 : ∀ j, Signs p382 (bank382 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p383 := params 30
abbrev ray383 := rays 30
def bank383 : Fin 1 → Cell := oneBank p383 ray383
theorem signs383 : ∀ j, Signs p383 (bank383 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p384 := params 31
abbrev ray384 := rays 31
def bank384 : Fin 1 → Cell := oneBank p384 ray384
theorem signs384 : ∀ j, Signs p384 (bank384 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00353_00384
