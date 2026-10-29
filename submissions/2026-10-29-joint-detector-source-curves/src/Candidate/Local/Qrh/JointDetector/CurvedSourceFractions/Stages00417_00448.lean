/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00417_00448
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99944299825261,99944160232212,99944020612244,99943880965361,99943741291564,99943601590858,99943461863244,99943322108726,99943182327306,99943042518988,99942902683774,99942762821667,99942622932670,99942483016786,99942343074017,99942203104367,99942063107838,99941923084434,99941783034157,99941642957010,99941502852996,99941362722118,99941222564378,99941082379780,99940942168326,99940801930019,99940661664862,99940521372858,99940381054009,99940240708320,99940100335791,99939959936427,99939819510230]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (416+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(23595838796093712290402/29704040143667626493295:Fraction),(70781374834843567609868/89110370431004629479885:Fraction),(89702450037411890972/112938682422061317465:Fraction),(23589697443373973170727/29702290143669376493295:Fraction),(70762952586710132278934/89105120431009879479885:Fraction),(70756812641510361116428/89103370431011629479885:Fraction),(2620395322310375764484/3300060015963458499255:Fraction),(70744534561516857354928/89099870431015129479885:Fraction),(1571964365040186482404/1979958231800375099553:Fraction),(23577419363474327780722/29698790143672876493295:Fraction),(14145224152055530164784/17818924086204075895977:Fraction),(10102854746930037815593/12727552918717447068555:Fraction),(174602090624859738648/219978075138330566617:Fraction),(70707709976060177613076/89089370431025629479885:Fraction),(14140314609499694825819/17817524086205475895977:Fraction),(3366449444445377130817/4242184306239482356185:Fraction),(1910521681344507326464/2407678930568402148105:Fraction),(70683168300671097835612/89082370431032629479885:Fraction),(23559010994053930044001/29693540143678126493295:Fraction),(14134179975659207934404/17815774086207225895977:Fraction),(10094966480717657943592/12725302918719697068555:Fraction),(7850959229612113734976/9897263381226625497765:Fraction),(70652499358613471506948/89073620431041379479885:Fraction),(14129273573118010113686/17814374086208625895977:Fraction),(1569782999182502053888/1979336009578775099553:Fraction),(10090586325117185825467/12724052918720947068555:Fraction),(70627972179100895871352/89066620431048379479885:Fraction),(23540614099160301694388/29688290143683376493295:Fraction),(70615711006559488349116/89063120431051879479885:Fraction),(2017416626595798426434/2544610583744389413711:Fraction),(23534483815290218049343/29686540143685126493295:Fraction),(70597323176216225301721/89057870431057129479885:Fraction)]
abbrev p417 := params 0
abbrev ray417 := rays 0
def bank417 : Fin 1 → Cell := oneBank p417 ray417
theorem signs417 : ∀ j, Signs p417 (bank417 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p418 := params 1
abbrev ray418 := rays 1
def bank418 : Fin 1 → Cell := oneBank p418 ray418
theorem signs418 : ∀ j, Signs p418 (bank418 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p419 := params 2
abbrev ray419 := rays 2
def bank419 : Fin 1 → Cell := oneBank p419 ray419
theorem signs419 : ∀ j, Signs p419 (bank419 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p420 := params 3
abbrev ray420 := rays 3
def bank420 : Fin 1 → Cell := oneBank p420 ray420
theorem signs420 : ∀ j, Signs p420 (bank420 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p421 := params 4
abbrev ray421 := rays 4
def bank421 : Fin 1 → Cell := oneBank p421 ray421
theorem signs421 : ∀ j, Signs p421 (bank421 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p422 := params 5
abbrev ray422 := rays 5
def bank422 : Fin 1 → Cell := oneBank p422 ray422
theorem signs422 : ∀ j, Signs p422 (bank422 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p423 := params 6
abbrev ray423 := rays 6
def bank423 : Fin 1 → Cell := oneBank p423 ray423
theorem signs423 : ∀ j, Signs p423 (bank423 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p424 := params 7
abbrev ray424 := rays 7
def bank424 : Fin 1 → Cell := oneBank p424 ray424
theorem signs424 : ∀ j, Signs p424 (bank424 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p425 := params 8
abbrev ray425 := rays 8
def bank425 : Fin 1 → Cell := oneBank p425 ray425
theorem signs425 : ∀ j, Signs p425 (bank425 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p426 := params 9
abbrev ray426 := rays 9
def bank426 : Fin 1 → Cell := oneBank p426 ray426
theorem signs426 : ∀ j, Signs p426 (bank426 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p427 := params 10
abbrev ray427 := rays 10
def bank427 : Fin 1 → Cell := oneBank p427 ray427
theorem signs427 : ∀ j, Signs p427 (bank427 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p428 := params 11
abbrev ray428 := rays 11
def bank428 : Fin 1 → Cell := oneBank p428 ray428
theorem signs428 : ∀ j, Signs p428 (bank428 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p429 := params 12
abbrev ray429 := rays 12
def bank429 : Fin 1 → Cell := oneBank p429 ray429
theorem signs429 : ∀ j, Signs p429 (bank429 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p430 := params 13
abbrev ray430 := rays 13
def bank430 : Fin 1 → Cell := oneBank p430 ray430
theorem signs430 : ∀ j, Signs p430 (bank430 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p431 := params 14
abbrev ray431 := rays 14
def bank431 : Fin 1 → Cell := oneBank p431 ray431
theorem signs431 : ∀ j, Signs p431 (bank431 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p432 := params 15
abbrev ray432 := rays 15
def bank432 : Fin 1 → Cell := oneBank p432 ray432
theorem signs432 : ∀ j, Signs p432 (bank432 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p433 := params 16
abbrev ray433 := rays 16
def bank433 : Fin 1 → Cell := oneBank p433 ray433
theorem signs433 : ∀ j, Signs p433 (bank433 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p434 := params 17
abbrev ray434 := rays 17
def bank434 : Fin 1 → Cell := oneBank p434 ray434
theorem signs434 : ∀ j, Signs p434 (bank434 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p435 := params 18
abbrev ray435 := rays 18
def bank435 : Fin 1 → Cell := oneBank p435 ray435
theorem signs435 : ∀ j, Signs p435 (bank435 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p436 := params 19
abbrev ray436 := rays 19
def bank436 : Fin 1 → Cell := oneBank p436 ray436
theorem signs436 : ∀ j, Signs p436 (bank436 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p437 := params 20
abbrev ray437 := rays 20
def bank437 : Fin 1 → Cell := oneBank p437 ray437
theorem signs437 : ∀ j, Signs p437 (bank437 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p438 := params 21
abbrev ray438 := rays 21
def bank438 : Fin 1 → Cell := oneBank p438 ray438
theorem signs438 : ∀ j, Signs p438 (bank438 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p439 := params 22
abbrev ray439 := rays 22
def bank439 : Fin 1 → Cell := oneBank p439 ray439
theorem signs439 : ∀ j, Signs p439 (bank439 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p440 := params 23
abbrev ray440 := rays 23
def bank440 : Fin 1 → Cell := oneBank p440 ray440
theorem signs440 : ∀ j, Signs p440 (bank440 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p441 := params 24
abbrev ray441 := rays 24
def bank441 : Fin 1 → Cell := oneBank p441 ray441
theorem signs441 : ∀ j, Signs p441 (bank441 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p442 := params 25
abbrev ray442 := rays 25
def bank442 : Fin 1 → Cell := oneBank p442 ray442
theorem signs442 : ∀ j, Signs p442 (bank442 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p443 := params 26
abbrev ray443 := rays 26
def bank443 : Fin 1 → Cell := oneBank p443 ray443
theorem signs443 : ∀ j, Signs p443 (bank443 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p444 := params 27
abbrev ray444 := rays 27
def bank444 : Fin 1 → Cell := oneBank p444 ray444
theorem signs444 : ∀ j, Signs p444 (bank444 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p445 := params 28
abbrev ray445 := rays 28
def bank445 : Fin 1 → Cell := oneBank p445 ray445
theorem signs445 : ∀ j, Signs p445 (bank445 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p446 := params 29
abbrev ray446 := rays 29
def bank446 : Fin 1 → Cell := oneBank p446 ray446
theorem signs446 : ∀ j, Signs p446 (bank446 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p447 := params 30
abbrev ray447 := rays 30
def bank447 : Fin 1 → Cell := oneBank p447 ray447
theorem signs447 : ∀ j, Signs p447 (bank447 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p448 := params 31
abbrev ray448 := rays 31
def bank448 : Fin 1 → Cell := oneBank p448 ray448
theorem signs448 : ∀ j, Signs p448 (bank448 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00417_00448
