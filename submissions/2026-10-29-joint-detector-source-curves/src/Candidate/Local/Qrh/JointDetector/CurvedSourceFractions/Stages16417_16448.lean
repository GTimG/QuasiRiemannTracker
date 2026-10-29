/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16417_16448
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94734659172926,94734179146118,94733699103326,94733219044551,94732738969792,94732258879050,94731778772324,94731298649615,94730818510922,94730338356246,94729858185586,94729377998943,94728897796316,94728417577706,94727937343112,94727457092535,94726976825974,94726496543430,94726016244902,94725535930391,94725055599896,94724575253418,94724094890956,94723614512511,94723134118083,94722653707671,94722173281276,94721692838897,94721212380535,94720731906189,94720251415860,94719770909547,94719290387251]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16416+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16417 := params 0
abbrev ray16417 := rays 0
def bank16417 : Fin 1 → Cell := oneBank p16417 ray16417
theorem signs16417 : ∀ j, Signs p16417 (bank16417 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16418 := params 1
abbrev ray16418 := rays 1
def bank16418 : Fin 1 → Cell := oneBank p16418 ray16418
theorem signs16418 : ∀ j, Signs p16418 (bank16418 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16419 := params 2
abbrev ray16419 := rays 2
def bank16419 : Fin 1 → Cell := oneBank p16419 ray16419
theorem signs16419 : ∀ j, Signs p16419 (bank16419 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16420 := params 3
abbrev ray16420 := rays 3
def bank16420 : Fin 1 → Cell := oneBank p16420 ray16420
theorem signs16420 : ∀ j, Signs p16420 (bank16420 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16421 := params 4
abbrev ray16421 := rays 4
def bank16421 : Fin 1 → Cell := oneBank p16421 ray16421
theorem signs16421 : ∀ j, Signs p16421 (bank16421 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16422 := params 5
abbrev ray16422 := rays 5
def bank16422 : Fin 1 → Cell := oneBank p16422 ray16422
theorem signs16422 : ∀ j, Signs p16422 (bank16422 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16423 := params 6
abbrev ray16423 := rays 6
def bank16423 : Fin 1 → Cell := oneBank p16423 ray16423
theorem signs16423 : ∀ j, Signs p16423 (bank16423 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16424 := params 7
abbrev ray16424 := rays 7
def bank16424 : Fin 1 → Cell := oneBank p16424 ray16424
theorem signs16424 : ∀ j, Signs p16424 (bank16424 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16425 := params 8
abbrev ray16425 := rays 8
def bank16425 : Fin 1 → Cell := oneBank p16425 ray16425
theorem signs16425 : ∀ j, Signs p16425 (bank16425 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16426 := params 9
abbrev ray16426 := rays 9
def bank16426 : Fin 1 → Cell := oneBank p16426 ray16426
theorem signs16426 : ∀ j, Signs p16426 (bank16426 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16427 := params 10
abbrev ray16427 := rays 10
def bank16427 : Fin 1 → Cell := oneBank p16427 ray16427
theorem signs16427 : ∀ j, Signs p16427 (bank16427 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16428 := params 11
abbrev ray16428 := rays 11
def bank16428 : Fin 1 → Cell := oneBank p16428 ray16428
theorem signs16428 : ∀ j, Signs p16428 (bank16428 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16429 := params 12
abbrev ray16429 := rays 12
def bank16429 : Fin 1 → Cell := oneBank p16429 ray16429
theorem signs16429 : ∀ j, Signs p16429 (bank16429 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16430 := params 13
abbrev ray16430 := rays 13
def bank16430 : Fin 1 → Cell := oneBank p16430 ray16430
theorem signs16430 : ∀ j, Signs p16430 (bank16430 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16431 := params 14
abbrev ray16431 := rays 14
def bank16431 : Fin 1 → Cell := oneBank p16431 ray16431
theorem signs16431 : ∀ j, Signs p16431 (bank16431 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16432 := params 15
abbrev ray16432 := rays 15
def bank16432 : Fin 1 → Cell := oneBank p16432 ray16432
theorem signs16432 : ∀ j, Signs p16432 (bank16432 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16433 := params 16
abbrev ray16433 := rays 16
def bank16433 : Fin 1 → Cell := oneBank p16433 ray16433
theorem signs16433 : ∀ j, Signs p16433 (bank16433 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16434 := params 17
abbrev ray16434 := rays 17
def bank16434 : Fin 1 → Cell := oneBank p16434 ray16434
theorem signs16434 : ∀ j, Signs p16434 (bank16434 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16435 := params 18
abbrev ray16435 := rays 18
def bank16435 : Fin 1 → Cell := oneBank p16435 ray16435
theorem signs16435 : ∀ j, Signs p16435 (bank16435 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16436 := params 19
abbrev ray16436 := rays 19
def bank16436 : Fin 1 → Cell := oneBank p16436 ray16436
theorem signs16436 : ∀ j, Signs p16436 (bank16436 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16437 := params 20
abbrev ray16437 := rays 20
def bank16437 : Fin 1 → Cell := oneBank p16437 ray16437
theorem signs16437 : ∀ j, Signs p16437 (bank16437 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16438 := params 21
abbrev ray16438 := rays 21
def bank16438 : Fin 1 → Cell := oneBank p16438 ray16438
theorem signs16438 : ∀ j, Signs p16438 (bank16438 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16439 := params 22
abbrev ray16439 := rays 22
def bank16439 : Fin 1 → Cell := oneBank p16439 ray16439
theorem signs16439 : ∀ j, Signs p16439 (bank16439 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16440 := params 23
abbrev ray16440 := rays 23
def bank16440 : Fin 1 → Cell := oneBank p16440 ray16440
theorem signs16440 : ∀ j, Signs p16440 (bank16440 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16441 := params 24
abbrev ray16441 := rays 24
def bank16441 : Fin 1 → Cell := oneBank p16441 ray16441
theorem signs16441 : ∀ j, Signs p16441 (bank16441 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16442 := params 25
abbrev ray16442 := rays 25
def bank16442 : Fin 1 → Cell := oneBank p16442 ray16442
theorem signs16442 : ∀ j, Signs p16442 (bank16442 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16443 := params 26
abbrev ray16443 := rays 26
def bank16443 : Fin 1 → Cell := oneBank p16443 ray16443
theorem signs16443 : ∀ j, Signs p16443 (bank16443 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16444 := params 27
abbrev ray16444 := rays 27
def bank16444 : Fin 1 → Cell := oneBank p16444 ray16444
theorem signs16444 : ∀ j, Signs p16444 (bank16444 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16445 := params 28
abbrev ray16445 := rays 28
def bank16445 : Fin 1 → Cell := oneBank p16445 ray16445
theorem signs16445 : ∀ j, Signs p16445 (bank16445 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16446 := params 29
abbrev ray16446 := rays 29
def bank16446 : Fin 1 → Cell := oneBank p16446 ray16446
theorem signs16446 : ∀ j, Signs p16446 (bank16446 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16447 := params 30
abbrev ray16447 := rays 30
def bank16447 : Fin 1 → Cell := oneBank p16447 ray16447
theorem signs16447 : ∀ j, Signs p16447 (bank16447 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16448 := params 31
abbrev ray16448 := rays 31
def bank16448 : Fin 1 → Cell := oneBank p16448 ray16448
theorem signs16448 : ∀ j, Signs p16448 (bank16448 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16417_16448
