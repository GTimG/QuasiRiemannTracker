/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15457_15488
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95188108609446,95187643940249,95187179255029,95186714553786,95186249836520,95185785103231,95185320353919,95184855588585,95184390807228,95183926009849,95183461196448,95182996367024,95182531521578,95182066660110,95181601782620,95181136889108,95180671979574,95180207054018,95179742112441,95179277154842,95178812181221,95178347191579,95177882185915,95177417164230,95176952126524,95176487072796,95176022003047,95175556917277,95175091815486,95174626697674,95174161563841,95173696413988,95173231248114]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15456+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15457 := params 0
abbrev ray15457 := rays 0
def bank15457 : Fin 1 → Cell := oneBank p15457 ray15457
theorem signs15457 : ∀ j, Signs p15457 (bank15457 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15458 := params 1
abbrev ray15458 := rays 1
def bank15458 : Fin 1 → Cell := oneBank p15458 ray15458
theorem signs15458 : ∀ j, Signs p15458 (bank15458 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15459 := params 2
abbrev ray15459 := rays 2
def bank15459 : Fin 1 → Cell := oneBank p15459 ray15459
theorem signs15459 : ∀ j, Signs p15459 (bank15459 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15460 := params 3
abbrev ray15460 := rays 3
def bank15460 : Fin 1 → Cell := oneBank p15460 ray15460
theorem signs15460 : ∀ j, Signs p15460 (bank15460 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15461 := params 4
abbrev ray15461 := rays 4
def bank15461 : Fin 1 → Cell := oneBank p15461 ray15461
theorem signs15461 : ∀ j, Signs p15461 (bank15461 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15462 := params 5
abbrev ray15462 := rays 5
def bank15462 : Fin 1 → Cell := oneBank p15462 ray15462
theorem signs15462 : ∀ j, Signs p15462 (bank15462 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15463 := params 6
abbrev ray15463 := rays 6
def bank15463 : Fin 1 → Cell := oneBank p15463 ray15463
theorem signs15463 : ∀ j, Signs p15463 (bank15463 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15464 := params 7
abbrev ray15464 := rays 7
def bank15464 : Fin 1 → Cell := oneBank p15464 ray15464
theorem signs15464 : ∀ j, Signs p15464 (bank15464 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15465 := params 8
abbrev ray15465 := rays 8
def bank15465 : Fin 1 → Cell := oneBank p15465 ray15465
theorem signs15465 : ∀ j, Signs p15465 (bank15465 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15466 := params 9
abbrev ray15466 := rays 9
def bank15466 : Fin 1 → Cell := oneBank p15466 ray15466
theorem signs15466 : ∀ j, Signs p15466 (bank15466 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15467 := params 10
abbrev ray15467 := rays 10
def bank15467 : Fin 1 → Cell := oneBank p15467 ray15467
theorem signs15467 : ∀ j, Signs p15467 (bank15467 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15468 := params 11
abbrev ray15468 := rays 11
def bank15468 : Fin 1 → Cell := oneBank p15468 ray15468
theorem signs15468 : ∀ j, Signs p15468 (bank15468 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15469 := params 12
abbrev ray15469 := rays 12
def bank15469 : Fin 1 → Cell := oneBank p15469 ray15469
theorem signs15469 : ∀ j, Signs p15469 (bank15469 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15470 := params 13
abbrev ray15470 := rays 13
def bank15470 : Fin 1 → Cell := oneBank p15470 ray15470
theorem signs15470 : ∀ j, Signs p15470 (bank15470 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15471 := params 14
abbrev ray15471 := rays 14
def bank15471 : Fin 1 → Cell := oneBank p15471 ray15471
theorem signs15471 : ∀ j, Signs p15471 (bank15471 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15472 := params 15
abbrev ray15472 := rays 15
def bank15472 : Fin 1 → Cell := oneBank p15472 ray15472
theorem signs15472 : ∀ j, Signs p15472 (bank15472 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15473 := params 16
abbrev ray15473 := rays 16
def bank15473 : Fin 1 → Cell := oneBank p15473 ray15473
theorem signs15473 : ∀ j, Signs p15473 (bank15473 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15474 := params 17
abbrev ray15474 := rays 17
def bank15474 : Fin 1 → Cell := oneBank p15474 ray15474
theorem signs15474 : ∀ j, Signs p15474 (bank15474 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15475 := params 18
abbrev ray15475 := rays 18
def bank15475 : Fin 1 → Cell := oneBank p15475 ray15475
theorem signs15475 : ∀ j, Signs p15475 (bank15475 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15476 := params 19
abbrev ray15476 := rays 19
def bank15476 : Fin 1 → Cell := oneBank p15476 ray15476
theorem signs15476 : ∀ j, Signs p15476 (bank15476 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15477 := params 20
abbrev ray15477 := rays 20
def bank15477 : Fin 1 → Cell := oneBank p15477 ray15477
theorem signs15477 : ∀ j, Signs p15477 (bank15477 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15478 := params 21
abbrev ray15478 := rays 21
def bank15478 : Fin 1 → Cell := oneBank p15478 ray15478
theorem signs15478 : ∀ j, Signs p15478 (bank15478 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15479 := params 22
abbrev ray15479 := rays 22
def bank15479 : Fin 1 → Cell := oneBank p15479 ray15479
theorem signs15479 : ∀ j, Signs p15479 (bank15479 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15480 := params 23
abbrev ray15480 := rays 23
def bank15480 : Fin 1 → Cell := oneBank p15480 ray15480
theorem signs15480 : ∀ j, Signs p15480 (bank15480 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15481 := params 24
abbrev ray15481 := rays 24
def bank15481 : Fin 1 → Cell := oneBank p15481 ray15481
theorem signs15481 : ∀ j, Signs p15481 (bank15481 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15482 := params 25
abbrev ray15482 := rays 25
def bank15482 : Fin 1 → Cell := oneBank p15482 ray15482
theorem signs15482 : ∀ j, Signs p15482 (bank15482 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15483 := params 26
abbrev ray15483 := rays 26
def bank15483 : Fin 1 → Cell := oneBank p15483 ray15483
theorem signs15483 : ∀ j, Signs p15483 (bank15483 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15484 := params 27
abbrev ray15484 := rays 27
def bank15484 : Fin 1 → Cell := oneBank p15484 ray15484
theorem signs15484 : ∀ j, Signs p15484 (bank15484 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15485 := params 28
abbrev ray15485 := rays 28
def bank15485 : Fin 1 → Cell := oneBank p15485 ray15485
theorem signs15485 : ∀ j, Signs p15485 (bank15485 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15486 := params 29
abbrev ray15486 := rays 29
def bank15486 : Fin 1 → Cell := oneBank p15486 ray15486
theorem signs15486 : ∀ j, Signs p15486 (bank15486 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15487 := params 30
abbrev ray15487 := rays 30
def bank15487 : Fin 1 → Cell := oneBank p15487 ray15487
theorem signs15487 : ∀ j, Signs p15487 (bank15487 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15488 := params 31
abbrev ray15488 := rays 31
def bank15488 : Fin 1 → Cell := oneBank p15488 ray15488
theorem signs15488 : ∀ j, Signs p15488 (bank15488 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15457_15488
