/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16545_16576
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94673085828104,94672603755416,94672121666744,94671639562089,94671157441450,94670675304828,94670193152222,94669710983633,94669228799060,94668746598503,94668264381963,94667782149439,94667299900932,94666817636441,94666335355967,94665853059509,94665370747067,94664888418642,94664406074233,94663923713840,94663441337464,94662958945104,94662476536760,94661994112433,94661511672122,94661029215827,94660546743549,94660064255287,94659581751041,94659099230812,94658616694599,94658134142402,94657651574222]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16544+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16545 := params 0
abbrev ray16545 := rays 0
def bank16545 : Fin 1 → Cell := oneBank p16545 ray16545
theorem signs16545 : ∀ j, Signs p16545 (bank16545 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16546 := params 1
abbrev ray16546 := rays 1
def bank16546 : Fin 1 → Cell := oneBank p16546 ray16546
theorem signs16546 : ∀ j, Signs p16546 (bank16546 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16547 := params 2
abbrev ray16547 := rays 2
def bank16547 : Fin 1 → Cell := oneBank p16547 ray16547
theorem signs16547 : ∀ j, Signs p16547 (bank16547 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16548 := params 3
abbrev ray16548 := rays 3
def bank16548 : Fin 1 → Cell := oneBank p16548 ray16548
theorem signs16548 : ∀ j, Signs p16548 (bank16548 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16549 := params 4
abbrev ray16549 := rays 4
def bank16549 : Fin 1 → Cell := oneBank p16549 ray16549
theorem signs16549 : ∀ j, Signs p16549 (bank16549 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16550 := params 5
abbrev ray16550 := rays 5
def bank16550 : Fin 1 → Cell := oneBank p16550 ray16550
theorem signs16550 : ∀ j, Signs p16550 (bank16550 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16551 := params 6
abbrev ray16551 := rays 6
def bank16551 : Fin 1 → Cell := oneBank p16551 ray16551
theorem signs16551 : ∀ j, Signs p16551 (bank16551 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16552 := params 7
abbrev ray16552 := rays 7
def bank16552 : Fin 1 → Cell := oneBank p16552 ray16552
theorem signs16552 : ∀ j, Signs p16552 (bank16552 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16553 := params 8
abbrev ray16553 := rays 8
def bank16553 : Fin 1 → Cell := oneBank p16553 ray16553
theorem signs16553 : ∀ j, Signs p16553 (bank16553 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16554 := params 9
abbrev ray16554 := rays 9
def bank16554 : Fin 1 → Cell := oneBank p16554 ray16554
theorem signs16554 : ∀ j, Signs p16554 (bank16554 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16555 := params 10
abbrev ray16555 := rays 10
def bank16555 : Fin 1 → Cell := oneBank p16555 ray16555
theorem signs16555 : ∀ j, Signs p16555 (bank16555 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16556 := params 11
abbrev ray16556 := rays 11
def bank16556 : Fin 1 → Cell := oneBank p16556 ray16556
theorem signs16556 : ∀ j, Signs p16556 (bank16556 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16557 := params 12
abbrev ray16557 := rays 12
def bank16557 : Fin 1 → Cell := oneBank p16557 ray16557
theorem signs16557 : ∀ j, Signs p16557 (bank16557 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16558 := params 13
abbrev ray16558 := rays 13
def bank16558 : Fin 1 → Cell := oneBank p16558 ray16558
theorem signs16558 : ∀ j, Signs p16558 (bank16558 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16559 := params 14
abbrev ray16559 := rays 14
def bank16559 : Fin 1 → Cell := oneBank p16559 ray16559
theorem signs16559 : ∀ j, Signs p16559 (bank16559 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16560 := params 15
abbrev ray16560 := rays 15
def bank16560 : Fin 1 → Cell := oneBank p16560 ray16560
theorem signs16560 : ∀ j, Signs p16560 (bank16560 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16561 := params 16
abbrev ray16561 := rays 16
def bank16561 : Fin 1 → Cell := oneBank p16561 ray16561
theorem signs16561 : ∀ j, Signs p16561 (bank16561 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16562 := params 17
abbrev ray16562 := rays 17
def bank16562 : Fin 1 → Cell := oneBank p16562 ray16562
theorem signs16562 : ∀ j, Signs p16562 (bank16562 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16563 := params 18
abbrev ray16563 := rays 18
def bank16563 : Fin 1 → Cell := oneBank p16563 ray16563
theorem signs16563 : ∀ j, Signs p16563 (bank16563 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16564 := params 19
abbrev ray16564 := rays 19
def bank16564 : Fin 1 → Cell := oneBank p16564 ray16564
theorem signs16564 : ∀ j, Signs p16564 (bank16564 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16565 := params 20
abbrev ray16565 := rays 20
def bank16565 : Fin 1 → Cell := oneBank p16565 ray16565
theorem signs16565 : ∀ j, Signs p16565 (bank16565 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16566 := params 21
abbrev ray16566 := rays 21
def bank16566 : Fin 1 → Cell := oneBank p16566 ray16566
theorem signs16566 : ∀ j, Signs p16566 (bank16566 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16567 := params 22
abbrev ray16567 := rays 22
def bank16567 : Fin 1 → Cell := oneBank p16567 ray16567
theorem signs16567 : ∀ j, Signs p16567 (bank16567 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16568 := params 23
abbrev ray16568 := rays 23
def bank16568 : Fin 1 → Cell := oneBank p16568 ray16568
theorem signs16568 : ∀ j, Signs p16568 (bank16568 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16569 := params 24
abbrev ray16569 := rays 24
def bank16569 : Fin 1 → Cell := oneBank p16569 ray16569
theorem signs16569 : ∀ j, Signs p16569 (bank16569 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16570 := params 25
abbrev ray16570 := rays 25
def bank16570 : Fin 1 → Cell := oneBank p16570 ray16570
theorem signs16570 : ∀ j, Signs p16570 (bank16570 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16571 := params 26
abbrev ray16571 := rays 26
def bank16571 : Fin 1 → Cell := oneBank p16571 ray16571
theorem signs16571 : ∀ j, Signs p16571 (bank16571 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16572 := params 27
abbrev ray16572 := rays 27
def bank16572 : Fin 1 → Cell := oneBank p16572 ray16572
theorem signs16572 : ∀ j, Signs p16572 (bank16572 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16573 := params 28
abbrev ray16573 := rays 28
def bank16573 : Fin 1 → Cell := oneBank p16573 ray16573
theorem signs16573 : ∀ j, Signs p16573 (bank16573 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16574 := params 29
abbrev ray16574 := rays 29
def bank16574 : Fin 1 → Cell := oneBank p16574 ray16574
theorem signs16574 : ∀ j, Signs p16574 (bank16574 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16575 := params 30
abbrev ray16575 := rays 30
def bank16575 : Fin 1 → Cell := oneBank p16575 ray16575
theorem signs16575 : ∀ j, Signs p16575 (bank16575 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16576 := params 31
abbrev ray16576 := rays 31
def bank16576 : Fin 1 → Cell := oneBank p16576 ray16576
theorem signs16576 : ∀ j, Signs p16576 (bank16576 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16545_16576
