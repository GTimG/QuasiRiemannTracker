/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages02561_02592
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99586569500842,99586375144103,99586180760428,99585986349819,99585791912277,99585597447803,99585402956399,99585208438066,99585013892805,99584819320618,99584624721506,99584430095471,99584235442513,99584040762635,99583846055837,99583651322121,99583456561488,99583261773939,99583066959476,99582872118100,99582677249813,99582482354616,99582287432510,99582092483497,99581897507577,99581702504753,99581507475025,99581312418395,99581117334864,99580922224434,99580727087106,99580531922881,99580336731761]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (2560+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p2561 := params 0
abbrev ray2561 := rays 0
def bank2561 : Fin 2 → Cell := twoBank p2561 ray2561
theorem signs2561 : ∀ j, Signs p2561 (bank2561 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2562 := params 1
abbrev ray2562 := rays 1
def bank2562 : Fin 2 → Cell := twoBank p2562 ray2562
theorem signs2562 : ∀ j, Signs p2562 (bank2562 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2563 := params 2
abbrev ray2563 := rays 2
def bank2563 : Fin 2 → Cell := twoBank p2563 ray2563
theorem signs2563 : ∀ j, Signs p2563 (bank2563 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2564 := params 3
abbrev ray2564 := rays 3
def bank2564 : Fin 2 → Cell := twoBank p2564 ray2564
theorem signs2564 : ∀ j, Signs p2564 (bank2564 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2565 := params 4
abbrev ray2565 := rays 4
def bank2565 : Fin 2 → Cell := twoBank p2565 ray2565
theorem signs2565 : ∀ j, Signs p2565 (bank2565 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2566 := params 5
abbrev ray2566 := rays 5
def bank2566 : Fin 2 → Cell := twoBank p2566 ray2566
theorem signs2566 : ∀ j, Signs p2566 (bank2566 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2567 := params 6
abbrev ray2567 := rays 6
def bank2567 : Fin 2 → Cell := twoBank p2567 ray2567
theorem signs2567 : ∀ j, Signs p2567 (bank2567 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2568 := params 7
abbrev ray2568 := rays 7
def bank2568 : Fin 2 → Cell := twoBank p2568 ray2568
theorem signs2568 : ∀ j, Signs p2568 (bank2568 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2569 := params 8
abbrev ray2569 := rays 8
def bank2569 : Fin 2 → Cell := twoBank p2569 ray2569
theorem signs2569 : ∀ j, Signs p2569 (bank2569 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2570 := params 9
abbrev ray2570 := rays 9
def bank2570 : Fin 2 → Cell := twoBank p2570 ray2570
theorem signs2570 : ∀ j, Signs p2570 (bank2570 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2571 := params 10
abbrev ray2571 := rays 10
def bank2571 : Fin 2 → Cell := twoBank p2571 ray2571
theorem signs2571 : ∀ j, Signs p2571 (bank2571 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2572 := params 11
abbrev ray2572 := rays 11
def bank2572 : Fin 2 → Cell := twoBank p2572 ray2572
theorem signs2572 : ∀ j, Signs p2572 (bank2572 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2573 := params 12
abbrev ray2573 := rays 12
def bank2573 : Fin 2 → Cell := twoBank p2573 ray2573
theorem signs2573 : ∀ j, Signs p2573 (bank2573 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2574 := params 13
abbrev ray2574 := rays 13
def bank2574 : Fin 2 → Cell := twoBank p2574 ray2574
theorem signs2574 : ∀ j, Signs p2574 (bank2574 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2575 := params 14
abbrev ray2575 := rays 14
def bank2575 : Fin 2 → Cell := twoBank p2575 ray2575
theorem signs2575 : ∀ j, Signs p2575 (bank2575 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2576 := params 15
abbrev ray2576 := rays 15
def bank2576 : Fin 2 → Cell := twoBank p2576 ray2576
theorem signs2576 : ∀ j, Signs p2576 (bank2576 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2577 := params 16
abbrev ray2577 := rays 16
def bank2577 : Fin 2 → Cell := twoBank p2577 ray2577
theorem signs2577 : ∀ j, Signs p2577 (bank2577 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2578 := params 17
abbrev ray2578 := rays 17
def bank2578 : Fin 2 → Cell := twoBank p2578 ray2578
theorem signs2578 : ∀ j, Signs p2578 (bank2578 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2579 := params 18
abbrev ray2579 := rays 18
def bank2579 : Fin 2 → Cell := twoBank p2579 ray2579
theorem signs2579 : ∀ j, Signs p2579 (bank2579 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2580 := params 19
abbrev ray2580 := rays 19
def bank2580 : Fin 2 → Cell := twoBank p2580 ray2580
theorem signs2580 : ∀ j, Signs p2580 (bank2580 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2581 := params 20
abbrev ray2581 := rays 20
def bank2581 : Fin 2 → Cell := twoBank p2581 ray2581
theorem signs2581 : ∀ j, Signs p2581 (bank2581 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2582 := params 21
abbrev ray2582 := rays 21
def bank2582 : Fin 2 → Cell := twoBank p2582 ray2582
theorem signs2582 : ∀ j, Signs p2582 (bank2582 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2583 := params 22
abbrev ray2583 := rays 22
def bank2583 : Fin 2 → Cell := twoBank p2583 ray2583
theorem signs2583 : ∀ j, Signs p2583 (bank2583 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2584 := params 23
abbrev ray2584 := rays 23
def bank2584 : Fin 2 → Cell := twoBank p2584 ray2584
theorem signs2584 : ∀ j, Signs p2584 (bank2584 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2585 := params 24
abbrev ray2585 := rays 24
def bank2585 : Fin 2 → Cell := twoBank p2585 ray2585
theorem signs2585 : ∀ j, Signs p2585 (bank2585 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2586 := params 25
abbrev ray2586 := rays 25
def bank2586 : Fin 2 → Cell := twoBank p2586 ray2586
theorem signs2586 : ∀ j, Signs p2586 (bank2586 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2587 := params 26
abbrev ray2587 := rays 26
def bank2587 : Fin 2 → Cell := twoBank p2587 ray2587
theorem signs2587 : ∀ j, Signs p2587 (bank2587 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2588 := params 27
abbrev ray2588 := rays 27
def bank2588 : Fin 2 → Cell := twoBank p2588 ray2588
theorem signs2588 : ∀ j, Signs p2588 (bank2588 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2589 := params 28
abbrev ray2589 := rays 28
def bank2589 : Fin 2 → Cell := twoBank p2589 ray2589
theorem signs2589 : ∀ j, Signs p2589 (bank2589 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2590 := params 29
abbrev ray2590 := rays 29
def bank2590 : Fin 2 → Cell := twoBank p2590 ray2590
theorem signs2590 : ∀ j, Signs p2590 (bank2590 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2591 := params 30
abbrev ray2591 := rays 30
def bank2591 : Fin 2 → Cell := twoBank p2591 ray2591
theorem signs2591 : ∀ j, Signs p2591 (bank2591 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2592 := params 31
abbrev ray2592 := rays 31
def bank2592 : Fin 2 → Cell := twoBank p2592 ray2592
theorem signs2592 : ∀ j, Signs p2592 (bank2592 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages02561_02592
