/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages14561_14592
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95598002024886,95597551752107,95597101463207,95596651158185,95596200837042,95595750499777,95595300146391,95594849776884,95594399391256,95593948989508,95593498571639,95593048137650,95592597687540,95592147221310,95591696738960,95591246240490,95590795725901,95590345195192,95589894648364,95589444085417,95588993506350,95588542911164,95588092299860,95587641672437,95587191028895,95586740369235,95586289693457,95585839001560,95585388293545,95584937569412,95584486829162,95584036072794,95583585300309]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (14560+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p14561 := params 0
abbrev ray14561 := rays 0
def bank14561 : Fin 1 → Cell := oneBank p14561 ray14561
theorem signs14561 : ∀ j, Signs p14561 (bank14561 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14562 := params 1
abbrev ray14562 := rays 1
def bank14562 : Fin 1 → Cell := oneBank p14562 ray14562
theorem signs14562 : ∀ j, Signs p14562 (bank14562 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14563 := params 2
abbrev ray14563 := rays 2
def bank14563 : Fin 1 → Cell := oneBank p14563 ray14563
theorem signs14563 : ∀ j, Signs p14563 (bank14563 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14564 := params 3
abbrev ray14564 := rays 3
def bank14564 : Fin 1 → Cell := oneBank p14564 ray14564
theorem signs14564 : ∀ j, Signs p14564 (bank14564 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14565 := params 4
abbrev ray14565 := rays 4
def bank14565 : Fin 1 → Cell := oneBank p14565 ray14565
theorem signs14565 : ∀ j, Signs p14565 (bank14565 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14566 := params 5
abbrev ray14566 := rays 5
def bank14566 : Fin 1 → Cell := oneBank p14566 ray14566
theorem signs14566 : ∀ j, Signs p14566 (bank14566 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14567 := params 6
abbrev ray14567 := rays 6
def bank14567 : Fin 1 → Cell := oneBank p14567 ray14567
theorem signs14567 : ∀ j, Signs p14567 (bank14567 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14568 := params 7
abbrev ray14568 := rays 7
def bank14568 : Fin 1 → Cell := oneBank p14568 ray14568
theorem signs14568 : ∀ j, Signs p14568 (bank14568 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14569 := params 8
abbrev ray14569 := rays 8
def bank14569 : Fin 1 → Cell := oneBank p14569 ray14569
theorem signs14569 : ∀ j, Signs p14569 (bank14569 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14570 := params 9
abbrev ray14570 := rays 9
def bank14570 : Fin 1 → Cell := oneBank p14570 ray14570
theorem signs14570 : ∀ j, Signs p14570 (bank14570 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14571 := params 10
abbrev ray14571 := rays 10
def bank14571 : Fin 1 → Cell := oneBank p14571 ray14571
theorem signs14571 : ∀ j, Signs p14571 (bank14571 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14572 := params 11
abbrev ray14572 := rays 11
def bank14572 : Fin 1 → Cell := oneBank p14572 ray14572
theorem signs14572 : ∀ j, Signs p14572 (bank14572 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14573 := params 12
abbrev ray14573 := rays 12
def bank14573 : Fin 1 → Cell := oneBank p14573 ray14573
theorem signs14573 : ∀ j, Signs p14573 (bank14573 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14574 := params 13
abbrev ray14574 := rays 13
def bank14574 : Fin 1 → Cell := oneBank p14574 ray14574
theorem signs14574 : ∀ j, Signs p14574 (bank14574 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14575 := params 14
abbrev ray14575 := rays 14
def bank14575 : Fin 1 → Cell := oneBank p14575 ray14575
theorem signs14575 : ∀ j, Signs p14575 (bank14575 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14576 := params 15
abbrev ray14576 := rays 15
def bank14576 : Fin 1 → Cell := oneBank p14576 ray14576
theorem signs14576 : ∀ j, Signs p14576 (bank14576 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14577 := params 16
abbrev ray14577 := rays 16
def bank14577 : Fin 1 → Cell := oneBank p14577 ray14577
theorem signs14577 : ∀ j, Signs p14577 (bank14577 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14578 := params 17
abbrev ray14578 := rays 17
def bank14578 : Fin 1 → Cell := oneBank p14578 ray14578
theorem signs14578 : ∀ j, Signs p14578 (bank14578 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14579 := params 18
abbrev ray14579 := rays 18
def bank14579 : Fin 1 → Cell := oneBank p14579 ray14579
theorem signs14579 : ∀ j, Signs p14579 (bank14579 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14580 := params 19
abbrev ray14580 := rays 19
def bank14580 : Fin 1 → Cell := oneBank p14580 ray14580
theorem signs14580 : ∀ j, Signs p14580 (bank14580 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14581 := params 20
abbrev ray14581 := rays 20
def bank14581 : Fin 1 → Cell := oneBank p14581 ray14581
theorem signs14581 : ∀ j, Signs p14581 (bank14581 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14582 := params 21
abbrev ray14582 := rays 21
def bank14582 : Fin 1 → Cell := oneBank p14582 ray14582
theorem signs14582 : ∀ j, Signs p14582 (bank14582 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14583 := params 22
abbrev ray14583 := rays 22
def bank14583 : Fin 1 → Cell := oneBank p14583 ray14583
theorem signs14583 : ∀ j, Signs p14583 (bank14583 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14584 := params 23
abbrev ray14584 := rays 23
def bank14584 : Fin 1 → Cell := oneBank p14584 ray14584
theorem signs14584 : ∀ j, Signs p14584 (bank14584 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14585 := params 24
abbrev ray14585 := rays 24
def bank14585 : Fin 1 → Cell := oneBank p14585 ray14585
theorem signs14585 : ∀ j, Signs p14585 (bank14585 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14586 := params 25
abbrev ray14586 := rays 25
def bank14586 : Fin 1 → Cell := oneBank p14586 ray14586
theorem signs14586 : ∀ j, Signs p14586 (bank14586 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14587 := params 26
abbrev ray14587 := rays 26
def bank14587 : Fin 1 → Cell := oneBank p14587 ray14587
theorem signs14587 : ∀ j, Signs p14587 (bank14587 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14588 := params 27
abbrev ray14588 := rays 27
def bank14588 : Fin 1 → Cell := oneBank p14588 ray14588
theorem signs14588 : ∀ j, Signs p14588 (bank14588 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14589 := params 28
abbrev ray14589 := rays 28
def bank14589 : Fin 1 → Cell := oneBank p14589 ray14589
theorem signs14589 : ∀ j, Signs p14589 (bank14589 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14590 := params 29
abbrev ray14590 := rays 29
def bank14590 : Fin 1 → Cell := oneBank p14590 ray14590
theorem signs14590 : ∀ j, Signs p14590 (bank14590 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14591 := params 30
abbrev ray14591 := rays 30
def bank14591 : Fin 1 → Cell := oneBank p14591 ray14591
theorem signs14591 : ∀ j, Signs p14591 (bank14591 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p14592 := params 31
abbrev ray14592 := rays 31
def bank14592 : Fin 1 → Cell := oneBank p14592 ray14592
theorem signs14592 : ∀ j, Signs p14592 (bank14592 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages14561_14592
