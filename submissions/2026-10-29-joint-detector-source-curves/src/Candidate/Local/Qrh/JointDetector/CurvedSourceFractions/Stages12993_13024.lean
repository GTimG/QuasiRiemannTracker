/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12993_13024
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96284087298393,96283662529002,96283237743173,96282812940905,96282388122199,96281963287054,96281538435472,96281113567452,96280688682995,96280263782101,96279838864770,96279413931002,96278988980798,96278564014158,96278139031083,96277714031572,96277289015626,96276863983245,96276438934429,96276013869179,96275588787495,96275163689377,96274738574825,96274313443840,96273888296422,96273463132571,96273037952287,96272612755571,96272187542423,96271762312843,96271337066831,96270911804388,96270486525514]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12992+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p12993 := params 0
abbrev ray12993 := rays 0
def bank12993 : Fin 1 → Cell := oneBank p12993 ray12993
theorem signs12993 : ∀ j, Signs p12993 (bank12993 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12994 := params 1
abbrev ray12994 := rays 1
def bank12994 : Fin 1 → Cell := oneBank p12994 ray12994
theorem signs12994 : ∀ j, Signs p12994 (bank12994 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12995 := params 2
abbrev ray12995 := rays 2
def bank12995 : Fin 1 → Cell := oneBank p12995 ray12995
theorem signs12995 : ∀ j, Signs p12995 (bank12995 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12996 := params 3
abbrev ray12996 := rays 3
def bank12996 : Fin 1 → Cell := oneBank p12996 ray12996
theorem signs12996 : ∀ j, Signs p12996 (bank12996 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12997 := params 4
abbrev ray12997 := rays 4
def bank12997 : Fin 1 → Cell := oneBank p12997 ray12997
theorem signs12997 : ∀ j, Signs p12997 (bank12997 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12998 := params 5
abbrev ray12998 := rays 5
def bank12998 : Fin 1 → Cell := oneBank p12998 ray12998
theorem signs12998 : ∀ j, Signs p12998 (bank12998 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12999 := params 6
abbrev ray12999 := rays 6
def bank12999 : Fin 1 → Cell := oneBank p12999 ray12999
theorem signs12999 : ∀ j, Signs p12999 (bank12999 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13000 := params 7
abbrev ray13000 := rays 7
def bank13000 : Fin 1 → Cell := oneBank p13000 ray13000
theorem signs13000 : ∀ j, Signs p13000 (bank13000 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13001 := params 8
abbrev ray13001 := rays 8
def bank13001 : Fin 1 → Cell := oneBank p13001 ray13001
theorem signs13001 : ∀ j, Signs p13001 (bank13001 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13002 := params 9
abbrev ray13002 := rays 9
def bank13002 : Fin 1 → Cell := oneBank p13002 ray13002
theorem signs13002 : ∀ j, Signs p13002 (bank13002 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13003 := params 10
abbrev ray13003 := rays 10
def bank13003 : Fin 1 → Cell := oneBank p13003 ray13003
theorem signs13003 : ∀ j, Signs p13003 (bank13003 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13004 := params 11
abbrev ray13004 := rays 11
def bank13004 : Fin 1 → Cell := oneBank p13004 ray13004
theorem signs13004 : ∀ j, Signs p13004 (bank13004 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13005 := params 12
abbrev ray13005 := rays 12
def bank13005 : Fin 1 → Cell := oneBank p13005 ray13005
theorem signs13005 : ∀ j, Signs p13005 (bank13005 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13006 := params 13
abbrev ray13006 := rays 13
def bank13006 : Fin 1 → Cell := oneBank p13006 ray13006
theorem signs13006 : ∀ j, Signs p13006 (bank13006 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13007 := params 14
abbrev ray13007 := rays 14
def bank13007 : Fin 1 → Cell := oneBank p13007 ray13007
theorem signs13007 : ∀ j, Signs p13007 (bank13007 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13008 := params 15
abbrev ray13008 := rays 15
def bank13008 : Fin 1 → Cell := oneBank p13008 ray13008
theorem signs13008 : ∀ j, Signs p13008 (bank13008 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13009 := params 16
abbrev ray13009 := rays 16
def bank13009 : Fin 1 → Cell := oneBank p13009 ray13009
theorem signs13009 : ∀ j, Signs p13009 (bank13009 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13010 := params 17
abbrev ray13010 := rays 17
def bank13010 : Fin 1 → Cell := oneBank p13010 ray13010
theorem signs13010 : ∀ j, Signs p13010 (bank13010 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13011 := params 18
abbrev ray13011 := rays 18
def bank13011 : Fin 1 → Cell := oneBank p13011 ray13011
theorem signs13011 : ∀ j, Signs p13011 (bank13011 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13012 := params 19
abbrev ray13012 := rays 19
def bank13012 : Fin 1 → Cell := oneBank p13012 ray13012
theorem signs13012 : ∀ j, Signs p13012 (bank13012 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13013 := params 20
abbrev ray13013 := rays 20
def bank13013 : Fin 1 → Cell := oneBank p13013 ray13013
theorem signs13013 : ∀ j, Signs p13013 (bank13013 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13014 := params 21
abbrev ray13014 := rays 21
def bank13014 : Fin 1 → Cell := oneBank p13014 ray13014
theorem signs13014 : ∀ j, Signs p13014 (bank13014 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13015 := params 22
abbrev ray13015 := rays 22
def bank13015 : Fin 1 → Cell := oneBank p13015 ray13015
theorem signs13015 : ∀ j, Signs p13015 (bank13015 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13016 := params 23
abbrev ray13016 := rays 23
def bank13016 : Fin 1 → Cell := oneBank p13016 ray13016
theorem signs13016 : ∀ j, Signs p13016 (bank13016 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13017 := params 24
abbrev ray13017 := rays 24
def bank13017 : Fin 1 → Cell := oneBank p13017 ray13017
theorem signs13017 : ∀ j, Signs p13017 (bank13017 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13018 := params 25
abbrev ray13018 := rays 25
def bank13018 : Fin 1 → Cell := oneBank p13018 ray13018
theorem signs13018 : ∀ j, Signs p13018 (bank13018 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13019 := params 26
abbrev ray13019 := rays 26
def bank13019 : Fin 1 → Cell := oneBank p13019 ray13019
theorem signs13019 : ∀ j, Signs p13019 (bank13019 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13020 := params 27
abbrev ray13020 := rays 27
def bank13020 : Fin 1 → Cell := oneBank p13020 ray13020
theorem signs13020 : ∀ j, Signs p13020 (bank13020 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13021 := params 28
abbrev ray13021 := rays 28
def bank13021 : Fin 1 → Cell := oneBank p13021 ray13021
theorem signs13021 : ∀ j, Signs p13021 (bank13021 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13022 := params 29
abbrev ray13022 := rays 29
def bank13022 : Fin 1 → Cell := oneBank p13022 ray13022
theorem signs13022 : ∀ j, Signs p13022 (bank13022 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13023 := params 30
abbrev ray13023 := rays 30
def bank13023 : Fin 1 → Cell := oneBank p13023 ray13023
theorem signs13023 : ∀ j, Signs p13023 (bank13023 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p13024 := params 31
abbrev ray13024 := rays 31
def bank13024 : Fin 1 → Cell := oneBank p13024 ray13024
theorem signs13024 : ∀ j, Signs p13024 (bank13024 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12993_13024
