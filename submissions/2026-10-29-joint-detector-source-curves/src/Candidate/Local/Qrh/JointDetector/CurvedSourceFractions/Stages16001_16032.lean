/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16001_16032
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94932963821926,94932490445609,94932017053299,94931543644997,94931070220703,94930596780417,94930123324139,94929649851869,94929176363607,94928702859354,94928229339109,94927755802872,94927282250643,94926808682422,94926335098210,94925861498006,94925387881810,94924914249623,94924440601444,94923966937274,94923493257112,94923019560959,94922545848814,94922072120678,94921598376551,94921124616432,94920650840322,94920177048221,94919703240129,94919229416045,94918755575970,94918281719904,94917807847847]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16000+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16001 := params 0
abbrev ray16001 := rays 0
def bank16001 : Fin 1 → Cell := oneBank p16001 ray16001
theorem signs16001 : ∀ j, Signs p16001 (bank16001 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16002 := params 1
abbrev ray16002 := rays 1
def bank16002 : Fin 1 → Cell := oneBank p16002 ray16002
theorem signs16002 : ∀ j, Signs p16002 (bank16002 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16003 := params 2
abbrev ray16003 := rays 2
def bank16003 : Fin 1 → Cell := oneBank p16003 ray16003
theorem signs16003 : ∀ j, Signs p16003 (bank16003 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16004 := params 3
abbrev ray16004 := rays 3
def bank16004 : Fin 1 → Cell := oneBank p16004 ray16004
theorem signs16004 : ∀ j, Signs p16004 (bank16004 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16005 := params 4
abbrev ray16005 := rays 4
def bank16005 : Fin 1 → Cell := oneBank p16005 ray16005
theorem signs16005 : ∀ j, Signs p16005 (bank16005 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16006 := params 5
abbrev ray16006 := rays 5
def bank16006 : Fin 1 → Cell := oneBank p16006 ray16006
theorem signs16006 : ∀ j, Signs p16006 (bank16006 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16007 := params 6
abbrev ray16007 := rays 6
def bank16007 : Fin 1 → Cell := oneBank p16007 ray16007
theorem signs16007 : ∀ j, Signs p16007 (bank16007 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16008 := params 7
abbrev ray16008 := rays 7
def bank16008 : Fin 1 → Cell := oneBank p16008 ray16008
theorem signs16008 : ∀ j, Signs p16008 (bank16008 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16009 := params 8
abbrev ray16009 := rays 8
def bank16009 : Fin 1 → Cell := oneBank p16009 ray16009
theorem signs16009 : ∀ j, Signs p16009 (bank16009 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16010 := params 9
abbrev ray16010 := rays 9
def bank16010 : Fin 1 → Cell := oneBank p16010 ray16010
theorem signs16010 : ∀ j, Signs p16010 (bank16010 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16011 := params 10
abbrev ray16011 := rays 10
def bank16011 : Fin 1 → Cell := oneBank p16011 ray16011
theorem signs16011 : ∀ j, Signs p16011 (bank16011 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16012 := params 11
abbrev ray16012 := rays 11
def bank16012 : Fin 1 → Cell := oneBank p16012 ray16012
theorem signs16012 : ∀ j, Signs p16012 (bank16012 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16013 := params 12
abbrev ray16013 := rays 12
def bank16013 : Fin 1 → Cell := oneBank p16013 ray16013
theorem signs16013 : ∀ j, Signs p16013 (bank16013 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16014 := params 13
abbrev ray16014 := rays 13
def bank16014 : Fin 1 → Cell := oneBank p16014 ray16014
theorem signs16014 : ∀ j, Signs p16014 (bank16014 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16015 := params 14
abbrev ray16015 := rays 14
def bank16015 : Fin 1 → Cell := oneBank p16015 ray16015
theorem signs16015 : ∀ j, Signs p16015 (bank16015 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16016 := params 15
abbrev ray16016 := rays 15
def bank16016 : Fin 1 → Cell := oneBank p16016 ray16016
theorem signs16016 : ∀ j, Signs p16016 (bank16016 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16017 := params 16
abbrev ray16017 := rays 16
def bank16017 : Fin 1 → Cell := oneBank p16017 ray16017
theorem signs16017 : ∀ j, Signs p16017 (bank16017 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16018 := params 17
abbrev ray16018 := rays 17
def bank16018 : Fin 1 → Cell := oneBank p16018 ray16018
theorem signs16018 : ∀ j, Signs p16018 (bank16018 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16019 := params 18
abbrev ray16019 := rays 18
def bank16019 : Fin 1 → Cell := oneBank p16019 ray16019
theorem signs16019 : ∀ j, Signs p16019 (bank16019 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16020 := params 19
abbrev ray16020 := rays 19
def bank16020 : Fin 1 → Cell := oneBank p16020 ray16020
theorem signs16020 : ∀ j, Signs p16020 (bank16020 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16021 := params 20
abbrev ray16021 := rays 20
def bank16021 : Fin 1 → Cell := oneBank p16021 ray16021
theorem signs16021 : ∀ j, Signs p16021 (bank16021 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16022 := params 21
abbrev ray16022 := rays 21
def bank16022 : Fin 1 → Cell := oneBank p16022 ray16022
theorem signs16022 : ∀ j, Signs p16022 (bank16022 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16023 := params 22
abbrev ray16023 := rays 22
def bank16023 : Fin 1 → Cell := oneBank p16023 ray16023
theorem signs16023 : ∀ j, Signs p16023 (bank16023 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16024 := params 23
abbrev ray16024 := rays 23
def bank16024 : Fin 1 → Cell := oneBank p16024 ray16024
theorem signs16024 : ∀ j, Signs p16024 (bank16024 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16025 := params 24
abbrev ray16025 := rays 24
def bank16025 : Fin 1 → Cell := oneBank p16025 ray16025
theorem signs16025 : ∀ j, Signs p16025 (bank16025 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16026 := params 25
abbrev ray16026 := rays 25
def bank16026 : Fin 1 → Cell := oneBank p16026 ray16026
theorem signs16026 : ∀ j, Signs p16026 (bank16026 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16027 := params 26
abbrev ray16027 := rays 26
def bank16027 : Fin 1 → Cell := oneBank p16027 ray16027
theorem signs16027 : ∀ j, Signs p16027 (bank16027 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16028 := params 27
abbrev ray16028 := rays 27
def bank16028 : Fin 1 → Cell := oneBank p16028 ray16028
theorem signs16028 : ∀ j, Signs p16028 (bank16028 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16029 := params 28
abbrev ray16029 := rays 28
def bank16029 : Fin 1 → Cell := oneBank p16029 ray16029
theorem signs16029 : ∀ j, Signs p16029 (bank16029 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16030 := params 29
abbrev ray16030 := rays 29
def bank16030 : Fin 1 → Cell := oneBank p16030 ray16030
theorem signs16030 : ∀ j, Signs p16030 (bank16030 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16031 := params 30
abbrev ray16031 := rays 30
def bank16031 : Fin 1 → Cell := oneBank p16031 ray16031
theorem signs16031 : ∀ j, Signs p16031 (bank16031 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16032 := params 31
abbrev ray16032 := rays 31
def bank16032 : Fin 1 → Cell := oneBank p16032 ray16032
theorem signs16032 : ∀ j, Signs p16032 (bank16032 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16001_16032
