/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04001_04032
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99279427945361,99279196116134,99278964261746,99278732382198,99278500477490,99278268547624,99278036592601,99277804612422,99277572607089,99277340576602,99277108520962,99276876440171,99276644334230,99276412203140,99276180046902,99275947865517,99275715658986,99275483427310,99275251170491,99275018888529,99274786581426,99274554249183,99274321891801,99274089509281,99273857101624,99273624668832,99273392210905,99273159727845,99272927219652,99272694686328,99272462127874,99272229544291,99271996935580]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4000+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4001 := params 0
abbrev ray4001 := rays 0
def bank4001 : Fin 2 → Cell := twoBank p4001 ray4001
theorem signs4001 : ∀ j, Signs p4001 (bank4001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4002 := params 1
abbrev ray4002 := rays 1
def bank4002 : Fin 2 → Cell := twoBank p4002 ray4002
theorem signs4002 : ∀ j, Signs p4002 (bank4002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4003 := params 2
abbrev ray4003 := rays 2
def bank4003 : Fin 2 → Cell := twoBank p4003 ray4003
theorem signs4003 : ∀ j, Signs p4003 (bank4003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4004 := params 3
abbrev ray4004 := rays 3
def bank4004 : Fin 2 → Cell := twoBank p4004 ray4004
theorem signs4004 : ∀ j, Signs p4004 (bank4004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4005 := params 4
abbrev ray4005 := rays 4
def bank4005 : Fin 2 → Cell := twoBank p4005 ray4005
theorem signs4005 : ∀ j, Signs p4005 (bank4005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4006 := params 5
abbrev ray4006 := rays 5
def bank4006 : Fin 2 → Cell := twoBank p4006 ray4006
theorem signs4006 : ∀ j, Signs p4006 (bank4006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4007 := params 6
abbrev ray4007 := rays 6
def bank4007 : Fin 2 → Cell := twoBank p4007 ray4007
theorem signs4007 : ∀ j, Signs p4007 (bank4007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4008 := params 7
abbrev ray4008 := rays 7
def bank4008 : Fin 2 → Cell := twoBank p4008 ray4008
theorem signs4008 : ∀ j, Signs p4008 (bank4008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4009 := params 8
abbrev ray4009 := rays 8
def bank4009 : Fin 2 → Cell := twoBank p4009 ray4009
theorem signs4009 : ∀ j, Signs p4009 (bank4009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4010 := params 9
abbrev ray4010 := rays 9
def bank4010 : Fin 2 → Cell := twoBank p4010 ray4010
theorem signs4010 : ∀ j, Signs p4010 (bank4010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4011 := params 10
abbrev ray4011 := rays 10
def bank4011 : Fin 2 → Cell := twoBank p4011 ray4011
theorem signs4011 : ∀ j, Signs p4011 (bank4011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4012 := params 11
abbrev ray4012 := rays 11
def bank4012 : Fin 2 → Cell := twoBank p4012 ray4012
theorem signs4012 : ∀ j, Signs p4012 (bank4012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4013 := params 12
abbrev ray4013 := rays 12
def bank4013 : Fin 2 → Cell := twoBank p4013 ray4013
theorem signs4013 : ∀ j, Signs p4013 (bank4013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4014 := params 13
abbrev ray4014 := rays 13
def bank4014 : Fin 2 → Cell := twoBank p4014 ray4014
theorem signs4014 : ∀ j, Signs p4014 (bank4014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4015 := params 14
abbrev ray4015 := rays 14
def bank4015 : Fin 2 → Cell := twoBank p4015 ray4015
theorem signs4015 : ∀ j, Signs p4015 (bank4015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4016 := params 15
abbrev ray4016 := rays 15
def bank4016 : Fin 2 → Cell := twoBank p4016 ray4016
theorem signs4016 : ∀ j, Signs p4016 (bank4016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4017 := params 16
abbrev ray4017 := rays 16
def bank4017 : Fin 2 → Cell := twoBank p4017 ray4017
theorem signs4017 : ∀ j, Signs p4017 (bank4017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4018 := params 17
abbrev ray4018 := rays 17
def bank4018 : Fin 2 → Cell := twoBank p4018 ray4018
theorem signs4018 : ∀ j, Signs p4018 (bank4018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4019 := params 18
abbrev ray4019 := rays 18
def bank4019 : Fin 2 → Cell := twoBank p4019 ray4019
theorem signs4019 : ∀ j, Signs p4019 (bank4019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4020 := params 19
abbrev ray4020 := rays 19
def bank4020 : Fin 2 → Cell := twoBank p4020 ray4020
theorem signs4020 : ∀ j, Signs p4020 (bank4020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4021 := params 20
abbrev ray4021 := rays 20
def bank4021 : Fin 2 → Cell := twoBank p4021 ray4021
theorem signs4021 : ∀ j, Signs p4021 (bank4021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4022 := params 21
abbrev ray4022 := rays 21
def bank4022 : Fin 2 → Cell := twoBank p4022 ray4022
theorem signs4022 : ∀ j, Signs p4022 (bank4022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4023 := params 22
abbrev ray4023 := rays 22
def bank4023 : Fin 2 → Cell := twoBank p4023 ray4023
theorem signs4023 : ∀ j, Signs p4023 (bank4023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4024 := params 23
abbrev ray4024 := rays 23
def bank4024 : Fin 2 → Cell := twoBank p4024 ray4024
theorem signs4024 : ∀ j, Signs p4024 (bank4024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4025 := params 24
abbrev ray4025 := rays 24
def bank4025 : Fin 2 → Cell := twoBank p4025 ray4025
theorem signs4025 : ∀ j, Signs p4025 (bank4025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4026 := params 25
abbrev ray4026 := rays 25
def bank4026 : Fin 2 → Cell := twoBank p4026 ray4026
theorem signs4026 : ∀ j, Signs p4026 (bank4026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4027 := params 26
abbrev ray4027 := rays 26
def bank4027 : Fin 2 → Cell := twoBank p4027 ray4027
theorem signs4027 : ∀ j, Signs p4027 (bank4027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4028 := params 27
abbrev ray4028 := rays 27
def bank4028 : Fin 2 → Cell := twoBank p4028 ray4028
theorem signs4028 : ∀ j, Signs p4028 (bank4028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4029 := params 28
abbrev ray4029 := rays 28
def bank4029 : Fin 2 → Cell := twoBank p4029 ray4029
theorem signs4029 : ∀ j, Signs p4029 (bank4029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4030 := params 29
abbrev ray4030 := rays 29
def bank4030 : Fin 2 → Cell := twoBank p4030 ray4030
theorem signs4030 : ∀ j, Signs p4030 (bank4030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4031 := params 30
abbrev ray4031 := rays 30
def bank4031 : Fin 2 → Cell := twoBank p4031 ray4031
theorem signs4031 : ∀ j, Signs p4031 (bank4031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4032 := params 31
abbrev ray4032 := rays 31
def bank4032 : Fin 2 → Cell := twoBank p4032 ray4032
theorem signs4032 : ∀ j, Signs p4032 (bank4032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04001_04032
