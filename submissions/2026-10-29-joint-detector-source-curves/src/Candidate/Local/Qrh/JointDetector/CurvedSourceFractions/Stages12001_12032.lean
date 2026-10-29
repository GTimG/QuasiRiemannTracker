/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages12001_12032
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![96696518310484,96696112022710,96695705715581,96695299389097,96694893043259,96694486678068,96694080293523,96693673889625,96693267466375,96692861023773,96692454561819,96692048080514,96691641579858,96691235059852,96690828520496,96690421961791,96690015383737,96689608786334,96689202169583,96688795533485,96688388878039,96687982203246,96687575509107,96687168795622,96686762062791,96686355310615,96685948539095,96685541748230,96685134938022,96684728108470,96684321259575,96683914391338,96683507503759]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (12000+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p12001 := params 0
abbrev ray12001 := rays 0
def bank12001 : Fin 2 → Cell := twoBank p12001 ray12001
theorem signs12001 : ∀ j, Signs p12001 (bank12001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12002 := params 1
abbrev ray12002 := rays 1
def bank12002 : Fin 2 → Cell := twoBank p12002 ray12002
theorem signs12002 : ∀ j, Signs p12002 (bank12002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12003 := params 2
abbrev ray12003 := rays 2
def bank12003 : Fin 2 → Cell := twoBank p12003 ray12003
theorem signs12003 : ∀ j, Signs p12003 (bank12003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12004 := params 3
abbrev ray12004 := rays 3
def bank12004 : Fin 2 → Cell := twoBank p12004 ray12004
theorem signs12004 : ∀ j, Signs p12004 (bank12004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12005 := params 4
abbrev ray12005 := rays 4
def bank12005 : Fin 2 → Cell := twoBank p12005 ray12005
theorem signs12005 : ∀ j, Signs p12005 (bank12005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12006 := params 5
abbrev ray12006 := rays 5
def bank12006 : Fin 2 → Cell := twoBank p12006 ray12006
theorem signs12006 : ∀ j, Signs p12006 (bank12006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12007 := params 6
abbrev ray12007 := rays 6
def bank12007 : Fin 2 → Cell := twoBank p12007 ray12007
theorem signs12007 : ∀ j, Signs p12007 (bank12007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12008 := params 7
abbrev ray12008 := rays 7
def bank12008 : Fin 2 → Cell := twoBank p12008 ray12008
theorem signs12008 : ∀ j, Signs p12008 (bank12008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12009 := params 8
abbrev ray12009 := rays 8
def bank12009 : Fin 2 → Cell := twoBank p12009 ray12009
theorem signs12009 : ∀ j, Signs p12009 (bank12009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12010 := params 9
abbrev ray12010 := rays 9
def bank12010 : Fin 2 → Cell := twoBank p12010 ray12010
theorem signs12010 : ∀ j, Signs p12010 (bank12010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12011 := params 10
abbrev ray12011 := rays 10
def bank12011 : Fin 2 → Cell := twoBank p12011 ray12011
theorem signs12011 : ∀ j, Signs p12011 (bank12011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12012 := params 11
abbrev ray12012 := rays 11
def bank12012 : Fin 2 → Cell := twoBank p12012 ray12012
theorem signs12012 : ∀ j, Signs p12012 (bank12012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12013 := params 12
abbrev ray12013 := rays 12
def bank12013 : Fin 2 → Cell := twoBank p12013 ray12013
theorem signs12013 : ∀ j, Signs p12013 (bank12013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12014 := params 13
abbrev ray12014 := rays 13
def bank12014 : Fin 2 → Cell := twoBank p12014 ray12014
theorem signs12014 : ∀ j, Signs p12014 (bank12014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12015 := params 14
abbrev ray12015 := rays 14
def bank12015 : Fin 2 → Cell := twoBank p12015 ray12015
theorem signs12015 : ∀ j, Signs p12015 (bank12015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12016 := params 15
abbrev ray12016 := rays 15
def bank12016 : Fin 2 → Cell := twoBank p12016 ray12016
theorem signs12016 : ∀ j, Signs p12016 (bank12016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12017 := params 16
abbrev ray12017 := rays 16
def bank12017 : Fin 2 → Cell := twoBank p12017 ray12017
theorem signs12017 : ∀ j, Signs p12017 (bank12017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12018 := params 17
abbrev ray12018 := rays 17
def bank12018 : Fin 2 → Cell := twoBank p12018 ray12018
theorem signs12018 : ∀ j, Signs p12018 (bank12018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12019 := params 18
abbrev ray12019 := rays 18
def bank12019 : Fin 2 → Cell := twoBank p12019 ray12019
theorem signs12019 : ∀ j, Signs p12019 (bank12019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12020 := params 19
abbrev ray12020 := rays 19
def bank12020 : Fin 2 → Cell := twoBank p12020 ray12020
theorem signs12020 : ∀ j, Signs p12020 (bank12020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12021 := params 20
abbrev ray12021 := rays 20
def bank12021 : Fin 2 → Cell := twoBank p12021 ray12021
theorem signs12021 : ∀ j, Signs p12021 (bank12021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12022 := params 21
abbrev ray12022 := rays 21
def bank12022 : Fin 2 → Cell := twoBank p12022 ray12022
theorem signs12022 : ∀ j, Signs p12022 (bank12022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12023 := params 22
abbrev ray12023 := rays 22
def bank12023 : Fin 2 → Cell := twoBank p12023 ray12023
theorem signs12023 : ∀ j, Signs p12023 (bank12023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12024 := params 23
abbrev ray12024 := rays 23
def bank12024 : Fin 2 → Cell := twoBank p12024 ray12024
theorem signs12024 : ∀ j, Signs p12024 (bank12024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12025 := params 24
abbrev ray12025 := rays 24
def bank12025 : Fin 2 → Cell := twoBank p12025 ray12025
theorem signs12025 : ∀ j, Signs p12025 (bank12025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12026 := params 25
abbrev ray12026 := rays 25
def bank12026 : Fin 2 → Cell := twoBank p12026 ray12026
theorem signs12026 : ∀ j, Signs p12026 (bank12026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12027 := params 26
abbrev ray12027 := rays 26
def bank12027 : Fin 2 → Cell := twoBank p12027 ray12027
theorem signs12027 : ∀ j, Signs p12027 (bank12027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12028 := params 27
abbrev ray12028 := rays 27
def bank12028 : Fin 2 → Cell := twoBank p12028 ray12028
theorem signs12028 : ∀ j, Signs p12028 (bank12028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12029 := params 28
abbrev ray12029 := rays 28
def bank12029 : Fin 2 → Cell := twoBank p12029 ray12029
theorem signs12029 : ∀ j, Signs p12029 (bank12029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12030 := params 29
abbrev ray12030 := rays 29
def bank12030 : Fin 2 → Cell := twoBank p12030 ray12030
theorem signs12030 : ∀ j, Signs p12030 (bank12030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12031 := params 30
abbrev ray12031 := rays 30
def bank12031 : Fin 2 → Cell := twoBank p12031 ray12031
theorem signs12031 : ∀ j, Signs p12031 (bank12031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p12032 := params 31
abbrev ray12032 := rays 31
def bank12032 : Fin 2 → Cell := twoBank p12032 ray12032
theorem signs12032 : ∀ j, Signs p12032 (bank12032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages12001_12032
