/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08001_08032
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![98161542704515,98161217942251,98160893158402,98160568352968,98160243525950,98159918677349,98159593807165,98159268915399,98158944002052,98158619067125,98158294110618,98157969132532,98157644132868,98157319111626,98156994068807,98156669004412,98156343918441,98156018810895,98155693681775,98155368531082,98155043358816,98154718164978,98154392949569,98154067712589,98153742454039,98153417173920,98153091872232,98152766548976,98152441204153,98152115837764,98151790449809,98151465040289,98151139609204]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8000+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8001 := params 0
abbrev ray8001 := rays 0
def bank8001 : Fin 2 → Cell := twoBank p8001 ray8001
theorem signs8001 : ∀ j, Signs p8001 (bank8001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8002 := params 1
abbrev ray8002 := rays 1
def bank8002 : Fin 2 → Cell := twoBank p8002 ray8002
theorem signs8002 : ∀ j, Signs p8002 (bank8002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8003 := params 2
abbrev ray8003 := rays 2
def bank8003 : Fin 2 → Cell := twoBank p8003 ray8003
theorem signs8003 : ∀ j, Signs p8003 (bank8003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8004 := params 3
abbrev ray8004 := rays 3
def bank8004 : Fin 2 → Cell := twoBank p8004 ray8004
theorem signs8004 : ∀ j, Signs p8004 (bank8004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8005 := params 4
abbrev ray8005 := rays 4
def bank8005 : Fin 2 → Cell := twoBank p8005 ray8005
theorem signs8005 : ∀ j, Signs p8005 (bank8005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8006 := params 5
abbrev ray8006 := rays 5
def bank8006 : Fin 2 → Cell := twoBank p8006 ray8006
theorem signs8006 : ∀ j, Signs p8006 (bank8006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8007 := params 6
abbrev ray8007 := rays 6
def bank8007 : Fin 2 → Cell := twoBank p8007 ray8007
theorem signs8007 : ∀ j, Signs p8007 (bank8007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8008 := params 7
abbrev ray8008 := rays 7
def bank8008 : Fin 2 → Cell := twoBank p8008 ray8008
theorem signs8008 : ∀ j, Signs p8008 (bank8008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8009 := params 8
abbrev ray8009 := rays 8
def bank8009 : Fin 2 → Cell := twoBank p8009 ray8009
theorem signs8009 : ∀ j, Signs p8009 (bank8009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8010 := params 9
abbrev ray8010 := rays 9
def bank8010 : Fin 2 → Cell := twoBank p8010 ray8010
theorem signs8010 : ∀ j, Signs p8010 (bank8010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8011 := params 10
abbrev ray8011 := rays 10
def bank8011 : Fin 2 → Cell := twoBank p8011 ray8011
theorem signs8011 : ∀ j, Signs p8011 (bank8011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8012 := params 11
abbrev ray8012 := rays 11
def bank8012 : Fin 2 → Cell := twoBank p8012 ray8012
theorem signs8012 : ∀ j, Signs p8012 (bank8012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8013 := params 12
abbrev ray8013 := rays 12
def bank8013 : Fin 2 → Cell := twoBank p8013 ray8013
theorem signs8013 : ∀ j, Signs p8013 (bank8013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8014 := params 13
abbrev ray8014 := rays 13
def bank8014 : Fin 2 → Cell := twoBank p8014 ray8014
theorem signs8014 : ∀ j, Signs p8014 (bank8014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8015 := params 14
abbrev ray8015 := rays 14
def bank8015 : Fin 2 → Cell := twoBank p8015 ray8015
theorem signs8015 : ∀ j, Signs p8015 (bank8015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8016 := params 15
abbrev ray8016 := rays 15
def bank8016 : Fin 2 → Cell := twoBank p8016 ray8016
theorem signs8016 : ∀ j, Signs p8016 (bank8016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8017 := params 16
abbrev ray8017 := rays 16
def bank8017 : Fin 2 → Cell := twoBank p8017 ray8017
theorem signs8017 : ∀ j, Signs p8017 (bank8017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8018 := params 17
abbrev ray8018 := rays 17
def bank8018 : Fin 2 → Cell := twoBank p8018 ray8018
theorem signs8018 : ∀ j, Signs p8018 (bank8018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8019 := params 18
abbrev ray8019 := rays 18
def bank8019 : Fin 2 → Cell := twoBank p8019 ray8019
theorem signs8019 : ∀ j, Signs p8019 (bank8019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8020 := params 19
abbrev ray8020 := rays 19
def bank8020 : Fin 2 → Cell := twoBank p8020 ray8020
theorem signs8020 : ∀ j, Signs p8020 (bank8020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8021 := params 20
abbrev ray8021 := rays 20
def bank8021 : Fin 2 → Cell := twoBank p8021 ray8021
theorem signs8021 : ∀ j, Signs p8021 (bank8021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8022 := params 21
abbrev ray8022 := rays 21
def bank8022 : Fin 2 → Cell := twoBank p8022 ray8022
theorem signs8022 : ∀ j, Signs p8022 (bank8022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8023 := params 22
abbrev ray8023 := rays 22
def bank8023 : Fin 2 → Cell := twoBank p8023 ray8023
theorem signs8023 : ∀ j, Signs p8023 (bank8023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8024 := params 23
abbrev ray8024 := rays 23
def bank8024 : Fin 2 → Cell := twoBank p8024 ray8024
theorem signs8024 : ∀ j, Signs p8024 (bank8024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8025 := params 24
abbrev ray8025 := rays 24
def bank8025 : Fin 2 → Cell := twoBank p8025 ray8025
theorem signs8025 : ∀ j, Signs p8025 (bank8025 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8026 := params 25
abbrev ray8026 := rays 25
def bank8026 : Fin 2 → Cell := twoBank p8026 ray8026
theorem signs8026 : ∀ j, Signs p8026 (bank8026 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8027 := params 26
abbrev ray8027 := rays 26
def bank8027 : Fin 2 → Cell := twoBank p8027 ray8027
theorem signs8027 : ∀ j, Signs p8027 (bank8027 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8028 := params 27
abbrev ray8028 := rays 27
def bank8028 : Fin 2 → Cell := twoBank p8028 ray8028
theorem signs8028 : ∀ j, Signs p8028 (bank8028 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8029 := params 28
abbrev ray8029 := rays 28
def bank8029 : Fin 2 → Cell := twoBank p8029 ray8029
theorem signs8029 : ∀ j, Signs p8029 (bank8029 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8030 := params 29
abbrev ray8030 := rays 29
def bank8030 : Fin 2 → Cell := twoBank p8030 ray8030
theorem signs8030 : ∀ j, Signs p8030 (bank8030 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8031 := params 30
abbrev ray8031 := rays 30
def bank8031 : Fin 2 → Cell := twoBank p8031 ray8031
theorem signs8031 : ∀ j, Signs p8031 (bank8031 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8032 := params 31
abbrev ray8032 := rays 31
def bank8032 : Fin 2 → Cell := twoBank p8032 ray8032
theorem signs8032 : ∀ j, Signs p8032 (bank8032 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08001_08032
