/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages15009_15040
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![95394667597148,95394210115097,95393752616981,95393295102800,95392837572554,95392380026244,95391922463869,95391464885430,95391007290927,95390549680360,95390092053729,95389634411034,95389176752275,95388719077452,95388261386566,95387803679616,95387345956603,95386888217527,95386430462387,95385972691184,95385514903919,95385057100591,95384599281200,95384141445746,95383683594230,95383225726652,95382767843011,95382309943308,95381852027543,95381394095716,95380936147827,95380478183877,95380020203865]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (15008+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p15009 := params 0
abbrev ray15009 := rays 0
def bank15009 : Fin 1 → Cell := oneBank p15009 ray15009
theorem signs15009 : ∀ j, Signs p15009 (bank15009 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15010 := params 1
abbrev ray15010 := rays 1
def bank15010 : Fin 1 → Cell := oneBank p15010 ray15010
theorem signs15010 : ∀ j, Signs p15010 (bank15010 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15011 := params 2
abbrev ray15011 := rays 2
def bank15011 : Fin 1 → Cell := oneBank p15011 ray15011
theorem signs15011 : ∀ j, Signs p15011 (bank15011 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15012 := params 3
abbrev ray15012 := rays 3
def bank15012 : Fin 1 → Cell := oneBank p15012 ray15012
theorem signs15012 : ∀ j, Signs p15012 (bank15012 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15013 := params 4
abbrev ray15013 := rays 4
def bank15013 : Fin 1 → Cell := oneBank p15013 ray15013
theorem signs15013 : ∀ j, Signs p15013 (bank15013 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15014 := params 5
abbrev ray15014 := rays 5
def bank15014 : Fin 1 → Cell := oneBank p15014 ray15014
theorem signs15014 : ∀ j, Signs p15014 (bank15014 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15015 := params 6
abbrev ray15015 := rays 6
def bank15015 : Fin 1 → Cell := oneBank p15015 ray15015
theorem signs15015 : ∀ j, Signs p15015 (bank15015 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15016 := params 7
abbrev ray15016 := rays 7
def bank15016 : Fin 1 → Cell := oneBank p15016 ray15016
theorem signs15016 : ∀ j, Signs p15016 (bank15016 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15017 := params 8
abbrev ray15017 := rays 8
def bank15017 : Fin 1 → Cell := oneBank p15017 ray15017
theorem signs15017 : ∀ j, Signs p15017 (bank15017 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15018 := params 9
abbrev ray15018 := rays 9
def bank15018 : Fin 1 → Cell := oneBank p15018 ray15018
theorem signs15018 : ∀ j, Signs p15018 (bank15018 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15019 := params 10
abbrev ray15019 := rays 10
def bank15019 : Fin 1 → Cell := oneBank p15019 ray15019
theorem signs15019 : ∀ j, Signs p15019 (bank15019 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15020 := params 11
abbrev ray15020 := rays 11
def bank15020 : Fin 1 → Cell := oneBank p15020 ray15020
theorem signs15020 : ∀ j, Signs p15020 (bank15020 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15021 := params 12
abbrev ray15021 := rays 12
def bank15021 : Fin 1 → Cell := oneBank p15021 ray15021
theorem signs15021 : ∀ j, Signs p15021 (bank15021 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15022 := params 13
abbrev ray15022 := rays 13
def bank15022 : Fin 1 → Cell := oneBank p15022 ray15022
theorem signs15022 : ∀ j, Signs p15022 (bank15022 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15023 := params 14
abbrev ray15023 := rays 14
def bank15023 : Fin 1 → Cell := oneBank p15023 ray15023
theorem signs15023 : ∀ j, Signs p15023 (bank15023 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15024 := params 15
abbrev ray15024 := rays 15
def bank15024 : Fin 1 → Cell := oneBank p15024 ray15024
theorem signs15024 : ∀ j, Signs p15024 (bank15024 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15025 := params 16
abbrev ray15025 := rays 16
def bank15025 : Fin 1 → Cell := oneBank p15025 ray15025
theorem signs15025 : ∀ j, Signs p15025 (bank15025 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15026 := params 17
abbrev ray15026 := rays 17
def bank15026 : Fin 1 → Cell := oneBank p15026 ray15026
theorem signs15026 : ∀ j, Signs p15026 (bank15026 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15027 := params 18
abbrev ray15027 := rays 18
def bank15027 : Fin 1 → Cell := oneBank p15027 ray15027
theorem signs15027 : ∀ j, Signs p15027 (bank15027 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15028 := params 19
abbrev ray15028 := rays 19
def bank15028 : Fin 1 → Cell := oneBank p15028 ray15028
theorem signs15028 : ∀ j, Signs p15028 (bank15028 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15029 := params 20
abbrev ray15029 := rays 20
def bank15029 : Fin 1 → Cell := oneBank p15029 ray15029
theorem signs15029 : ∀ j, Signs p15029 (bank15029 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15030 := params 21
abbrev ray15030 := rays 21
def bank15030 : Fin 1 → Cell := oneBank p15030 ray15030
theorem signs15030 : ∀ j, Signs p15030 (bank15030 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15031 := params 22
abbrev ray15031 := rays 22
def bank15031 : Fin 1 → Cell := oneBank p15031 ray15031
theorem signs15031 : ∀ j, Signs p15031 (bank15031 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15032 := params 23
abbrev ray15032 := rays 23
def bank15032 : Fin 1 → Cell := oneBank p15032 ray15032
theorem signs15032 : ∀ j, Signs p15032 (bank15032 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15033 := params 24
abbrev ray15033 := rays 24
def bank15033 : Fin 1 → Cell := oneBank p15033 ray15033
theorem signs15033 : ∀ j, Signs p15033 (bank15033 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15034 := params 25
abbrev ray15034 := rays 25
def bank15034 : Fin 1 → Cell := oneBank p15034 ray15034
theorem signs15034 : ∀ j, Signs p15034 (bank15034 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15035 := params 26
abbrev ray15035 := rays 26
def bank15035 : Fin 1 → Cell := oneBank p15035 ray15035
theorem signs15035 : ∀ j, Signs p15035 (bank15035 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15036 := params 27
abbrev ray15036 := rays 27
def bank15036 : Fin 1 → Cell := oneBank p15036 ray15036
theorem signs15036 : ∀ j, Signs p15036 (bank15036 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15037 := params 28
abbrev ray15037 := rays 28
def bank15037 : Fin 1 → Cell := oneBank p15037 ray15037
theorem signs15037 : ∀ j, Signs p15037 (bank15037 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15038 := params 29
abbrev ray15038 := rays 29
def bank15038 : Fin 1 → Cell := oneBank p15038 ray15038
theorem signs15038 : ∀ j, Signs p15038 (bank15038 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15039 := params 30
abbrev ray15039 := rays 30
def bank15039 : Fin 1 → Cell := oneBank p15039 ray15039
theorem signs15039 : ∀ j, Signs p15039 (bank15039 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p15040 := params 31
abbrev ray15040 := rays 31
def bank15040 : Fin 1 → Cell := oneBank p15040 ray15040
theorem signs15040 : ∀ j, Signs p15040 (bank15040 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages15009_15040
