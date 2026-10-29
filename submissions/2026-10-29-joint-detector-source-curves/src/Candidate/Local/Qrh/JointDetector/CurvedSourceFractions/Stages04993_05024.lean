/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages04993_05024
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99037262665174,99037006407090,99036750124896,99036493818593,99036237488181,99035981133662,99035724755037,99035468352307,99035211925472,99034955474534,99034698999494,99034442500353,99034185977111,99033929429770,99033672858331,99033416262794,99033159643161,99032902999433,99032646331611,99032389639695,99032132923687,99031876183588,99031619419398,99031362631119,99031105818752,99030848982297,99030592121756,99030335237130,99030078328419,99029821395625,99029564438749,99029307457791,99029050452753]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (4992+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p4993 := params 0
abbrev ray4993 := rays 0
def bank4993 : Fin 2 → Cell := twoBank p4993 ray4993
theorem signs4993 : ∀ j, Signs p4993 (bank4993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4994 := params 1
abbrev ray4994 := rays 1
def bank4994 : Fin 2 → Cell := twoBank p4994 ray4994
theorem signs4994 : ∀ j, Signs p4994 (bank4994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4995 := params 2
abbrev ray4995 := rays 2
def bank4995 : Fin 2 → Cell := twoBank p4995 ray4995
theorem signs4995 : ∀ j, Signs p4995 (bank4995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4996 := params 3
abbrev ray4996 := rays 3
def bank4996 : Fin 2 → Cell := twoBank p4996 ray4996
theorem signs4996 : ∀ j, Signs p4996 (bank4996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4997 := params 4
abbrev ray4997 := rays 4
def bank4997 : Fin 2 → Cell := twoBank p4997 ray4997
theorem signs4997 : ∀ j, Signs p4997 (bank4997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4998 := params 5
abbrev ray4998 := rays 5
def bank4998 : Fin 2 → Cell := twoBank p4998 ray4998
theorem signs4998 : ∀ j, Signs p4998 (bank4998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p4999 := params 6
abbrev ray4999 := rays 6
def bank4999 : Fin 2 → Cell := twoBank p4999 ray4999
theorem signs4999 : ∀ j, Signs p4999 (bank4999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5000 := params 7
abbrev ray5000 := rays 7
def bank5000 : Fin 2 → Cell := twoBank p5000 ray5000
theorem signs5000 : ∀ j, Signs p5000 (bank5000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5001 := params 8
abbrev ray5001 := rays 8
def bank5001 : Fin 2 → Cell := twoBank p5001 ray5001
theorem signs5001 : ∀ j, Signs p5001 (bank5001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5002 := params 9
abbrev ray5002 := rays 9
def bank5002 : Fin 2 → Cell := twoBank p5002 ray5002
theorem signs5002 : ∀ j, Signs p5002 (bank5002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5003 := params 10
abbrev ray5003 := rays 10
def bank5003 : Fin 2 → Cell := twoBank p5003 ray5003
theorem signs5003 : ∀ j, Signs p5003 (bank5003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5004 := params 11
abbrev ray5004 := rays 11
def bank5004 : Fin 2 → Cell := twoBank p5004 ray5004
theorem signs5004 : ∀ j, Signs p5004 (bank5004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5005 := params 12
abbrev ray5005 := rays 12
def bank5005 : Fin 2 → Cell := twoBank p5005 ray5005
theorem signs5005 : ∀ j, Signs p5005 (bank5005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5006 := params 13
abbrev ray5006 := rays 13
def bank5006 : Fin 2 → Cell := twoBank p5006 ray5006
theorem signs5006 : ∀ j, Signs p5006 (bank5006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5007 := params 14
abbrev ray5007 := rays 14
def bank5007 : Fin 2 → Cell := twoBank p5007 ray5007
theorem signs5007 : ∀ j, Signs p5007 (bank5007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5008 := params 15
abbrev ray5008 := rays 15
def bank5008 : Fin 2 → Cell := twoBank p5008 ray5008
theorem signs5008 : ∀ j, Signs p5008 (bank5008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5009 := params 16
abbrev ray5009 := rays 16
def bank5009 : Fin 2 → Cell := twoBank p5009 ray5009
theorem signs5009 : ∀ j, Signs p5009 (bank5009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5010 := params 17
abbrev ray5010 := rays 17
def bank5010 : Fin 2 → Cell := twoBank p5010 ray5010
theorem signs5010 : ∀ j, Signs p5010 (bank5010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5011 := params 18
abbrev ray5011 := rays 18
def bank5011 : Fin 2 → Cell := twoBank p5011 ray5011
theorem signs5011 : ∀ j, Signs p5011 (bank5011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5012 := params 19
abbrev ray5012 := rays 19
def bank5012 : Fin 2 → Cell := twoBank p5012 ray5012
theorem signs5012 : ∀ j, Signs p5012 (bank5012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5013 := params 20
abbrev ray5013 := rays 20
def bank5013 : Fin 2 → Cell := twoBank p5013 ray5013
theorem signs5013 : ∀ j, Signs p5013 (bank5013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5014 := params 21
abbrev ray5014 := rays 21
def bank5014 : Fin 2 → Cell := twoBank p5014 ray5014
theorem signs5014 : ∀ j, Signs p5014 (bank5014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5015 := params 22
abbrev ray5015 := rays 22
def bank5015 : Fin 2 → Cell := twoBank p5015 ray5015
theorem signs5015 : ∀ j, Signs p5015 (bank5015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5016 := params 23
abbrev ray5016 := rays 23
def bank5016 : Fin 2 → Cell := twoBank p5016 ray5016
theorem signs5016 : ∀ j, Signs p5016 (bank5016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5017 := params 24
abbrev ray5017 := rays 24
def bank5017 : Fin 2 → Cell := twoBank p5017 ray5017
theorem signs5017 : ∀ j, Signs p5017 (bank5017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5018 := params 25
abbrev ray5018 := rays 25
def bank5018 : Fin 2 → Cell := twoBank p5018 ray5018
theorem signs5018 : ∀ j, Signs p5018 (bank5018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5019 := params 26
abbrev ray5019 := rays 26
def bank5019 : Fin 2 → Cell := twoBank p5019 ray5019
theorem signs5019 : ∀ j, Signs p5019 (bank5019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5020 := params 27
abbrev ray5020 := rays 27
def bank5020 : Fin 2 → Cell := twoBank p5020 ray5020
theorem signs5020 : ∀ j, Signs p5020 (bank5020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5021 := params 28
abbrev ray5021 := rays 28
def bank5021 : Fin 2 → Cell := twoBank p5021 ray5021
theorem signs5021 : ∀ j, Signs p5021 (bank5021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5022 := params 29
abbrev ray5022 := rays 29
def bank5022 : Fin 2 → Cell := twoBank p5022 ray5022
theorem signs5022 : ∀ j, Signs p5022 (bank5022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5023 := params 30
abbrev ray5023 := rays 30
def bank5023 : Fin 2 → Cell := twoBank p5023 ray5023
theorem signs5023 : ∀ j, Signs p5023 (bank5023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p5024 := params 31
abbrev ray5024 := rays 31
def bank5024 : Fin 2 → Cell := twoBank p5024 ray5024
theorem signs5024 : ∀ j, Signs p5024 (bank5024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages04993_05024
