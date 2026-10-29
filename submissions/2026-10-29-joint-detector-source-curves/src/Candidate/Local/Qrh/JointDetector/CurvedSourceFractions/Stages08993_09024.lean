/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages08993_09024
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![97828878945837,97828533102224,97828187237681,97827841352210,97827495445811,97827149518484,97826803570230,97826457601050,97826111610944,97825765599913,97825419567958,97825073515079,97824727441277,97824381346552,97824035230905,97823689094337,97823342936848,97822996758439,97822650559111,97822304338864,97821958097699,97821611835617,97821265552618,97820919248702,97820572923871,97820226578125,97819880211464,97819533823889,97819187415401,97818840986001,97818494535689,97818148064465,97817801572331]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (8992+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![clippedRay (params 0),clippedRay (params 1),clippedRay (params 2),clippedRay (params 3),clippedRay (params 4),clippedRay (params 5),clippedRay (params 6),clippedRay (params 7),clippedRay (params 8),clippedRay (params 9),clippedRay (params 10),clippedRay (params 11),clippedRay (params 12),clippedRay (params 13),clippedRay (params 14),clippedRay (params 15),clippedRay (params 16),clippedRay (params 17),clippedRay (params 18),clippedRay (params 19),clippedRay (params 20),clippedRay (params 21),clippedRay (params 22),clippedRay (params 23),clippedRay (params 24),clippedRay (params 25),clippedRay (params 26),clippedRay (params 27),clippedRay (params 28),clippedRay (params 29),clippedRay (params 30),clippedRay (params 31)]
abbrev p8993 := params 0
abbrev ray8993 := rays 0
def bank8993 : Fin 2 → Cell := twoBank p8993 ray8993
theorem signs8993 : ∀ j, Signs p8993 (bank8993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8994 := params 1
abbrev ray8994 := rays 1
def bank8994 : Fin 2 → Cell := twoBank p8994 ray8994
theorem signs8994 : ∀ j, Signs p8994 (bank8994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8995 := params 2
abbrev ray8995 := rays 2
def bank8995 : Fin 2 → Cell := twoBank p8995 ray8995
theorem signs8995 : ∀ j, Signs p8995 (bank8995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8996 := params 3
abbrev ray8996 := rays 3
def bank8996 : Fin 2 → Cell := twoBank p8996 ray8996
theorem signs8996 : ∀ j, Signs p8996 (bank8996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8997 := params 4
abbrev ray8997 := rays 4
def bank8997 : Fin 2 → Cell := twoBank p8997 ray8997
theorem signs8997 : ∀ j, Signs p8997 (bank8997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8998 := params 5
abbrev ray8998 := rays 5
def bank8998 : Fin 2 → Cell := twoBank p8998 ray8998
theorem signs8998 : ∀ j, Signs p8998 (bank8998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p8999 := params 6
abbrev ray8999 := rays 6
def bank8999 : Fin 2 → Cell := twoBank p8999 ray8999
theorem signs8999 : ∀ j, Signs p8999 (bank8999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9000 := params 7
abbrev ray9000 := rays 7
def bank9000 : Fin 2 → Cell := twoBank p9000 ray9000
theorem signs9000 : ∀ j, Signs p9000 (bank9000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9001 := params 8
abbrev ray9001 := rays 8
def bank9001 : Fin 2 → Cell := twoBank p9001 ray9001
theorem signs9001 : ∀ j, Signs p9001 (bank9001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9002 := params 9
abbrev ray9002 := rays 9
def bank9002 : Fin 2 → Cell := twoBank p9002 ray9002
theorem signs9002 : ∀ j, Signs p9002 (bank9002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9003 := params 10
abbrev ray9003 := rays 10
def bank9003 : Fin 2 → Cell := twoBank p9003 ray9003
theorem signs9003 : ∀ j, Signs p9003 (bank9003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9004 := params 11
abbrev ray9004 := rays 11
def bank9004 : Fin 2 → Cell := twoBank p9004 ray9004
theorem signs9004 : ∀ j, Signs p9004 (bank9004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9005 := params 12
abbrev ray9005 := rays 12
def bank9005 : Fin 2 → Cell := twoBank p9005 ray9005
theorem signs9005 : ∀ j, Signs p9005 (bank9005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9006 := params 13
abbrev ray9006 := rays 13
def bank9006 : Fin 2 → Cell := twoBank p9006 ray9006
theorem signs9006 : ∀ j, Signs p9006 (bank9006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9007 := params 14
abbrev ray9007 := rays 14
def bank9007 : Fin 2 → Cell := twoBank p9007 ray9007
theorem signs9007 : ∀ j, Signs p9007 (bank9007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9008 := params 15
abbrev ray9008 := rays 15
def bank9008 : Fin 2 → Cell := twoBank p9008 ray9008
theorem signs9008 : ∀ j, Signs p9008 (bank9008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9009 := params 16
abbrev ray9009 := rays 16
def bank9009 : Fin 2 → Cell := twoBank p9009 ray9009
theorem signs9009 : ∀ j, Signs p9009 (bank9009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9010 := params 17
abbrev ray9010 := rays 17
def bank9010 : Fin 2 → Cell := twoBank p9010 ray9010
theorem signs9010 : ∀ j, Signs p9010 (bank9010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9011 := params 18
abbrev ray9011 := rays 18
def bank9011 : Fin 2 → Cell := twoBank p9011 ray9011
theorem signs9011 : ∀ j, Signs p9011 (bank9011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9012 := params 19
abbrev ray9012 := rays 19
def bank9012 : Fin 2 → Cell := twoBank p9012 ray9012
theorem signs9012 : ∀ j, Signs p9012 (bank9012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9013 := params 20
abbrev ray9013 := rays 20
def bank9013 : Fin 2 → Cell := twoBank p9013 ray9013
theorem signs9013 : ∀ j, Signs p9013 (bank9013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9014 := params 21
abbrev ray9014 := rays 21
def bank9014 : Fin 2 → Cell := twoBank p9014 ray9014
theorem signs9014 : ∀ j, Signs p9014 (bank9014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9015 := params 22
abbrev ray9015 := rays 22
def bank9015 : Fin 2 → Cell := twoBank p9015 ray9015
theorem signs9015 : ∀ j, Signs p9015 (bank9015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9016 := params 23
abbrev ray9016 := rays 23
def bank9016 : Fin 2 → Cell := twoBank p9016 ray9016
theorem signs9016 : ∀ j, Signs p9016 (bank9016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9017 := params 24
abbrev ray9017 := rays 24
def bank9017 : Fin 2 → Cell := twoBank p9017 ray9017
theorem signs9017 : ∀ j, Signs p9017 (bank9017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9018 := params 25
abbrev ray9018 := rays 25
def bank9018 : Fin 2 → Cell := twoBank p9018 ray9018
theorem signs9018 : ∀ j, Signs p9018 (bank9018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9019 := params 26
abbrev ray9019 := rays 26
def bank9019 : Fin 2 → Cell := twoBank p9019 ray9019
theorem signs9019 : ∀ j, Signs p9019 (bank9019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9020 := params 27
abbrev ray9020 := rays 27
def bank9020 : Fin 2 → Cell := twoBank p9020 ray9020
theorem signs9020 : ∀ j, Signs p9020 (bank9020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9021 := params 28
abbrev ray9021 := rays 28
def bank9021 : Fin 2 → Cell := twoBank p9021 ray9021
theorem signs9021 : ∀ j, Signs p9021 (bank9021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9022 := params 29
abbrev ray9022 := rays 29
def bank9022 : Fin 2 → Cell := twoBank p9022 ray9022
theorem signs9022 : ∀ j, Signs p9022 (bank9022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9023 := params 30
abbrev ray9023 := rays 30
def bank9023 : Fin 2 → Cell := twoBank p9023 ray9023
theorem signs9023 : ∀ j, Signs p9023 (bank9023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p9024 := params 31
abbrev ray9024 := rays 31
def bank9024 : Fin 2 → Cell := twoBank p9024 ray9024
theorem signs9024 : ∀ j, Signs p9024 (bank9024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages08993_09024
