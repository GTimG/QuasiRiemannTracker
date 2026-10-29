/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages16993_17024
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![94455516663638,94455027428688,94454538177744,94454048910807,94453559627876,94453070328952,94452581014034,94452091683123,94451602336218,94451112973319,94450623594426,94450134199540,94449644788660,94449155361786,94448665918918,94448176460056,94447686985200,94447197494350,94446707987506,94446218464668,94445728925836,94445239371009,94444749800188,94444260213373,94443770610563,94443280991759,94442791356961,94442301706168,94441812039381,94441322356599,94440832657823,94440342943052,94439853212286]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (16992+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]
abbrev p16993 := params 0
abbrev ray16993 := rays 0
def bank16993 : Fin 1 → Cell := oneBank p16993 ray16993
theorem signs16993 : ∀ j, Signs p16993 (bank16993 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16994 := params 1
abbrev ray16994 := rays 1
def bank16994 : Fin 1 → Cell := oneBank p16994 ray16994
theorem signs16994 : ∀ j, Signs p16994 (bank16994 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16995 := params 2
abbrev ray16995 := rays 2
def bank16995 : Fin 1 → Cell := oneBank p16995 ray16995
theorem signs16995 : ∀ j, Signs p16995 (bank16995 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16996 := params 3
abbrev ray16996 := rays 3
def bank16996 : Fin 1 → Cell := oneBank p16996 ray16996
theorem signs16996 : ∀ j, Signs p16996 (bank16996 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16997 := params 4
abbrev ray16997 := rays 4
def bank16997 : Fin 1 → Cell := oneBank p16997 ray16997
theorem signs16997 : ∀ j, Signs p16997 (bank16997 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16998 := params 5
abbrev ray16998 := rays 5
def bank16998 : Fin 1 → Cell := oneBank p16998 ray16998
theorem signs16998 : ∀ j, Signs p16998 (bank16998 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p16999 := params 6
abbrev ray16999 := rays 6
def bank16999 : Fin 1 → Cell := oneBank p16999 ray16999
theorem signs16999 : ∀ j, Signs p16999 (bank16999 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17000 := params 7
abbrev ray17000 := rays 7
def bank17000 : Fin 1 → Cell := oneBank p17000 ray17000
theorem signs17000 : ∀ j, Signs p17000 (bank17000 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17001 := params 8
abbrev ray17001 := rays 8
def bank17001 : Fin 1 → Cell := oneBank p17001 ray17001
theorem signs17001 : ∀ j, Signs p17001 (bank17001 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17002 := params 9
abbrev ray17002 := rays 9
def bank17002 : Fin 1 → Cell := oneBank p17002 ray17002
theorem signs17002 : ∀ j, Signs p17002 (bank17002 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17003 := params 10
abbrev ray17003 := rays 10
def bank17003 : Fin 1 → Cell := oneBank p17003 ray17003
theorem signs17003 : ∀ j, Signs p17003 (bank17003 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17004 := params 11
abbrev ray17004 := rays 11
def bank17004 : Fin 1 → Cell := oneBank p17004 ray17004
theorem signs17004 : ∀ j, Signs p17004 (bank17004 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17005 := params 12
abbrev ray17005 := rays 12
def bank17005 : Fin 1 → Cell := oneBank p17005 ray17005
theorem signs17005 : ∀ j, Signs p17005 (bank17005 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17006 := params 13
abbrev ray17006 := rays 13
def bank17006 : Fin 1 → Cell := oneBank p17006 ray17006
theorem signs17006 : ∀ j, Signs p17006 (bank17006 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17007 := params 14
abbrev ray17007 := rays 14
def bank17007 : Fin 1 → Cell := oneBank p17007 ray17007
theorem signs17007 : ∀ j, Signs p17007 (bank17007 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17008 := params 15
abbrev ray17008 := rays 15
def bank17008 : Fin 1 → Cell := oneBank p17008 ray17008
theorem signs17008 : ∀ j, Signs p17008 (bank17008 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17009 := params 16
abbrev ray17009 := rays 16
def bank17009 : Fin 1 → Cell := oneBank p17009 ray17009
theorem signs17009 : ∀ j, Signs p17009 (bank17009 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17010 := params 17
abbrev ray17010 := rays 17
def bank17010 : Fin 1 → Cell := oneBank p17010 ray17010
theorem signs17010 : ∀ j, Signs p17010 (bank17010 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17011 := params 18
abbrev ray17011 := rays 18
def bank17011 : Fin 1 → Cell := oneBank p17011 ray17011
theorem signs17011 : ∀ j, Signs p17011 (bank17011 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17012 := params 19
abbrev ray17012 := rays 19
def bank17012 : Fin 1 → Cell := oneBank p17012 ray17012
theorem signs17012 : ∀ j, Signs p17012 (bank17012 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17013 := params 20
abbrev ray17013 := rays 20
def bank17013 : Fin 1 → Cell := oneBank p17013 ray17013
theorem signs17013 : ∀ j, Signs p17013 (bank17013 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17014 := params 21
abbrev ray17014 := rays 21
def bank17014 : Fin 1 → Cell := oneBank p17014 ray17014
theorem signs17014 : ∀ j, Signs p17014 (bank17014 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17015 := params 22
abbrev ray17015 := rays 22
def bank17015 : Fin 1 → Cell := oneBank p17015 ray17015
theorem signs17015 : ∀ j, Signs p17015 (bank17015 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17016 := params 23
abbrev ray17016 := rays 23
def bank17016 : Fin 1 → Cell := oneBank p17016 ray17016
theorem signs17016 : ∀ j, Signs p17016 (bank17016 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17017 := params 24
abbrev ray17017 := rays 24
def bank17017 : Fin 1 → Cell := oneBank p17017 ray17017
theorem signs17017 : ∀ j, Signs p17017 (bank17017 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17018 := params 25
abbrev ray17018 := rays 25
def bank17018 : Fin 1 → Cell := oneBank p17018 ray17018
theorem signs17018 : ∀ j, Signs p17018 (bank17018 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17019 := params 26
abbrev ray17019 := rays 26
def bank17019 : Fin 1 → Cell := oneBank p17019 ray17019
theorem signs17019 : ∀ j, Signs p17019 (bank17019 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17020 := params 27
abbrev ray17020 := rays 27
def bank17020 : Fin 1 → Cell := oneBank p17020 ray17020
theorem signs17020 : ∀ j, Signs p17020 (bank17020 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17021 := params 28
abbrev ray17021 := rays 28
def bank17021 : Fin 1 → Cell := oneBank p17021 ray17021
theorem signs17021 : ∀ j, Signs p17021 (bank17021 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17022 := params 29
abbrev ray17022 := rays 29
def bank17022 : Fin 1 → Cell := oneBank p17022 ray17022
theorem signs17022 : ∀ j, Signs p17022 (bank17022 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17023 := params 30
abbrev ray17023 := rays 30
def bank17023 : Fin 1 → Cell := oneBank p17023 ray17023
theorem signs17023 : ∀ j, Signs p17023 (bank17023 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p17024 := params 31
abbrev ray17024 := rays 31
def bank17024 : Fin 1 → Cell := oneBank p17024 ray17024
theorem signs17024 : ∀ j, Signs p17024 (bank17024 j) false := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages16993_17024
