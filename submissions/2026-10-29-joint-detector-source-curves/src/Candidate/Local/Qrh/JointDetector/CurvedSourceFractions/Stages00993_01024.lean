/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages00993_01024
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99859523853705,99859369205927,99859214532756,99859059834194,99858905110243,99858750360905,99858595586183,99858440786079,99858285960596,99858131109736,99857976233502,99857821331895,99857666404919,99857511452576,99857356474869,99857201471799,99857046443369,99856891389582,99856736310440,99856581205946,99856426076102,99856270920910,99856115740373,99855960534492,99855805303271,99855650046713,99855494764819,99855339457592,99855184125034,99855028767147,99854873383935,99854717975399,99854562541542]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (992+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(4487921491827928376069/5873608028800725298659:Fraction),(9616131678080476630376/12586052918858947068555:Fraction),(4487134728625921422238/5873374695467625298659:Fraction),(121263281336951452876/158736703481110143207:Fraction),(67295222384474917542788/88097120432017879479885:Fraction),(13457864688142644902987/17619074086403925895977:Fraction),(22427808103578419248738/29364540144007126493295:Fraction),(4485168414047379061820/5872791362134875298659:Fraction),(9610232734384933301614/12584302918860697068555:Fraction),(22421910628184536394012/29362790144008876493295:Fraction),(13451967131700296455664/17617324086405675895977:Fraction),(13450787849275059875506/17616974086406025895977:Fraction),(22416014216062830125494/29361040144010626493295:Fraction),(67242147080196196585958/88081370432033629479885:Fraction),(67236252542453420400671/88079620432035379479885:Fraction),(166000883503062499623/217476223288980566617:Fraction),(2489794967605774194554/3262078534519958499255:Fraction),(22406190082018056693976/29358123477346876493295:Fraction),(497871675413675620304/652389780978091699851:Fraction),(67206783146073774667024/88070870432044129479885:Fraction),(7466765682421187599424/9785457825782875497765:Fraction),(213317456989500895888/279578953752532157079:Fraction),(67189107792164530102436/88065620432049379479885:Fraction),(67183216446872115633964/88063870432051129479885:Fraction),(22392441638609647846264/29354040144017626493295:Fraction),(1066213244689876235783/1397783657651660785395:Fraction),(51865285672451377337/67998934696568632803:Fraction),(1066026274452816948458/1397728102096160785395:Fraction),(13430753333207948779808/17611024086411975895977:Fraction),(6104352532358477457091/8004851857460148134535:Fraction),(4476132671782501333313/5870108028804225298659:Fraction),(7459566901330533123481/9783318936896125497765:Fraction)]
abbrev p993 := params 0
abbrev ray993 := rays 0
def bank993 : Fin 1 → Cell := oneBank p993 ray993
theorem signs993 : ∀ j, Signs p993 (bank993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p994 := params 1
abbrev ray994 := rays 1
def bank994 : Fin 1 → Cell := oneBank p994 ray994
theorem signs994 : ∀ j, Signs p994 (bank994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p995 := params 2
abbrev ray995 := rays 2
def bank995 : Fin 1 → Cell := oneBank p995 ray995
theorem signs995 : ∀ j, Signs p995 (bank995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p996 := params 3
abbrev ray996 := rays 3
def bank996 : Fin 1 → Cell := oneBank p996 ray996
theorem signs996 : ∀ j, Signs p996 (bank996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p997 := params 4
abbrev ray997 := rays 4
def bank997 : Fin 1 → Cell := oneBank p997 ray997
theorem signs997 : ∀ j, Signs p997 (bank997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p998 := params 5
abbrev ray998 := rays 5
def bank998 : Fin 1 → Cell := oneBank p998 ray998
theorem signs998 : ∀ j, Signs p998 (bank998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p999 := params 6
abbrev ray999 := rays 6
def bank999 : Fin 1 → Cell := oneBank p999 ray999
theorem signs999 : ∀ j, Signs p999 (bank999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1000 := params 7
abbrev ray1000 := rays 7
def bank1000 : Fin 1 → Cell := oneBank p1000 ray1000
theorem signs1000 : ∀ j, Signs p1000 (bank1000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1001 := params 8
abbrev ray1001 := rays 8
def bank1001 : Fin 1 → Cell := oneBank p1001 ray1001
theorem signs1001 : ∀ j, Signs p1001 (bank1001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1002 := params 9
abbrev ray1002 := rays 9
def bank1002 : Fin 1 → Cell := oneBank p1002 ray1002
theorem signs1002 : ∀ j, Signs p1002 (bank1002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1003 := params 10
abbrev ray1003 := rays 10
def bank1003 : Fin 1 → Cell := oneBank p1003 ray1003
theorem signs1003 : ∀ j, Signs p1003 (bank1003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1004 := params 11
abbrev ray1004 := rays 11
def bank1004 : Fin 1 → Cell := oneBank p1004 ray1004
theorem signs1004 : ∀ j, Signs p1004 (bank1004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1005 := params 12
abbrev ray1005 := rays 12
def bank1005 : Fin 1 → Cell := oneBank p1005 ray1005
theorem signs1005 : ∀ j, Signs p1005 (bank1005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1006 := params 13
abbrev ray1006 := rays 13
def bank1006 : Fin 1 → Cell := oneBank p1006 ray1006
theorem signs1006 : ∀ j, Signs p1006 (bank1006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1007 := params 14
abbrev ray1007 := rays 14
def bank1007 : Fin 1 → Cell := oneBank p1007 ray1007
theorem signs1007 : ∀ j, Signs p1007 (bank1007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1008 := params 15
abbrev ray1008 := rays 15
def bank1008 : Fin 1 → Cell := oneBank p1008 ray1008
theorem signs1008 : ∀ j, Signs p1008 (bank1008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1009 := params 16
abbrev ray1009 := rays 16
def bank1009 : Fin 1 → Cell := oneBank p1009 ray1009
theorem signs1009 : ∀ j, Signs p1009 (bank1009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1010 := params 17
abbrev ray1010 := rays 17
def bank1010 : Fin 1 → Cell := oneBank p1010 ray1010
theorem signs1010 : ∀ j, Signs p1010 (bank1010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1011 := params 18
abbrev ray1011 := rays 18
def bank1011 : Fin 1 → Cell := oneBank p1011 ray1011
theorem signs1011 : ∀ j, Signs p1011 (bank1011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1012 := params 19
abbrev ray1012 := rays 19
def bank1012 : Fin 1 → Cell := oneBank p1012 ray1012
theorem signs1012 : ∀ j, Signs p1012 (bank1012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1013 := params 20
abbrev ray1013 := rays 20
def bank1013 : Fin 1 → Cell := oneBank p1013 ray1013
theorem signs1013 : ∀ j, Signs p1013 (bank1013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1014 := params 21
abbrev ray1014 := rays 21
def bank1014 : Fin 1 → Cell := oneBank p1014 ray1014
theorem signs1014 : ∀ j, Signs p1014 (bank1014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1015 := params 22
abbrev ray1015 := rays 22
def bank1015 : Fin 1 → Cell := oneBank p1015 ray1015
theorem signs1015 : ∀ j, Signs p1015 (bank1015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1016 := params 23
abbrev ray1016 := rays 23
def bank1016 : Fin 1 → Cell := oneBank p1016 ray1016
theorem signs1016 : ∀ j, Signs p1016 (bank1016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1017 := params 24
abbrev ray1017 := rays 24
def bank1017 : Fin 1 → Cell := oneBank p1017 ray1017
theorem signs1017 : ∀ j, Signs p1017 (bank1017 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1018 := params 25
abbrev ray1018 := rays 25
def bank1018 : Fin 1 → Cell := oneBank p1018 ray1018
theorem signs1018 : ∀ j, Signs p1018 (bank1018 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1019 := params 26
abbrev ray1019 := rays 26
def bank1019 : Fin 1 → Cell := oneBank p1019 ray1019
theorem signs1019 : ∀ j, Signs p1019 (bank1019 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1020 := params 27
abbrev ray1020 := rays 27
def bank1020 : Fin 1 → Cell := oneBank p1020 ray1020
theorem signs1020 : ∀ j, Signs p1020 (bank1020 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1021 := params 28
abbrev ray1021 := rays 28
def bank1021 : Fin 1 → Cell := oneBank p1021 ray1021
theorem signs1021 : ∀ j, Signs p1021 (bank1021 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1022 := params 29
abbrev ray1022 := rays 29
def bank1022 : Fin 1 → Cell := oneBank p1022 ray1022
theorem signs1022 : ∀ j, Signs p1022 (bank1022 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1023 := params 30
abbrev ray1023 := rays 30
def bank1023 : Fin 1 → Cell := oneBank p1023 ray1023
theorem signs1023 : ∀ j, Signs p1023 (bank1023 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1024 := params 31
abbrev ray1024 := rays 31
def bank1024 : Fin 1 → Cell := oneBank p1024 ray1024
theorem signs1024 : ∀ j, Signs p1024 (bank1024 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages00993_01024
