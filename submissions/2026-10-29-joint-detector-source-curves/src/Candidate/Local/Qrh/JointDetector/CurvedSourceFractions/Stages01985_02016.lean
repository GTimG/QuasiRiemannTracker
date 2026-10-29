/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common
namespace Qrh.JointDetector.CurvedSourceFractions.Stages01985_02016
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def bValues : Fin 33 → ℕ := ![99694000927492,99693822184997,99693643419226,99693464630181,99693285817863,99693106982274,99692928123415,99692749241289,99692570335899,99692391407245,99692212455330,99692033480155,99691854481722,99691675460033,99691496415090,99691317346895,99691138255450,99690959140756,99690780002815,99690600841629,99690421657200,99690242449530,99690063218621,99689883964475,99689704687093,99689525386477,99689346062630,99689166715552,99688987345246,99688807951714,99688628534957,99688449091123,99688269619591]
def b (i : Fin 33) : Fraction := Fraction.ofInt (bValues i)/100000000000000
def params (i : Fin 32) : Params := point (1984+i.val) (b i.castSucc) (b i.succ)
def rays : Fin 32 → Fraction := ![(12335342472938684514400/17273624086749375895977:Fraction),(2284119939989762831309/3198754460509208499255:Fraction),(20555255154150438133828/28788206811250126493295:Fraction),(12332058722585453260294/17272574086750425895977:Fraction),(761170637051892452013/1066186672021652833085:Fraction),(1666198666413523568476/2334037038750152148105:Fraction),(111070053245482628935/155599316096860143207:Fraction),(20546136094347082818701/28785290144586376493295:Fraction),(1760941088078823130942/2467260583821739413711:Fraction),(333121447137176191721/466769569912230429621:Fraction),(456459247599913755076/639634225435291699851:Fraction),(12323306039928141585952/17269774086753225895977:Fraction),(61611061811277571935884/86347120433767879479885:Fraction),(6845065917878709549754/9593930048196625497765:Fraction),(4106675051911853708968/5756241362251425298659:Fraction),(4106310542299168395242/5756124695584875298659:Fraction),(10088319665603550860/14142525869578194837:Fraction),(61583724820617421756688/86338370433776629479885:Fraction),(12315651830202072446398/17267324086755675895977:Fraction),(6841421479948358792684/9592763381531125497765:Fraction),(4104488570427939939610/5755541362252125298659:Fraction),(456013804677638681336/639491632842841699851:Fraction),(20518799924992048022954/28776540144595126493295:Fraction),(332707760847003445090/466637137479930429621:Fraction),(61545472806920665225049/86326120433788879479885:Fraction),(2279259618348723114164/3197198904955208499255:Fraction),(4102303176832716284992/5754841362252825298659:Fraction),(1079457639436509603728/1514401235680598762805:Fraction),(6835958256880491972584/9591013381532875497765:Fraction),(61518163014330235650536/86317370433797629479885:Fraction),clippedRay (params 30),clippedRay (params 31)]
abbrev p1985 := params 0
abbrev ray1985 := rays 0
def bank1985 : Fin 1 → Cell := oneBank p1985 ray1985
theorem signs1985 : ∀ j, Signs p1985 (bank1985 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1986 := params 1
abbrev ray1986 := rays 1
def bank1986 : Fin 1 → Cell := oneBank p1986 ray1986
theorem signs1986 : ∀ j, Signs p1986 (bank1986 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1987 := params 2
abbrev ray1987 := rays 2
def bank1987 : Fin 1 → Cell := oneBank p1987 ray1987
theorem signs1987 : ∀ j, Signs p1987 (bank1987 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1988 := params 3
abbrev ray1988 := rays 3
def bank1988 : Fin 1 → Cell := oneBank p1988 ray1988
theorem signs1988 : ∀ j, Signs p1988 (bank1988 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1989 := params 4
abbrev ray1989 := rays 4
def bank1989 : Fin 1 → Cell := oneBank p1989 ray1989
theorem signs1989 : ∀ j, Signs p1989 (bank1989 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1990 := params 5
abbrev ray1990 := rays 5
def bank1990 : Fin 1 → Cell := oneBank p1990 ray1990
theorem signs1990 : ∀ j, Signs p1990 (bank1990 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1991 := params 6
abbrev ray1991 := rays 6
def bank1991 : Fin 1 → Cell := oneBank p1991 ray1991
theorem signs1991 : ∀ j, Signs p1991 (bank1991 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1992 := params 7
abbrev ray1992 := rays 7
def bank1992 : Fin 1 → Cell := oneBank p1992 ray1992
theorem signs1992 : ∀ j, Signs p1992 (bank1992 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1993 := params 8
abbrev ray1993 := rays 8
def bank1993 : Fin 1 → Cell := oneBank p1993 ray1993
theorem signs1993 : ∀ j, Signs p1993 (bank1993 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1994 := params 9
abbrev ray1994 := rays 9
def bank1994 : Fin 1 → Cell := oneBank p1994 ray1994
theorem signs1994 : ∀ j, Signs p1994 (bank1994 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1995 := params 10
abbrev ray1995 := rays 10
def bank1995 : Fin 1 → Cell := oneBank p1995 ray1995
theorem signs1995 : ∀ j, Signs p1995 (bank1995 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1996 := params 11
abbrev ray1996 := rays 11
def bank1996 : Fin 1 → Cell := oneBank p1996 ray1996
theorem signs1996 : ∀ j, Signs p1996 (bank1996 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1997 := params 12
abbrev ray1997 := rays 12
def bank1997 : Fin 1 → Cell := oneBank p1997 ray1997
theorem signs1997 : ∀ j, Signs p1997 (bank1997 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1998 := params 13
abbrev ray1998 := rays 13
def bank1998 : Fin 1 → Cell := oneBank p1998 ray1998
theorem signs1998 : ∀ j, Signs p1998 (bank1998 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p1999 := params 14
abbrev ray1999 := rays 14
def bank1999 : Fin 1 → Cell := oneBank p1999 ray1999
theorem signs1999 : ∀ j, Signs p1999 (bank1999 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2000 := params 15
abbrev ray2000 := rays 15
def bank2000 : Fin 1 → Cell := oneBank p2000 ray2000
theorem signs2000 : ∀ j, Signs p2000 (bank2000 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2001 := params 16
abbrev ray2001 := rays 16
def bank2001 : Fin 1 → Cell := oneBank p2001 ray2001
theorem signs2001 : ∀ j, Signs p2001 (bank2001 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2002 := params 17
abbrev ray2002 := rays 17
def bank2002 : Fin 1 → Cell := oneBank p2002 ray2002
theorem signs2002 : ∀ j, Signs p2002 (bank2002 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2003 := params 18
abbrev ray2003 := rays 18
def bank2003 : Fin 1 → Cell := oneBank p2003 ray2003
theorem signs2003 : ∀ j, Signs p2003 (bank2003 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2004 := params 19
abbrev ray2004 := rays 19
def bank2004 : Fin 1 → Cell := oneBank p2004 ray2004
theorem signs2004 : ∀ j, Signs p2004 (bank2004 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2005 := params 20
abbrev ray2005 := rays 20
def bank2005 : Fin 1 → Cell := oneBank p2005 ray2005
theorem signs2005 : ∀ j, Signs p2005 (bank2005 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2006 := params 21
abbrev ray2006 := rays 21
def bank2006 : Fin 1 → Cell := oneBank p2006 ray2006
theorem signs2006 : ∀ j, Signs p2006 (bank2006 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2007 := params 22
abbrev ray2007 := rays 22
def bank2007 : Fin 1 → Cell := oneBank p2007 ray2007
theorem signs2007 : ∀ j, Signs p2007 (bank2007 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2008 := params 23
abbrev ray2008 := rays 23
def bank2008 : Fin 1 → Cell := oneBank p2008 ray2008
theorem signs2008 : ∀ j, Signs p2008 (bank2008 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2009 := params 24
abbrev ray2009 := rays 24
def bank2009 : Fin 1 → Cell := oneBank p2009 ray2009
theorem signs2009 : ∀ j, Signs p2009 (bank2009 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2010 := params 25
abbrev ray2010 := rays 25
def bank2010 : Fin 1 → Cell := oneBank p2010 ray2010
theorem signs2010 : ∀ j, Signs p2010 (bank2010 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2011 := params 26
abbrev ray2011 := rays 26
def bank2011 : Fin 1 → Cell := oneBank p2011 ray2011
theorem signs2011 : ∀ j, Signs p2011 (bank2011 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2012 := params 27
abbrev ray2012 := rays 27
def bank2012 : Fin 1 → Cell := oneBank p2012 ray2012
theorem signs2012 : ∀ j, Signs p2012 (bank2012 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2013 := params 28
abbrev ray2013 := rays 28
def bank2013 : Fin 1 → Cell := oneBank p2013 ray2013
theorem signs2013 : ∀ j, Signs p2013 (bank2013 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2014 := params 29
abbrev ray2014 := rays 29
def bank2014 : Fin 3 → Cell := threeBank p2014 ray2014
theorem signs2014 : ∀ j, Signs p2014 (bank2014 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2015 := params 30
abbrev ray2015 := rays 30
def bank2015 : Fin 2 → Cell := twoBank p2015 ray2015
theorem signs2015 : ∀ j, Signs p2015 (bank2015 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
abbrev p2016 := params 31
abbrev ray2016 := rays 31
def bank2016 : Fin 2 → Cell := twoBank p2016 ray2016
theorem signs2016 : ∀ j, Signs p2016 (bank2016 j) true := by
  intro j
  fin_cases j <;> unfold Signs <;> decide +kernel
end Qrh.JointDetector.CurvedSourceFractions.Stages01985_02016
