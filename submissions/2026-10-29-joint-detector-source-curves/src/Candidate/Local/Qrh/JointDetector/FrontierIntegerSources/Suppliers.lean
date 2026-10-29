/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.FrontierIntegerSources.All
import Candidate.Local.Qrh.JointDetector.SourceCurveLowBank.Feedback
import Candidate.Local.Qrh.JointDetector.SourceCurveSuffix.Frontier
namespace Qrh.JointDetector.FrontierIntegerSources
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths QRH.Record1252270103Source

theorem supplier1_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (2938098301089380810259500000000000000000/2969390772433447882178711534888561663577:ℝ) (1000000000000000000/434829244260283861:ℝ) (1/10:ℝ) :=
 supplier1 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier2_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (119570835508974091584812500000000000000/121547480233128876816640189114959396379:ℝ) (125000000000000000/56811366882099949:ℝ) (1/10:ℝ) :=
 supplier2 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier3_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (26473100000000000000000/26938336372378280509427:ℝ) (200000000000000000/91566884230346339:ℝ) (1/10:ℝ) :=
 supplier3 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier4_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (24345875000000000000000/24916887732680114263857:ℝ) (250000000000000000/119048106471923757:ℝ) (1/10:ℝ) :=
 supplier4 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier5_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (126990500000000000000000/130969454299025819256483:ℝ) (1000000000000000000/499992190281953781:ℝ) (1/10:ℝ) :=
 supplier5 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier6_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (12427250000000000000000/12926344945048992710019:ℝ) (500000000000000000/263120991411016197:ℝ) (1/10:ℝ) :=
 supplier6 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier7_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (73763500000000000000000/77081188030401828860133:ℝ) (1000000000000000000/540613321763782193:ℝ) (1/10:ℝ) :=
 supplier7 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier8_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (4865900000000000000000/5108988652583522185927:ℝ) (200000000000000000/111120530973824351:ℝ) (1/10:ℝ) :=
 supplier8 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier9_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (1805650000000000000000/1905279150937348632609:ℝ) (100000000000000000/57148659256046931:ℝ) (1/10:ℝ) :=
 supplier9 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier10_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (8962072953125000000000000/9490792564634773789948053:ℝ) (31250000000000000/18226357523746579:ℝ) (1/10:ℝ) :=
 supplier10 hβ (SourceCurveLowBank.Feedback.source hβ hprevious)

theorem supplier11_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (9442913011809/10000000000000:ℝ) (312499981773642476253421/182263575237465790000000:ℝ) (1001/10000:ℝ) :=
 SourceCurveSuffix.Frontier.source11 hβ (supplier10_of_previous hβ hprevious)

theorem supplier12_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (47214564568949/50000000000000:ℝ) (156249981773642476253421/91131787618732895000000:ℝ) (501/5000:ℝ) :=
 SourceCurveSuffix.Frontier.source12 hβ (supplier10_of_previous hβ hprevious)

theorem supplier13_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (47214564078853/50000000000000:ℝ) (312499945320927428760263/182263575237465790000000:ℝ) (1003/10000:ℝ) :=
 SourceCurveSuffix.Frontier.source13 hβ (supplier10_of_previous hβ hprevious)

theorem supplier14_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (47214563588757/50000000000000:ℝ) (78124981773642476253421/45565893809366447500000:ℝ) (251/2500:ℝ) :=
 SourceCurveSuffix.Frontier.source14 hβ (supplier10_of_previous hβ hprevious)

theorem supplier15_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (47214563098661/50000000000000:ℝ) (62499981773642476253421/36452715047493158000000:ℝ) (201/2000:ℝ) :=
 SourceCurveSuffix.Frontier.source15 hβ (supplier10_of_previous hβ hprevious)

theorem supplier16_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (94429125217129/100000000000000:ℝ) (156249945320927428760263/91131787618732895000000:ℝ) (503/5000:ℝ) :=
 SourceCurveSuffix.Frontier.source16 hβ (supplier10_of_previous hβ hprevious)

theorem supplier17_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (11803640529617/12500000000000:ℝ) (312499872415497333773947/182263575237465790000000:ℝ) (1007/10000:ℝ) :=
 SourceCurveSuffix.Frontier.source17 hβ (supplier10_of_previous hβ hprevious)

theorem supplier18_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (94429123256743/100000000000000:ℝ) (39062481773642476253421/22782946904683223750000:ℝ) (63/625:ℝ) :=
 SourceCurveSuffix.Frontier.source18 hβ (supplier10_of_previous hβ hprevious)

theorem supplier19_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (1888582445531/2000000000000:ℝ) (312499835962782286280789/182263575237465790000000:ℝ) (1009/10000:ℝ) :=
 SourceCurveSuffix.Frontier.source19 hβ (supplier10_of_previous hβ hprevious)

theorem supplier20_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357037/10000000000:ℝ)) :
 GlobalSource (94429121296357/100000000000000:ℝ) (31249981773642476253421/18226357523746579000000:ℝ) (101/1000:ℝ) :=
 SourceCurveSuffix.Frontier.source20 hβ (supplier10_of_previous hβ hprevious)
end
end Qrh.JointDetector.FrontierIntegerSources
