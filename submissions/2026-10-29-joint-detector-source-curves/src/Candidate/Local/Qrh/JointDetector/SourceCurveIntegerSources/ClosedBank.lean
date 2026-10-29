/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.SourceCurveIntegerSources.Ray
import Candidate.Local.Qrh.JointDetector.SourceCurveLowBank.Ray
import Candidate.Local.Qrh.JointDetector.SourceCurveSuffix.Ray
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.Endpoint
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.BankSuppliers
namespace Qrh.JointDetector.SourceCurveIntegerSources
noncomputable section
set_option autoImplicit false
open OAI.SevenEighths QRH.Record1252270103Source

theorem supplier1 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (59784962862251179500000000000000000/60419647067436616762923904456503737:ℝ) (1000000000000000000/434708601583500581:ℝ) (1/10:ℝ) :=
 Ray.supplier1 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier2 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (17512526066994755450000000000000000/17802782098520571788969505940924293:ℝ) (100000000000000000/45462953437438059:ℝ) (1/10:ℝ) :=
 Ray.supplier2 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier3 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (1985500000000000000000/2020388105485661143599:ℝ) (1000000000000000000/457826445838581723:ℝ) (1/10:ℝ) :=
 Ray.supplier3 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier4 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (81140625000000000000/83047748376231418073:ℝ) (31250000000000000/14885776729921387:ℝ) (1/10:ℝ) :=
 Ray.supplier4 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier5 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (1523900000000000000000/1571642598618682687851:ℝ) (200000000000000000/99996347815657103:ℝ) (1/10:ℝ) :=
 Ray.supplier5 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier6 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (3727550000000000000000/3877524871986836653461:ℝ) (100000000000000000/52645851112471137:ℝ) (1/10:ℝ) :=
 Ray.supplier6 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier7 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (96062500000000000000/100375673245485993679:ℝ) (250000000000000000/135095118769160153:ℝ) (1/10:ℝ) :=
 Ray.supplier7 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier8 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (36500500000000000000000/38320953437144210239341:ℝ) (1000000000000000000/555351991031465447:ℝ) (1/10:ℝ) :=
 Ray.supplier8 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier9 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (9028250000000000000000/9526396028060234024007:ℝ) (500000000000000000/285743304480045413:ℝ) (1/10:ℝ) :=
 Ray.supplier9 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier10 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (286820000000000000000/303723238078631476323:ℝ) (40000000000000000/23322063893007101:ℝ) (1/10:ℝ) :=
 Ray.supplier10 hβ (SourceCurveLowBank.Ray.source hβ hprevious)

theorem supplier11 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (11804270958531/12500000000000:ℝ) (799976677936106992899/466441277860142020000:ℝ) (1001/10000:ℝ) :=
 SourceCurveSuffix.Ray.source11 hβ (supplier10 hβ hprevious)

theorem supplier12 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (94433677697847/100000000000000:ℝ) (399976677936106992899/233220638930071010000:ℝ) (501/5000:ℝ) :=
 SourceCurveSuffix.Ray.source12 hβ (supplier10 hβ hprevious)

theorem supplier13 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (94433187711453/100000000000000:ℝ) (799930033808320978697/466441277860142020000:ℝ) (1003/10000:ℝ) :=
 SourceCurveSuffix.Ray.source13 hβ (supplier10 hβ hprevious)

theorem supplier14 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (47216348854533/50000000000000:ℝ) (199976677936106992899/116610319465035505000:ℝ) (251/2500:ℝ) :=
 SourceCurveSuffix.Ray.source14 hβ (supplier10 hβ hprevious)

theorem supplier15 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (18886441538137/20000000000000:ℝ) (159976677936106992899/93288255572028404000:ℝ) (201/2000:ℝ) :=
 SourceCurveSuffix.Ray.source15 hβ (supplier10 hβ hprevious)

theorem supplier16 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (94431717656311/100000000000000:ℝ) (399930033808320978697/233220638930071010000:ℝ) (503/5000:ℝ) :=
 SourceCurveSuffix.Ray.source16 hβ (supplier10 hβ hprevious)

theorem supplier17 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (11803903450743/12500000000000:ℝ) (799836745552748950293/466441277860142020000:ℝ) (1007/10000:ℝ) :=
 SourceCurveSuffix.Ray.source17 hβ (supplier10 hβ hprevious)

theorem supplier18 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (94430737539583/100000000000000:ℝ) (99976677936106992899/58305159732517752500:ℝ) (63/625:ℝ) :=
 SourceCurveSuffix.Ray.source18 hβ (supplier10 hβ hprevious)

theorem supplier19 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (94430247457229/100000000000000:ℝ) (799790101424962936091/466441277860142020000:ℝ) (1009/10000:ℝ) :=
 SourceCurveSuffix.Ray.source19 hβ (supplier10 hβ hprevious)

theorem supplier20 (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 GlobalSource (94429757358881/100000000000000:ℝ) (79976677936106992899/46644127786014202000:ℝ) (101/1000:ℝ) :=
 SourceCurveSuffix.Ray.source20 hβ (supplier10 hβ hprevious)

theorem bankSuppliers_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) : RayCurveReturn.BankSuppliers := by
 intro b hb
 cases b with
 | old => exact (hb rfl).elim
 | Cnew =>
  change GlobalSource (94429757358881/100000000000000:ℝ) (79976677936106992899/46644127786014202000:ℝ) (101/1000:ℝ)
  exact supplier20 hβ hprevious
 | Pnew =>
  change GlobalSource (1985500000000000000000/2020388105485661143599:ℝ) (1000000000000000000/457826445838581723:ℝ) (1/10:ℝ)
  exact supplier3 hβ hprevious
 | Cphys =>
  change GlobalSource (1985500000000000000000/2020388105485661143599:ℝ) (1000000000000000000/457826445838581723:ℝ) (1/10:ℝ)
  exact supplier3 hβ hprevious
 | Cold =>
  change GlobalSource (17512526066994755450000000000000000/17802782098520571788969505940924293:ℝ) (100000000000000000/45462953437438059:ℝ) (1/10:ℝ)
  exact supplier2 hβ hprevious
 | Pold =>
  change GlobalSource (59784962862251179500000000000000000/60419647067436616762923904456503737:ℝ) (1000000000000000000/434708601583500581:ℝ) (1/10:ℝ)
  exact supplier1 hβ hprevious
 | Cphysold =>
  change GlobalSource (59784962862251179500000000000000000/60419647067436616762923904456503737:ℝ) (1000000000000000000/434708601583500581:ℝ) (1/10:ℝ)
  exact supplier1 hβ hprevious
 | Pwide =>
  change GlobalSource (1985500000000000000000/2020388105485661143599:ℝ) (1000000000000000000/457826445838581723:ℝ) (1/10:ℝ)
  exact supplier3 hβ hprevious
 | Pcount =>
  change GlobalSource (94429757358881/100000000000000:ℝ) (79976677936106992899/46644127786014202000:ℝ) (101/1000:ℝ)
  exact supplier20 hβ hprevious
 | Pcountmid =>
  change GlobalSource (94429757358881/100000000000000:ℝ) (79976677936106992899/46644127786014202000:ℝ) (101/1000:ℝ)
  exact supplier20 hβ hprevious
 | Cbridge0 =>
  change GlobalSource (17512526066994755450000000000000000/17802782098520571788969505940924293:ℝ) (100000000000000000/45462953437438059:ℝ) (1/10:ℝ)
  exact supplier2 hβ hprevious
 | Cbridge1 =>
  change GlobalSource (81140625000000000000/83047748376231418073:ℝ) (31250000000000000/14885776729921387:ℝ) (1/10:ℝ)
  exact supplier4 hβ hprevious
 | Cbridge2 =>
  change GlobalSource (1523900000000000000000/1571642598618682687851:ℝ) (200000000000000000/99996347815657103:ℝ) (1/10:ℝ)
  exact supplier5 hβ hprevious
 | Cbridge3 =>
  change GlobalSource (3727550000000000000000/3877524871986836653461:ℝ) (100000000000000000/52645851112471137:ℝ) (1/10:ℝ)
  exact supplier6 hβ hprevious
 | Cbridge4 =>
  change GlobalSource (36500500000000000000000/38320953437144210239341:ℝ) (1000000000000000000/555351991031465447:ℝ) (1/10:ℝ)
  exact supplier8 hβ hprevious
 | Cbridge5 =>
  change GlobalSource (96062500000000000000/100375673245485993679:ℝ) (250000000000000000/135095118769160153:ℝ) (1/10:ℝ)
  exact supplier7 hβ hprevious
 | Cbridge6 =>
  change GlobalSource (9028250000000000000000/9526396028060234024007:ℝ) (500000000000000000/285743304480045413:ℝ) (1/10:ℝ)
  exact supplier9 hβ hprevious

theorem physicalSource_of_previous (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
 (hprevious : HeckeZeroSupremum.beta ≤ (8738357291/10000000000:ℝ)) :
 QRH.Record12518109Existence.UniformUnitFaceSource RayCurveReturn.physicalSourceFace := by
 simpa only [RayCurveReturn.physicalSourceFace,RayCurveReturn.physicalB,RayCurveReturn.physicalLambda] using supplier3 hβ hprevious
end
end Qrh.JointDetector.SourceCurveIntegerSources
