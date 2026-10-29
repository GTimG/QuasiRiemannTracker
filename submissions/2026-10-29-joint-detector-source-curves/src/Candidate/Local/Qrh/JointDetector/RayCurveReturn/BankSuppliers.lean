/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.RayCurveReturn.SourceInlet
import Candidate.Local.Qrh.JointDetector.RestartSourceDomain
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.RayCurveReturn
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

/-- Exact supplier-bank indices used by each ordinary/capped count face. These indices do not assert source transitions. -/
def supplierStage : CountBranch → ℕ
 | .old => 0
 | .Cnew => 20
 | .Pnew => 3
 | .Cphys => 3
 | .Cold => 2
 | .Pold => 1
 | .Cphysold => 1
 | .Pwide => 3
 | .Pcount => 20
 | .Pcountmid => 20
 | .Cbridge0 => 2
 | .Cbridge1 => 4
 | .Cbridge2 => 5
 | .Cbridge3 => 6
 | .Cbridge4 => 8
 | .Cbridge5 => 7
 | .Cbridge6 => 9
def bankSupplier : CountBranch → SourceFace
 | .old => countingSource .old
 | .Cnew => globalFace (94429757358881/100000000000000:ℝ) (79976677936106992899/46644127786014202000:ℝ) (101/1000:ℝ)
 | .Pnew => globalFace (1985500000000000000000/2020388105485661143599:ℝ) (1000000000000000000/457826445838581723:ℝ) (1/10:ℝ)
 | .Cphys => globalFace (1985500000000000000000/2020388105485661143599:ℝ) (1000000000000000000/457826445838581723:ℝ) (1/10:ℝ)
 | .Cold => globalFace (17512526066994755450000000000000000/17802782098520571788969505940924293:ℝ) (100000000000000000/45462953437438059:ℝ) (1/10:ℝ)
 | .Pold => globalFace (59784962862251179500000000000000000/60419647067436616762923904456503737:ℝ) (1000000000000000000/434708601583500581:ℝ) (1/10:ℝ)
 | .Cphysold => globalFace (59784962862251179500000000000000000/60419647067436616762923904456503737:ℝ) (1000000000000000000/434708601583500581:ℝ) (1/10:ℝ)
 | .Pwide => globalFace (1985500000000000000000/2020388105485661143599:ℝ) (1000000000000000000/457826445838581723:ℝ) (1/10:ℝ)
 | .Pcount => globalFace (94429757358881/100000000000000:ℝ) (79976677936106992899/46644127786014202000:ℝ) (101/1000:ℝ)
 | .Pcountmid => globalFace (94429757358881/100000000000000:ℝ) (79976677936106992899/46644127786014202000:ℝ) (101/1000:ℝ)
 | .Cbridge0 => globalFace (17512526066994755450000000000000000/17802782098520571788969505940924293:ℝ) (100000000000000000/45462953437438059:ℝ) (1/10:ℝ)
 | .Cbridge1 => globalFace (81140625000000000000/83047748376231418073:ℝ) (31250000000000000/14885776729921387:ℝ) (1/10:ℝ)
 | .Cbridge2 => globalFace (1523900000000000000000/1571642598618682687851:ℝ) (200000000000000000/99996347815657103:ℝ) (1/10:ℝ)
 | .Cbridge3 => globalFace (3727550000000000000000/3877524871986836653461:ℝ) (100000000000000000/52645851112471137:ℝ) (1/10:ℝ)
 | .Cbridge4 => globalFace (36500500000000000000000/38320953437144210239341:ℝ) (1000000000000000000/555351991031465447:ℝ) (1/10:ℝ)
 | .Cbridge5 => globalFace (96062500000000000000/100375673245485993679:ℝ) (250000000000000000/135095118769160153:ℝ) (1/10:ℝ)
 | .Cbridge6 => globalFace (9028250000000000000000/9526396028060234024007:ℝ) (500000000000000000/285743304480045413:ℝ) (1/10:ℝ)


theorem bankSupplier_restricts (b : CountBranch) (hb : b ≠ .old) :
 RestartSourceDomain.Contains (bankSupplier b) (countingSource b) := by
 cases b <;> first | exact (hb rfl).elim | (apply RestartSourceDomain.contains_of_affine <;>
   norm_num [bankSupplier, countingSource, broadFace, globalFace,
     QRH.Record1252270103Return.globalFace, branchB, branchL, branchCap])

/-- Closed by the finite source chain, rather than an unproved face comparison. -/
def BankSuppliers : Prop := ∀ b : CountBranch, b ≠ .old →
 UniformUnitFaceSource (bankSupplier b)

theorem sourceBank_of_suppliers (hs : BankSuppliers) : SourceBank := by
 intro b hb ε hε
 obtain ⟨mesh, hm, hs⟩ := hs b hb ε hε
 exact ⟨mesh, hm, RestartSourceDomain.unit_source_of_contains (bankSupplier_restricts b hb) hs⟩

end
end Qrh.JointDetector.RayCurveReturn
