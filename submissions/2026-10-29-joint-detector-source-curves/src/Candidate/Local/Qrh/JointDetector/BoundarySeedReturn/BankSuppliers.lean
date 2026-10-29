/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.BoundarySeedReturn.SourceInlet
import Candidate.Local.Qrh.JointDetector.RestartSourceDomain
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.BoundarySeedReturn
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
 | .Cnew => globalFace (94429121296357/100000000000000:ℝ) (31249981773642476253421/18226357523746579000000:ℝ) (101/1000:ℝ)
 | .Pnew => globalFace (26473100000000000000000/26938336372378280509427:ℝ) (200000000000000000/91566884230346339:ℝ) (1/10:ℝ)
 | .Cphys => globalFace (26473100000000000000000/26938336372378280509427:ℝ) (200000000000000000/91566884230346339:ℝ) (1/10:ℝ)
 | .Cold => globalFace (119570835508974091584812500000000000000/121547480233128876816640189114959396379:ℝ) (125000000000000000/56811366882099949:ℝ) (1/10:ℝ)
 | .Pold => globalFace (2938098301089380810259500000000000000000/2969390772433447882178711534888561663577:ℝ) (1000000000000000000/434829244260283861:ℝ) (1/10:ℝ)
 | .Cphysold => globalFace (2938098301089380810259500000000000000000/2969390772433447882178711534888561663577:ℝ) (1000000000000000000/434829244260283861:ℝ) (1/10:ℝ)
 | .Pwide => globalFace (26473100000000000000000/26938336372378280509427:ℝ) (200000000000000000/91566884230346339:ℝ) (1/10:ℝ)
 | .Pcount => globalFace (94429121296357/100000000000000:ℝ) (31249981773642476253421/18226357523746579000000:ℝ) (101/1000:ℝ)
 | .Pcountmid => globalFace (94429121296357/100000000000000:ℝ) (31249981773642476253421/18226357523746579000000:ℝ) (101/1000:ℝ)
 | .Cbridge0 => globalFace (119570835508974091584812500000000000000/121547480233128876816640189114959396379:ℝ) (125000000000000000/56811366882099949:ℝ) (1/10:ℝ)
 | .Cbridge1 => globalFace (24345875000000000000000/24916887732680114263857:ℝ) (250000000000000000/119048106471923757:ℝ) (1/10:ℝ)
 | .Cbridge2 => globalFace (126990500000000000000000/130969454299025819256483:ℝ) (1000000000000000000/499992190281953781:ℝ) (1/10:ℝ)
 | .Cbridge3 => globalFace (12427250000000000000000/12926344945048992710019:ℝ) (500000000000000000/263120991411016197:ℝ) (1/10:ℝ)
 | .Cbridge4 => globalFace (4865900000000000000000/5108988652583522185927:ℝ) (200000000000000000/111120530973824351:ℝ) (1/10:ℝ)
 | .Cbridge5 => globalFace (73763500000000000000000/77081188030401828860133:ℝ) (1000000000000000000/540613321763782193:ℝ) (1/10:ℝ)
 | .Cbridge6 => globalFace (1805650000000000000000/1905279150937348632609:ℝ) (100000000000000000/57148659256046931:ℝ) (1/10:ℝ)


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
end Qrh.JointDetector.BoundarySeedReturn
