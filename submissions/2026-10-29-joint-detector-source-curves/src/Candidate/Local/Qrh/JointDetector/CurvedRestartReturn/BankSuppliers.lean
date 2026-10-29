/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/restart_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
A finite count-source bank and physical source remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.CurvedRestartReturn.SourceInlet
import Candidate.Local.Qrh.JointDetector.RestartSourceDomain
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.CurvedRestartReturn
open QRH.Record1252270103Return
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

/-- Exact finite stages used by each ordinary/capped count face. -/
def supplierStage : CountBranch → ℕ
 | .old => 0
 | .Cnew => 17046
 | .Pnew => 7653
 | .Cphys => 7653
 | .Cold => 6047
 | .Pold => 4087
 | .Cphysold => 4087
 | .Pwide => 7653
 | .Pcount => 17046
 | .Pcountmid => 17046
 | .Cbridge0 => 7337
 | .Cbridge1 => 9337
 | .Cbridge2 => 11337
 | .Cbridge3 => 13337
 | .Cbridge4 => 15337
 | .Cbridge5 => 14337
 | .Cbridge6 => 16337
def bankSupplier : CountBranch → SourceFace
 | .old => countingSource .old
 | .Cnew => globalFace (47214537432223/50000000000000:ℝ) (1714560586289/1000000000000:ℝ) (101/1000:ℝ)
 | .Pnew => globalFace (49136463480553/50000000000000:ℝ) (2184210586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cphys => globalFace (49136463480553/50000000000000:ℝ) (2184210586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cold => globalFace (49376847065383/50000000000000:ℝ) (2264510586289/1000000000000:ℝ) (1/10:ℝ)
 | .Pold => globalFace (49629582396207/50000000000000:ℝ) (2362510586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cphysold => globalFace (49629582396207/50000000000000:ℝ) (2362510586289/1000000000000:ℝ) (1/10:ℝ)
 | .Pwide => globalFace (49136463480553/50000000000000:ℝ) (2184210586289/1000000000000:ℝ) (1/10:ℝ)
 | .Pcount => globalFace (47214537432223/50000000000000:ℝ) (1714560586289/1000000000000:ℝ) (101/1000:ℝ)
 | .Pcountmid => globalFace (47214537432223/50000000000000:ℝ) (1714560586289/1000000000000:ℝ) (101/1000:ℝ)
 | .Cbridge0 => globalFace (6148254622871/6250000000000:ℝ) (2200010586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cbridge1 => globalFace (9770832513817/10000000000000:ℝ) (2100010586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cbridge2 => globalFace (96961605236449/100000000000000:ℝ) (2000010586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cbridge3 => globalFace (96136568108477/100000000000000:ℝ) (1900010586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cbridge4 => globalFace (47621644908577/50000000000000:ℝ) (1800010586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cbridge5 => globalFace (23924502480543/25000000000000:ℝ) (1850010586289/1000000000000:ℝ) (1/10:ℝ)
 | .Cbridge6 => globalFace (94772530782231/100000000000000:ℝ) (1750010586289/1000000000000:ℝ) (1/10:ℝ)


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
end Qrh.JointDetector.CurvedRestartReturn
