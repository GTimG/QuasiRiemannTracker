/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Restart return: h < .813, y < .473, ell < .173, row fee 1e-9.
All numerical proof obligations are re-elaborated; inherited notices follow. -/
/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Adapted for the fine-chain return: h < .810, floor reserve 1/10000.
All inherited notices follow unchanged; upstream source files are unmodified. -/
/- Repeated marks: fork of Collet's generic return module Transport.Transport.SourceCorrection (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Modified by Sil (2026-10-26): forked into QRH.SilDensitySplit.Return (namespaces and imports renamed);
re-elaborated against the widened coarse box `BoundsN` (873/1000<θ, h<806/1000, ell<171/1000) and,
where used, the physical slot cap as the `PhysicalSchedule` field `cap`. -/
import Candidate.Local.Qrh.JointDetector.RestartPhysical.Transport.Transport.PrincipalRemainderRegion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

set_option autoImplicit false
namespace Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [Qrh.JointDetector.RestartPhysical.Return.Geometry.BoundsN]
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.PrincipalSignalComparison
open OAI.SevenEighths.HeckeFamily OAI.SevenEighths.ProbePhysical

/-- The original source correction, analytically extended to the fresh boundary.
This proves the analytic clause and carries no source-moment or probe premise. -/
theorem actual_source_analytic
    (S : Finset (Ideal OAI.SevenEighths.HeckeFamily.O)) (hS : SourceExclusions S)
    (η : Character) :
    (∀ I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|Arithmetic.theta<s.re} ∧
    (∀s : ℂ,Arithmetic.theta<s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  refine ⟨excludePrimes_mask η S hS.prime,?_,?_⟩
  · exact remainder_globalClosedCorrection_analytic_x η S hS.tail 1 (1/6)
      (by norm_num) (by norm_num)
  · intro s hs
    exact remainder_globalClosedCorrection_bound η S hS.tail s 1 (1/6)
      hs.le (by norm_num) (by norm_num)

end
end Qrh.JointDetector.RestartPhysical.TransportKernel.Transport.Transport
