/- Modified 2026-10-22 for Mark Lewko private candidate.
Original authors, license and notices retained below and in vendor/collet. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Lewko.QRH.Stage1.Return.Transport.Transport.PrincipalRemainderRegion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

set_option autoImplicit false
namespace LewkoStage1Return.Transport.Transport
noncomputable section
variable [QRH.LewkoStage1Return.Geometry.Parameters] [QRH.LewkoStage1Return.Geometry.Bounds]
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
end LewkoStage1Return.Transport.Transport
#print axioms LewkoStage1Return.Transport.Transport.actual_source_analytic
