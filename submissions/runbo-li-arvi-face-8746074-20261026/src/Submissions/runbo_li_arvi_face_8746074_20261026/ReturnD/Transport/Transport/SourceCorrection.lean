/- Repeated marks: fork of Collet's generic return module Transport.Transport.SourceCorrection (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Transport.Transport.PrincipalRemainderRegion
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSignalComparison
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion

set_option autoImplicit false
namespace RepeatedMarksReturn.Transport.Transport
noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
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
end RepeatedMarksReturn.Transport.Transport
