/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/FixedSource.lean
Original SHA-256: 420a4e060363c53112c1ea73648fb959ad8e99fa989c3ee166290b7dff428d1b
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport

/-!
# Fixed source arithmetic data for an arbitrary actual error

The upstream SourceData record is indexed by HighData. Here HighData(1) is
only an auxiliary carrier for that existing record: none of its geometric
parameters are the tuned probe's parameters. Both required tail bounds are
obtained from one sufficiently large finite prime exclusion set. All later
moment theorems use independently specified actual slots and errors.
-/

namespace LW56e2.Transport.PhysicalHigh
noncomputable section
open scoped Classical ContDiff
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly Parameters
local notation "O" => HeckeFamily.O

/-- The arithmetic carrier exists for every actual positive error and every
specified finite set of prime exclusions. No hypothesis about beta is used. -/
theorem exists_tuned_source_data (e : ℝ) (he : 0 < e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀ P ∈ S₀, Prime P) :
    ∃ D : HighData (1 : ℝ), ∃ F : SourceData D,
      S₀ ⊆ F.S ∧ FirstTail (4 * e) F.S := by
  obtain ⟨D⟩ := exists_high_data (1 : ℝ) (by norm_num)
  obtain ⟨S,hsub,hS,hfirst,hmax⟩ :=
    exists_fixed_source (min e D.e) (lt_min he D.e_pos) S₀ hS₀
  have hseed : FirstTail (4 * D.e) S :=
    hfirst.mono_parameter (by linarith [min_le_right e D.e])
  have hactual : FirstTail (4 * e) S :=
    hfirst.mono_parameter (by linarith [min_le_left e D.e])
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,heq,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  let F : SourceData D :=
    ⟨S,hS,hmax,hseed,w,W,hw,hc,hs,hp,hb,hn,heq,hWn,hWs,hr,hWpos⟩
  exact ⟨D,F,hsub,hactual⟩

/-- The count constants are chosen at the actual reserved moment loss t,
before the moment degree and height exponent are selected. -/
theorem exists_tuned_count_parameters {Δ : ℝ} {D : HighData Δ}
    (F : SourceData D) (t : ℝ) (ht : 0 < t) :
    Nonempty (CountParameters F.modulus ⊤ t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x => (F.bounded x).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support
    (fun x => (F.bounded x).2) t ht

end
end LW56e2.Transport.PhysicalHigh
