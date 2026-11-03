/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/Nonvanishing.lean
Original SHA-256: b7a0db47d5df23ce917323f50103c1cae0d5ecf5f3001542aa455bec050789df
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.CommonProbe
import Submissions.lw56e2_parameter_refinement.Transport.OriginalBaseline

/-! Improved nonvanishing using only the pinned OpenAI theorem and the
independent transport proved in this library. -/

namespace LW56e2.Transport
noncomputable section
open OAI.SevenEighths

theorem improved_hecke_boundary :
    HeckeZeroSupremum.beta≤(4374785349/5000000000 : ℝ) := by
  rw [←TunedCandidate.boundary_value]
  exact improved_hecke_boundary_of_original original_hecke_boundary

theorem hecke_nonvanishing (χ : HeckeFamily.Character) (s : ℂ)
    (hs : (4374785349/5000000000 : ℝ)<s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : HeckeFamily.LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (improved_hecke_boundary.trans_lt hs) hpole

theorem dirichlet_nonvanishing {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (4374785349/5000000000 : ℝ)<s.re)
    (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  PhysicalAnalytic.dirichlet_of_hecke_at_boundary (by norm_num)
    hecke_nonvanishing χ s hs hpole

theorem zeta_nonvanishing (s : ℂ)
    (hs : (4374785349/5000000000 : ℝ)<s.re) : riemannZeta s≠0 :=
  PhysicalAnalytic.zeta_of_hecke_at_boundary (by norm_num)
    hecke_nonvanishing s hs

end
end LW56e2.Transport
