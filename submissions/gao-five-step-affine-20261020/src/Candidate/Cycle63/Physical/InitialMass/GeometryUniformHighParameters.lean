/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalParameters
import Candidate.Cycle63.Moment.HighParameters

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open Cycle63Moment

/-- Choose a single height cutoff after all actual-subset density receipts
are known. Each subset retains its own profile-bound function and source
parameters; no change of Fourier cardinality is involved. -/
theorem geometry_uniform_high_height {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι→HighSourceParameters) (J : ι→ℕ) (μ : ℝ)
    (hμ : 0<μ) (hs : ∀i,0<(P i).vslot) (hp : ∀i,0<(P i).vplain) :
    ∃τ : ℝ, 0<τ ∧ τ≤μ/16 ∧ ∀i,
      2*τ<(P i).d*(P i).vslot ∧ 8*τ≤(P i).d*(P i).vslot ∧
      16*τ≤(P i).d*(P i).vplain ∧ 2*τ*((J i:ℝ)+1)≤μ/8 := by
  let rate := fun i=>geometryFinalHeight μ (P i).d (P i).vslot (P i).vplain (J i)
  have gates (i : ι) := geometry_final_height_gates μ (P i).d (P i).vslot
    (P i).vplain (J i) hμ (P i).hd (hs i) (hp i)
  let τ := Finset.univ.inf' Finset.univ_nonempty rate
  have hτ : 0<τ := (Finset.lt_inf'_iff _).mpr (fun i _=>(gates i).1)
  have hle (i : ι) : τ≤ rate i := Finset.inf'_le rate (Finset.mem_univ i)
  let i₀ : ι := Classical.choice inferInstance
  refine ⟨τ,hτ,(hle i₀).trans (gates i₀).2.1,?_⟩
  intro i
  have hsmall := hle i
  have hg := gates i
  change τ≤geometryFinalHeight μ (P i).d (P i).vslot (P i).vplain (J i) at hsmall
  have hJ : 0≤(J i:ℝ)+1 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hsmall hJ
  exact ⟨by linarith [hg.2.2.1],by linarith [hg.2.2.1],
    by linarith [hg.2.2.2.1],by linarith [hg.2.2.2.2]⟩

end
end OAI.SevenEighths.Cycle63InitialMass
