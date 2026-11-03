/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/ParitySeriesMellin.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Unfolding.ParityThetaMellinIntegral

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.SeriesMellin

variable {K : Type} [Field K] [NumberField K]

theorem completed_eq (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    (RayTheta.Pδ D δ).Λ s = κδ K δ s * RayCoset.Zδ D δ s := by
  have h1 := (ThetaMellinIntegral.hasMellin D δ s hs).2
  have h2 := ((RayTheta.Pδ D δ).hasMellin (s := s)
    (by simpa [RayTheta.Pδ_k] using hs)).2
  rw [RayTheta.Pδ_f, RayTheta.Pδ_f₀] at h2
  rw [h1] at h2
  exact h2.symm

theorem uncompleted_eq (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    hδ K δ s * (RayTheta.Pδ D δ).Λ s = RayCoset.Zδ D δ s := by
  rw [completed_eq D δ s hs, ← mul_assoc,
    mul_comm (hδ K δ s) (κδ K δ s),
    FourierMellin.mellinFactor_mul_reciprocalGamma K δ s hs, one_mul]

end DedekindZetaZeroFree.AbelianQuotient.RayParity.SeriesMellin

end
