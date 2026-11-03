/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Poisson/Lattices/EuclideanSummation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.HarmonicAnalysis.Poisson.Lattices.TranslationAndModulation

@[expose] public section

noncomputable section
open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace DedekindZetaZeroFree.PoissonArch

theorem summable_norm_poisson_lattice_shift_modulation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    Summable (fun v : L =>
      ‖𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))‖) ∧
    Summable (fun w : dualLattice L =>
      ‖𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b)‖) := by
  exact ⟨summable_norm_modulated_schwartz_translate L f a b,
    summable_norm_shifted_fourier_schwartz_dual_lattice L f a b⟩

theorem poisson_summation_lattice_shift_modulation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (f : 𝓢(V, ℂ)) (a b : V) :
    (∑' v : L, 𝐞 (inner ℝ (a + (v : V)) b) • f (a + (v : V))) =
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        ∑' w : dualLattice L,
          𝐞 (inner ℝ a (w : V)) • (𝓕 (f : V → ℂ)) ((w : V) - b) := by
  exact poisson_shift_modulation L f a b

end DedekindZetaZeroFree.PoissonArch

end
