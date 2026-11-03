/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Analysis/UnboundedOperators/DenseTestsAndGreenIdentity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestEnergy

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree
namespace KPTestGreenTransfer

variable {S T H V : Type*}
  [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem laplacian_pairing
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w)))
    (f g : KPTestOperator.testDomain ι) :
    inner ℂ (KPTestOperator.descend ι hι j A f)
        (KPTestOperator.descend ι hι j A g) =
      inner ℂ (f : H) (KPTestOperator.laplacian ι hι A B g) := by
  rw [KPTestOperator.laplacian_eq_divergence_differential ι hι j hj A B g]
  exact KPTestOperator.descend_formalAdjoint ι hι j hj A B hgreen f
    ⟨KPTestOperator.descend ι hι j A g, KPTestOperator.descend_mem ι hι j A g⟩

theorem descend_dense_green
    (ι : S →ₗ[ℂ] H) (hι : Function.Injective ι)
    (j : T →ₗ[ℂ] V) (hj : Function.Injective j)
    (A : S →ₗ[ℂ] T) (B : T →ₗ[ℂ] S)
    (hscalar : DenseRange ι) (hcotangent : DenseRange j)
    (hgreen : ∀ f : S, ∀ w : T,
      inner ℂ (j (A f)) (j w) = inner ℂ (ι f) (ι (B w))) :
    Dense (KPTestOperator.testDomain ι : Set H) ∧
      Dense (KPTestOperator.testDomain j : Set V) ∧
      (KPTestOperator.descend ι hι j A).IsFormalAdjoint
        (KPTestOperator.descend j hj ι B) ∧
      (∀ (f : KPTestOperator.testDomain ι) (w : KPTestOperator.testDomain j),
        inner ℂ (KPTestOperator.descend ι hι j A f) (w : V) =
          inner ℂ (f : H) (KPTestOperator.descend j hj ι B w)) ∧
      (∀ f g : KPTestOperator.testDomain ι,
        inner ℂ (KPTestOperator.descend ι hι j A f)
            (KPTestOperator.descend ι hι j A g) =
          inner ℂ (f : H) (KPTestOperator.laplacian ι hι A B g)) := by
  have hs : Dense (KPTestOperator.testDomain ι : Set H) := by
    simpa only [KPTestOperator.testDomain, LinearMap.coe_range, DenseRange] using hscalar
  have ht : Dense (KPTestOperator.testDomain j : Set V) := by
    simpa only [KPTestOperator.testDomain, LinearMap.coe_range, DenseRange] using hcotangent
  have hf := KPTestOperator.descend_formalAdjoint ι hι j hj A B hgreen
  exact ⟨hs, ht, hf, hf, laplacian_pairing ι hι j hj A B hgreen⟩

end KPTestGreenTransfer
end DedekindZetaZeroFree

end
