/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Geometry/ArithmeticQuotients/Cusps/SiegelCoverAndTruncation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.PGL.SiegelReduction.UniformFrameBounds

@[expose] public section

noncomputable section
open scoped Classical Matrix
namespace DedekindZetaZeroFree

theorem kp_cusp_siegel_cover_and_truncation
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M)) :
    ∃ (n : ℕ) (q : Fin n → KPCuspArithmetic.Cusp F)
      (σ : Fin n → KPCuspArithmetic.PGL2 F) (t₀ : ℝ)
      (P : Fin n → Set (Fin (KPCuspLogShape.dimension F) → ℂ))
      (B : Fin n → Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F))),
      0 < n ∧
      (∀ a, σ a • KPCuspArithmetic.infinity F = q a) ∧
      (∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r) ∧
      (∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b) ∧
      (∀ a, IsCompact (P a) ∧ (P a).Nonempty ∧ IsCompact (B a) ∧ (B a).Nonempty) ∧
      (∀ z : KPArch.Space (KPCuspLogShape.dimension F),
        ∃ (γ : Γ) (a : Fin n) (w : KPArch.Space (KPCuspLogShape.dimension F)),
          w ∈ KPCuspSiegel.box F (P a) (B a) (Set.Ici t₀) ∧
          z = KPCuspSiegel.action F (γ : KPCuspArithmetic.PGL2 F)
            (KPCuspSiegel.action F (σ a) w)) ∧
      (∀ (a : Fin n) (T : ℝ),
        KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T =
          KPCuspSiegel.projection F Γ ''
            (KPCuspSiegel.action F (σ a) ''
              KPCuspSiegel.box F (P a) (B a) (Set.Ioi T))) ∧
      (∀ T : ℝ, t₀ < T →
        IsCompact (KPCuspSiegel.projection F Γ ''
          (⋃ a : Fin n, KPCuspSiegel.action F (σ a) ''
            KPCuspSiegel.box F (P a) (B a) (Set.Icc t₀ T))) ∧
        IsCompact ((Set.univ : Set (KPCuspSiegel.OrbitQuotient F Γ)) \
          (⋃ a : Fin n, KPCuspSiegel.projection F Γ ''
            KPCuspSiegel.highCusp F (σ a) T))) ∧
      ∃ T₁ : ℝ, t₀ < T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
        (Pairwise fun a b : Fin n =>
          Disjoint (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ a) T)
            (KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F (σ b) T)) ∧
        (∀ (a b : Fin n) (γ : Γ)
          (z : KPArch.Space (KPCuspLogShape.dimension F)),
          z ∈ KPCuspSiegel.highCusp F (σ a) T →
          KPCuspSiegel.action F (γ : KPCuspArithmetic.PGL2 F) z ∈
            KPCuspSiegel.highCusp F (σ b) T →
          a = b ∧ (γ : KPCuspArithmetic.PGL2 F) ∈ KPCuspSiegel.parabolic F Γ (q a)) ∧
        (∀ (a : Fin n) (g : KPCuspSiegel.parabolic F Γ (q a)),
          Set.MapsTo (KPCuspSiegel.action F (g : KPCuspArithmetic.PGL2 F))
            (KPCuspSiegel.highCusp F (σ a) T) (KPCuspSiegel.highCusp F (σ a) T)) ∧
        (∀ a : Fin n,
          ∃ e : KPCuspSiegel.CuspQuotient F Γ (q a) (KPCuspSiegel.highCusp F (σ a) T) →
            KPCuspSiegel.OrbitQuotient F Γ,
            Topology.IsEmbedding e ∧
            (∀ z : KPCuspSiegel.highCusp F (σ a) T,
              e (Quotient.mk _ z) = KPCuspSiegel.projection F Γ z)) := by
  exact kp_cusp_siegel_cover_and_truncation_proved F hF M hM Γ hΓ hcomm

end DedekindZetaZeroFree

end
