/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Weil/LiftedBruhatWordEvaluation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Data.Complex.Basic

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

theorem representation_bruhat {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ell : V →ₗ[ℂ] ℂ) (b : V)
    (a w n n' a' l z a'' : G) (ψ c : ℂ)
    (hword : a * w * n = n' * (a * a') * l)
    (hl : ρ l b = b)
    (hroot : ∀ v, ell (ρ n' v) = ψ * ell v)
    (hprod : a * a' = z * a'')
    (hz : ∀ v, ρ z v = c • v) :
    ell (ρ (a * w * n) b) = ψ * c * ell (ρ a'' b) := by
  rw [hword, hprod]
  simp only [map_mul, Module.End.mul_apply, hl, hroot, hz, map_smul, smul_eq_mul]
  ring

end DedekindZetaZeroFree.OrbitExpansion.ExteriorDigits

end
