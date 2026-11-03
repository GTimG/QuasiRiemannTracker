/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Jacquet/FiniteWhittakerProjectors.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.FiniteAdditiveLevelsAndAnnihilators

@[expose] public section

noncomputable section
open scoped Classical Topology NumberField
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors

section Algebra
variable {k G V : Type*} [CommRing k] [Monoid G]
  [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (n : Multiplicative k →* G)
  (a : kˣ → G) (e : AddChar k ℂ) (ell : V →ₗ[ℂ] ℂ)

def translateSum {I : Type*} (s : Finset I) (c : I → ℂ) (t : I → k) : V →ₗ[ℂ] V :=
  ∑ i ∈ s, c i • ρ (n (Multiplicative.ofAdd (t i)))

theorem translateSum_apply {I : Type*} (s : Finset I) (c : I → ℂ) (t : I → k)
    (v : V) :
    translateSum ρ n s c t v =
      ∑ i ∈ s, c i • ρ (n (Multiplicative.ofAdd (t i))) v := by
  simp [translateSum]

end Algebra

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
