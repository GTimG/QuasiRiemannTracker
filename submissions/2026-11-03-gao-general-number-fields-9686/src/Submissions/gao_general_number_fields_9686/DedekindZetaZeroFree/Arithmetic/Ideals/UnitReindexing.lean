/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Ideals/UnitReindexing.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Profiles.FractionalIdealShapeLattice

@[expose] public section

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

theorem tsum_fractionalIdeal_mul_unit
    (K : Type*) [Field K] [NumberField K]
    (I : FractionalIdeal (𝓞 K)⁰ K) (u : (𝓞 K)ˣ) (f : K → ℂ) :
    (∑' x : ↥(I : Submodule (𝓞 K) K),
      f ((algebraMap (𝓞 K) K (u : 𝓞 K)) * (x : K))) =
      ∑' x : ↥(I : Submodule (𝓞 K) K), f (x : K) := by

  let e : ↥(I : Submodule (𝓞 K) K) ≃ ↥(I : Submodule (𝓞 K) K) :=
    { toFun := fun x =>
        ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ x.2⟩
      invFun := fun x =>
        ⟨algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (x : K), by
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ _ x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
            (algebraMap (𝓞 K) K (u : 𝓞 K) * (x : K)) = (x : K)
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      right_inv := fun x => by
        apply Subtype.ext
        show algebraMap (𝓞 K) K (u : 𝓞 K) *
            (algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (x : K)) = (x : K)
        rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul] }

  exact Equiv.tsum_eq e (fun x : ↥(I : Submodule (𝓞 K) K) => f (x : K))

end DedekindZetaZeroFree.AbelianQuotient.Theta.GaussianSchwartz

end
