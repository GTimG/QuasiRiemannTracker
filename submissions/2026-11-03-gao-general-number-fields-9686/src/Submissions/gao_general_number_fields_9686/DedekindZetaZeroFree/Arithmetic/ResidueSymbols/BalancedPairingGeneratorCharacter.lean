/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/ResidueSymbols/BalancedPairingGeneratorCharacter.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.Ideal.Basic

@[expose] public section

namespace DedekindZetaZeroFree.Hecke

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def balancedPairingGeneratorChar (B : R → M → ℂ)
    (hzero : ∀ t, B 0 t = 1)
    (hadd : ∀ x y t, B (x + y) t = B x t * B y t) (z : M) : AddChar R ℂ where
  toFun k := B k z
  map_zero_eq_one' := hzero z
  map_add_eq_mul' x y := hadd x y z

@[simp] theorem balancedPairingGeneratorChar_apply (B : R → M → ℂ)
    (hzero : ∀ t, B 0 t = 1)
    (hadd : ∀ x y t, B (x + y) t = B x t * B y t) (z : M) (k : R) :
    balancedPairingGeneratorChar B hzero hadd z k = B k z := rfl

theorem balancedPairingGeneratorChar_primitive (B : R → M → ℂ)
    (hzero : ∀ t, B 0 t = 1)
    (hadd : ∀ x y t, B (x + y) t = B x t * B y t)
    (hbalanced : ∀ r k t, B (r * k) t = B k (r • t))
    (hleft : ∀ k, (∀ t, B k t = 1) → k = 0)
    (z : M) (hz : Function.Surjective (fun r : R => r • z)) :
    ∀ J : Ideal R,
      (∀ x ∈ J, balancedPairingGeneratorChar B hzero hadd z x = 1) → J = ⊥ := by
  intro J hJ
  refine le_bot_iff.mp fun x hx => ?_
  rw [Submodule.mem_bot]
  refine hleft x fun t => ?_
  obtain ⟨r, hr⟩ := hz t
  rw [← hr]
  change B x (r • z) = 1
  rw [← hbalanced r x z]
  exact hJ (r * x) (J.mul_mem_left r hx)

end DedekindZetaZeroFree.Hecke
