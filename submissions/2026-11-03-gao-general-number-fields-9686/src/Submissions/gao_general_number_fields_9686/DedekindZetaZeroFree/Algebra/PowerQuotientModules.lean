/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Algebra/PowerQuotientModules.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

namespace DedekindZetaZeroFree

abbrev PowerQuotient (G : Type*) [CommGroup G] (n : ℕ) : Type _ :=
  G ⧸ (powMonoidHom (α := G) n).range

theorem powerQuotient_pow_eq_one (G : Type*) [CommGroup G] (n : ℕ)
    (q : PowerQuotient G n) : q ^ n = 1 := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact MonoidHom.mem_range.mpr ⟨g, powMonoidHom_apply n g⟩

noncomputable instance instPowerQuotientModule (G : Type*) [CommGroup G] (n : ℕ) :
    Module (ZMod n) (Additive (PowerQuotient G n)) :=
  AddCommGroup.zmodModule (by
    intro x
    rw [← ofMul_toMul x, ← ofMul_pow]
    simp [powerQuotient_pow_eq_one G n x.toMul])

def addEquivToZModLinearEquiv (n : ℕ) (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module (ZMod n) M] [Module (ZMod n) N]
    (e : M ≃+ N) : M ≃ₗ[ZMod n] N :=
  { e with
    map_smul' := by
      intro c x
      exact ZMod.map_smul e c x }

end DedekindZetaZeroFree
