/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Arithmetic/Kummer/LocallyPowerSUnitExtensionDegree.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Approximation.SupportedPrincipalFactorization
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Quotients.SupportedIdeleNormSurjectivity

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree

noncomputable section

set_option maxHeartbeats 800000

theorem arith_sunit_kummer_degree_one
    (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) (hCl : Subsingleton (ClassGroup A.R))
    (n : ℕ+) (hn : (n : ℕ) ∈ ({2, 3, 6} : Finset ℕ))
    (ε : A.U)
    (hlocal : ∀ v : A.Place,
      match v with
      | Sum.inl w =>
          (A.diagonal (ε : Fˣ)).1 w ∈ (powMonoidHom (n : ℕ)).range
      | Sum.inr w =>
          (A.diagonal (ε : Fˣ)).2 w ∈ (powMonoidHom (n : ℕ)).range)
    (hnF : ((n : ℕ) : F) ≠ 0) :
    let a : Fˣ := (ε : Fˣ)
    letI : FiniteDimensional F
        (KummerTheory.chosenSimpleKummerExtension F n hnF a) :=
      KummerTheory.chosenSimpleKummerExtension_finiteDimensional F n hnF a
    Module.finrank F (KummerTheory.chosenSimpleKummerExtension F n hnF a) = 1 := by
  classical
  have hcases : (n : ℕ) = 2 ∨ (n : ℕ) = 3 ∨ (n : ℕ) = 6 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hn
  have hmu : (primitiveRoots (n : ℕ) F).Nonempty := by
    rcases hcases with hn2 | hn3 | hn6
    · rw [hn2]
      exact ⟨A.zeta12 ^ 6, (mem_primitiveRoots (by decide)).2
        (A.primitive_zeta12.pow (by decide) (by decide : 12 = 6 * 2))⟩
    · rw [hn3]
      exact ⟨A.zeta12 ^ 4, (mem_primitiveRoots (by decide)).2
        (A.primitive_zeta12.pow (by decide) (by decide : 12 = 4 * 3))⟩
    · rw [hn6]
      exact A.primitive_sixth_root
  have hdiv : (n : ℕ) ∣ 6 := by
    rcases hcases with hn2 | hn3 | hn6 <;> simp [*]
  let a : Fˣ := (ε : Fˣ)
  let L := KummerTheory.chosenSimpleKummerExtension F n hnF a
  letI : FiniteDimensional F L :=
    KummerTheory.chosenSimpleKummerExtension_finiteDimensional F n hnF a
  letI : IsAbelianGalois F L :=
    KummerTheory.chosenSimpleKummerExtension_isAbelianGalois F n hnF hmu a
  letI : NumberField L := NumberField.of_module_finite F L
  have hSplit : ∀ v ∈ A.Sf, _root_.FinitePlaceSplitsCompletely (K := F) (L := L) v := by
    intro v hv
    exact KummerTheory.chosenSimpleKummerExtension_finitePlaceSplitsCompletely_of_mem_nthPowerSubgroup
      n hnF hmu a v (hlocal (Sum.inr ⟨v, hv⟩))
  have hAway : ∀ v ∉ A.Sf, _root_.ChosenFinitePlaceIsUnramified (K := F) (L := L) v := by
    intro v hv
    have hnval : v.valuation F ((n : ℕ) : F) = 1 := by
      have hndvd : ((n : ℕ) : 𝓞 F) ∣ (6 : 𝓞 F) := by
        obtain ⟨k, hk⟩ := hdiv
        refine ⟨(k : 𝓞 F), ?_⟩
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          congrArg (Nat.cast : ℕ → 𝓞 F) hk
      have hnnot : ((n : ℕ) : 𝓞 F) ∉ v.asIdeal := by
        intro hmem
        exact hv (A.above_six v (v.asIdeal.mem_of_dvd hndvd hmem))
      simpa only [map_natCast] using
        (v.valuation_eq_one_iff_notMem (K := F)).2 hnnot
    have haval : v.valuation F (a : F) = 1 := ε.property v hv
    exact KummerTheory.chosenSimpleKummerExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one
      n hnF hmu a v haval hnval
  have hInf : ∀ w : NumberField.InfinitePlace F,
      _root_.infiniteTensorNormSubgroup (K := F) (L := L) w = ⊤ := by
    intro w
    exact KummerTheory.chosenSimpleKummerExtension_infiniteTensorNormSubgroup_eq_top_of_mem_nthPowerSubgroup
      n hnF hmu a w (hlocal (Sum.inl w))
  exact (ideleClassNorm_range_top_and_finrank_eq_one_of_supportedAt F L A.Sf
    hSplit hAway hInf
    (supportedAt_sup_principalSubgroup_eq_top_of_classGroup_subsingleton F A hCl)).2

end

end DedekindZetaZeroFree
