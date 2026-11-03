/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Adeles/Characters/SIntegerTraceAnnihilation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.LocalFields.TraceCharacterConductor
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Adeles.Characters.SLocalTraceRestriction

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem sLocalTraceCharacter_sIntegerDiagonal_eq_one
    (hS : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))
    (t : sIntegerRing F S) :
    sLocalTraceCharacter F S (sIntegerDiagonal F S t) = 1 := by

  have hfinite : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)) = 1 :=
    fun v hv =>
      localFiniteCharacter_eq_one_of_mem_integers F v _
        ((mem_sIntegerRing_iff F S (t : F)).1 t.2 v hv)

  have hsub : Function.mulSupport
      (fun v : HeightOneSpectrum (𝓞 F) =>
        localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)))
      ⊆ (S : Set (HeightOneSpectrum (𝓞 F))) :=
    Function.mulSupport_subset_iff'.2 fun v hv => hfinite v hv
  have hfin :
      (∏ᶠ v : HeightOneSpectrum (𝓞 F),
        localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F))) =
      ∏ v ∈ S, localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)) :=
    finprod_eq_prod_of_mulSupport_subset _ hsub
  have hcoe :
      (∏ v : S, localFiniteCharacter F v.1 (algebraMap F (v.1.adicCompletion F) (t : F))) =
      ∏ v ∈ S, localFiniteCharacter F v (algebraMap F (v.adicCompletion F) (t : F)) :=
    (Finset.prod_subtype S (fun _ => Iff.rfl)
      (fun w => localFiniteCharacter F w (algebraMap F (w.adicCompletion F) (t : F)))).symm
  have hdiag := traceCharacter_diagonal_product_formula F (t : F)
  rw [sLocalTraceCharacter_apply]
  simp only [sIntegerDiagonal_apply, sLocalDiagonal_infinite, sLocalDiagonal_finite]
  rw [hcoe, ← hfin]
  exact hdiag

theorem sLocalTraceCharacter_sIntegerDiagonal_mul_eq_one
    (hS : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))
    (m n : sIntegerRing F S) :
    sLocalTraceCharacter F S
      (sIntegerDiagonal F S m * sIntegerDiagonal F S n) = 1 := by
  rw [← map_mul]
  exact sLocalTraceCharacter_sIntegerDiagonal_eq_one F S hS (m * n)

end DedekindZetaZeroFree

end
