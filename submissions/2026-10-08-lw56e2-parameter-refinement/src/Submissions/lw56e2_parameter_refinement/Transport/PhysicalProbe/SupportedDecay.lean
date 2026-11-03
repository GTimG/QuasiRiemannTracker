/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalProbe/SupportedDecay.lean
Original SHA-256: a2e8aba661727db360a2c1499dd1714c55c9b70a7bc8409bd155dba41234b20b
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import Submissions.lw56e2_parameter_refinement.Transport.SupportedMass

/-!
# Supported mass of the actual canonical slot tuples

This instantiates the finite support-decay argument on the actual ideals,
canonical primary generators, and compensated tuple weights in OpenAI003.
The uniform three-halves mass is proved from the source's ideal summability
lemma; it is not assumed. All original source files remain unchanged.
-/

namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma transport_canonical_slot_inverse_three_halves : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2):ℝ))≤C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2)) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=>I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2):ℝ))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-(3/2):ℝ) := by
    rw [Finset.sum_image (fun P _ Q _ h=>hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=>elementNorm a.val^(-(3/2):ℝ))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

/-- Actual compensated tuple mass with scale decay retained. The support
lower bound is allowed to depend on the slot exponent; the constant is uniform
in the finite prime sets, the subset, and the scale. -/
theorem transport_lowUnselectedMass_decay (K : ℕ) (M a : ℝ)
    (hM : 0 ≤ M) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Fin K → ℝ) (Z : ℝ), 0 < Z →
      ∀ (T : Fin K → Finset PrimeIdeal) (_hT : ∀ i P, P ∈ T i → Supported P.val),
      (∀ i x, x ∈ canonicalSlotSupport (T i) → a * Z ^ (ell i) ≤ elementNorm x) →
      ∀ (J : Finset (Fin K)) (W : Fin K → ℝ → ℂ) (P : Fin K → ℝ),
      (∀ i x, ‖W i x‖ ≤ M) →
      (∑ t : LowUnselectedTuple (fun i => canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i => canonicalSlotSupport (T i)) J W P t‖ *
          elementNorm (∏ i : J, (t i).val) ^ (-(1/2 : ℝ))) ≤
        C * Z ^ (-lowUnselectedLength ell J / 2) := by
  obtain ⟨C, hC, hb⟩ := transport_canonical_slot_inverse_three_halves
  let D := C * M * a ^ (-(1/2 : ℝ))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨(max 1 D)^K, by positivity, ?_⟩
  intro ell Z hZ T hT hlower J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _
    (fun i => canonicalSlotSupport_nonzero _ (hT i))]
  rw [← Fintype.prod_sum (fun (i : J) (t : canonicalSlotSupport (T i.val)) =>
    elementNorm t.val ^ (-2 : ℝ) * ‖W i.val (elementNorm t.val / P i.val)‖)]
  have hslot (i : J) :
      (∑ t : canonicalSlotSupport (T i.val),
        elementNorm t.val ^ (-2 : ℝ) * ‖W i.val (elementNorm t.val / P i.val)‖) ≤
        D * Z ^ (-ell i.val / 2) := by
    have hm : (∑ t : canonicalSlotSupport (T i.val),
        ‖W i.val (elementNorm t.val / P i.val)‖ *
          elementNorm t.val ^ (-(3/2 : ℝ))) ≤ C * M := by
      calc
        _ ≤ ∑ t : canonicalSlotSupport (T i.val),
            M * elementNorm t.val ^ (-(3/2 : ℝ)) := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_right (hW i.val _)
            (Real.rpow_nonneg (by unfold elementNorm; positivity) _)
        _ = M * ∑ t : canonicalSlotSupport (T i.val),
            elementNorm t.val ^ (-(3/2 : ℝ)) := (Finset.mul_sum ..).symm
        _ ≤ M * C := mul_le_mul_of_nonneg_left (hb _ (hT i.val)) hM
        _ = C * M := mul_comm _ _
    have hs := LW56e2.Transport.SupportedMass.weighted_mass_decay Finset.univ
      (fun t : canonicalSlotSupport (T i.val) => elementNorm t.val)
      (fun t => ‖W i.val (elementNorm t.val / P i.val)‖)
      ha hZ (fun t _ => norm_nonneg _) (fun t _ _ => hlower i.val _ t.property) hm
    simpa only [mul_comm (elementNorm _ ^ (-2 : ℝ)), D] using hs
  calc
    _ ≤ ∏ i : J, D * Z ^ (-ell i.val / 2) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Finset.sum_nonneg (fun t _ => mul_nonneg
          (Real.rpow_nonneg (by unfold elementNorm; positivity) _) (norm_nonneg _))
      · intro i hi
        exact hslot i
    _ = D^J.card * Z ^ (-lowUnselectedLength ell J / 2) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← Real.rpow_sum_of_pos hZ]
      congr 2
      simp only [lowUnselectedLength, div_eq_mul_inv, ← Finset.sum_mul,
        Finset.sum_neg_distrib, Finset.sum_coe_sort]
    _ ≤ (max 1 D)^K * Z ^ (-lowUnselectedLength ell J / 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
      calc
        D^J.card ≤ (max 1 D)^J.card := pow_le_pow_left₀ hD (le_max_right _ _) _
        _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _)
          (by simpa using Finset.card_le_card (Finset.subset_univ J))

end SevenEighths.ProbePhysical
end
end OAI
