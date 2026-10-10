import Cycle25.Assembly.Low.Geometry
import OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import Cycle25.Assembly.Low.Detector.LowSlotScales
import Cycle25.Assembly.Low.Detector.LowNominalGeometry
/-! Adapted from OpenAI/math family003, pinned original module Detector.LowUnselectedMass.
Changed physical geometry and explicit compensation bookkeeping; upstream is unchanged.
Apache-2.0 upstream attribution retained. -/

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.Cycle25WeightedProbeLow
open ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_three_halves : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))≤C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2:ℝ)) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=>I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-(3/2:ℝ)) := by
    rw [Finset.sum_image (fun P _ Q _ h=>hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=>elementNorm a.val^(-(3/2:ℝ)))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

lemma lowUnselectedWeight_norm_identity {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖ =
      ∏i : J,elementNorm (a i).val^(-(3/2:ℝ))*‖W i.val (elementNorm (a i).val/P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  rw [elementNorm_finset_prod,Finset.prod_mul_distrib,Real.finsetProd_rpow Finset.univ
    (fun i : J=>elementNorm (a i).val) (fun i _=>by unfold elementNorm;positivity)]

theorem lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤M) :
    ∃C : ℝ,0<C ∧ ∀(T : Fin K→Finset PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤M)→
      (∑a : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P a‖)≤C := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_three_halves
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=>canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-(3/2:ℝ))*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod₀ (fun i _=>Finset.sum_nonneg (fun a _=>mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ))*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-(3/2:ℝ)))*M := (Finset.sum_mul ..).symm
        _≤C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun _ _=>le_max_right _ _)
    _≤_ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))

/-- The unselected prime norm supplies the exact power needed by the relaxed energy. -/
theorem lowUnselectedMass_decay (K : ℕ) (M a : ℝ) (hM : 0≤M) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀(ell : Fin K→ℝ)(Z : ℝ),0<Z→
    ∀(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
    (∀i n,n∈canonicalSlotSupport (T i)→a*Z^(ell i)≤elementNorm n)→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
    (∀i x,‖W i x‖≤M)→
    (∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖*
        elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ)))≤C*Z^(-lowUnselectedLength ell J/2) := by
  obtain ⟨C,hC,hbound⟩ := lowUnselectedMass_bound K M hM
  let c := (min 1 a)^K
  have hc : 0<c := by dsimp [c];positivity
  refine ⟨C*c^(-(1/2:ℝ)),by positivity,?_⟩
  intro ell Z hZ T hT hlower J W P hW
  have hp (p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ))≤c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
    have hh := lowUnselectedProduct_norm_lower ell a Z ha hZ _ hlower J p
    have hb := Real.rpow_le_rpow_of_nonpos (show 0<c*Z^(lowUnselectedLength ell J) by positivity) hh (show -(1/2:ℝ)≤0 by norm_num)
    have hid : (c*Z^(lowUnselectedLength ell J))^(-(1/2:ℝ))=c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le]
      congr 2
      ring
    exact hb.trans_eq hid
  calc
    _≤∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
        Finset.sum_le_sum (fun p _=>mul_le_mul_of_nonneg_left (hp p) (norm_nonneg _))
    _=(∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
      ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖)*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) := (Finset.sum_mul ..).symm
    _≤C*(c^(-(1/2:ℝ))*Z^(-lowUnselectedLength ell J/2)) :=
      mul_le_mul_of_nonneg_right (hbound T hT J W P hW) (by positivity)
    _=_ := by ring

end SevenEighths.Cycle25WeightedProbeLow
end

end OAI
