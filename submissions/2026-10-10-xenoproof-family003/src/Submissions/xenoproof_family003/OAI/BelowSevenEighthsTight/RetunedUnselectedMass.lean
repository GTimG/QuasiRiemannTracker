import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass

/- Decay of the ORIGINAL compensated unselected tuple mass. The original
   supported-ideal summability theorem supplies the constant; no prime number
   theorem or independence assumption is added. The exponent uses the explicit
   finite sum defining lowUnselectedLength in the pinned LowNominalGeometry. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.LowExtension
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_three_halves : ∃C : ℝ,0<C ∧
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


lemma canonical_slot_inverse_square_tail : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(hT : ∀P∈T,Supported P.val)(Y : ℝ),0<Y →
      (∀x∈canonicalSlotSupport T,Y≤elementNorm x) →
      (∑x : canonicalSlotSupport T,elementNorm x.val^(-2:ℝ))≤C*Y^(-(1/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_three_halves
  refine ⟨C,hC,?_⟩
  intro T hT Y hY hn
  have hp (x : canonicalSlotSupport T) :
      elementNorm x.val^(-2:ℝ)≤Y^(-(1/2:ℝ))*elementNorm x.val^(-(3/2:ℝ)) := by
    have hx := hY.trans_le (hn x.val x.property)
    have he : elementNorm x.val^(-2:ℝ)=
        elementNorm x.val^(-(1/2:ℝ))*elementNorm x.val^(-(3/2:ℝ)) := by
      rw [←Real.rpow_add hx]
      norm_num
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hY (hn x.val x.property) (by norm_num)) (by positivity)
  calc
    _≤∑x : canonicalSlotSupport T,Y^(-(1/2:ℝ))*elementNorm x.val^(-(3/2:ℝ)) :=
      Finset.sum_le_sum (fun x _=>hp x)
    _=Y^(-(1/2:ℝ))*(∑x : canonicalSlotSupport T,elementNorm x.val^(-(3/2:ℝ))) :=
      (Finset.mul_sum ..).symm
    _≤Y^(-(1/2:ℝ))*C := mul_le_mul_of_nonneg_left (hb T hT) (by positivity)
    _=_ := by ring

theorem lowUnselectedMass_decay (K : ℕ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧ ∀(ell : Fin K→ℝ)(Z : ℝ),0<Z →
    ∀(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ)) →
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤1) →
      (∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖*
          elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ)))≤
        C*Z^(-(∑i∈J,ell i)/2) := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_square_tail
  let A := C*a^(-(1/2:ℝ))
  refine ⟨(max 1 A)^K,by positivity,?_⟩
  intro ell Z hZ T hT hnorm J W P hW
  have htail (i : Fin K) :
      (∑x : canonicalSlotSupport (T i),elementNorm x.val^(-2:ℝ))≤A*Z^(-ell i/2) := by
    have hh := hb (T i) (hT i) (a*Z^(ell i)) (by positivity) (by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      rw [primaryTuple_norm p (hT i p hp)]
      exact hnorm i p hp)
    convert hh using 1
    rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le _),←Real.rpow_mul hZ.le]
    dsimp [A]
    rw [show ell i * (-(1/2:ℝ)) = -ell i/2 by ring]
    ring
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=>canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (p : canonicalSlotSupport (T i.val))=>
    elementNorm p.val^(-2:ℝ)*‖W i.val (elementNorm p.val/P i.val)‖)]
  calc
    _≤∏i : J,A*Z^(-ell i.val/2) := by
      apply Finset.prod_le_prod₀
        (fun i _=>Finset.sum_nonneg (fun p _=>mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      apply le_trans ?_ (htail i.val)
      apply Finset.sum_le_sum
      intro p hp
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) (-2:ℝ))
    _=A^J.card*Z^(-(∑i∈J,ell i)/2) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hZ]
      congr 2
      rw [←Finset.sum_div,Finset.sum_neg_distrib,Finset.sum_coe_sort]
    _≤_ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (pow_le_pow_left₀ (by dsimp [A];positivity) (le_max_right 1 A) J.card).trans
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))

#print axioms canonical_slot_inverse_square_tail
#print axioms lowUnselectedMass_decay
end
end BelowSevenEighthsTight.LowExtension
