import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowSlotScalesGeneric
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowReflectedLengthGeneric

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_three_halves : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))≤C := by
  obtain ⟨C,hC,hb⟩ :=
    ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2:ℝ)) (by norm_num)
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
    have hh := (canonicalSlotEquiv T hT).sum_comp
      (fun a=>elementNorm a.val^(-(3/2:ℝ)))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

private lemma inverse_half_of_lower_cap
    (a Z ell N : ℝ) (ha : 0<a) (hZ : 0<Z) (hN : 0<N)
    (hcap : a*Z^ell≤N) :
    N^(-(1/2:ℝ))≤a^(-(1/2:ℝ))*Z^(-ell/2) := by
  have hbase : 0<a*Z^ell := mul_pos ha (Real.rpow_pos_of_pos hZ _)
  have hsqrt : (a*Z^ell)^(1/2:ℝ)≤N^(1/2:ℝ) :=
    Real.rpow_le_rpow hbase.le hcap (by norm_num)
  have hinv : N^(-(1/2:ℝ))≤(a*Z^ell)^(-(1/2:ℝ)) := by
    rw [Real.rpow_neg hN.le,Real.rpow_neg hbase.le]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (Real.rpow_pos_of_pos hbase (1/2:ℝ)) hsqrt)
  apply hinv.trans_eq
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le ell),←Real.rpow_mul hZ.le]
  congr 1
  ring

/--
The lower slot caps save exactly one half of the unselected total length.
The constant is selected before `Z`, the prime pools, `J`, and all weights.
-/
theorem lowUnselectedMass_lower_bound_generic (K : ℕ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0<C ∧
    ∀(ell : Fin K→ℝ)(Z : ℝ),1≤Z→
    ∀(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(Yp : Fin K→ℝ),
      (∀i x,‖W i x‖≤1)→
      (∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W Yp p‖*
          elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ)))≤
        C*Z^(-lowUnselectedLength ell J/2) := by
  obtain ⟨Cs,hCs,hslot⟩ := canonical_slot_inverse_three_halves
  let D := Cs*a^(-(1/2:ℝ))
  let C := (max 1 D)^K
  have hD : 0<D := by dsimp [D];positivity
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro ell Z hZ T hT hlower J W Yp hW
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let slots := fun i=>canonicalSlotSupport (T i)
  have hslots : ∀i x,x∈slots i→x≠0 :=
    fun i=>canonicalSlotSupport_nonzero _ (hT i)
  simp_rw [lowUnselectedWeight_norm_identity (fun i=>canonicalSlotSupport (T i)) hslots]
  rw [←Fintype.prod_sum (fun (i : J) (x : canonicalSlotSupport (T i.val))=>
    elementNorm x.val^(-2:ℝ)*‖W i.val (elementNorm x.val/Yp i.val)‖)]
  have hone (i : J) :
      (∑x : canonicalSlotSupport (T i.val),
        elementNorm x.val^(-2:ℝ)*‖W i.val (elementNorm x.val/Yp i.val)‖)≤
      D*Z^(-ell i.val/2) := by
    have hterm (x : canonicalSlotSupport (T i.val)) :
        elementNorm x.val^(-2:ℝ)*‖W i.val (elementNorm x.val/Yp i.val)‖≤
        elementNorm x.val^(-(3/2:ℝ))*
          (a^(-(1/2:ℝ))*Z^(-ell i.val/2)) := by
      have hnx : 0<elementNorm x.val :=
        physicalElementNorm_pos _ (canonicalSlotSupport_nonzero _ (hT i.val) _ x.property)
      have hcap : a*Z^(ell i.val)≤elementNorm x.val := by
        obtain ⟨P,hP,hPx⟩ := Finset.mem_image.mp x.property
        rw [←hPx, primaryTuple_norm P (hT i.val P hP)]
        exact hlower i.val P hP
      have hhalf := inverse_half_of_lower_cap a Z (ell i.val)
        (elementNorm x.val) ha hz hnx hcap
      calc
        _≤elementNorm x.val^(-2:ℝ) :=
          mul_le_of_le_one_right (Real.rpow_nonneg hnx.le _) (hW i.val _)
        _=elementNorm x.val^(-(3/2:ℝ))*elementNorm x.val^(-(1/2:ℝ)) := by
          rw [←Real.rpow_add hnx]
          norm_num
        _≤_ := mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hnx.le _)
    calc
      _≤∑x : canonicalSlotSupport (T i.val),
          elementNorm x.val^(-(3/2:ℝ))*
            (a^(-(1/2:ℝ))*Z^(-ell i.val/2)) :=
        Finset.sum_le_sum (fun x _=>hterm x)
      _=(∑x : canonicalSlotSupport (T i.val),
          elementNorm x.val^(-(3/2:ℝ)))*
            (a^(-(1/2:ℝ))*Z^(-ell i.val/2)) := (Finset.sum_mul ..).symm
      _≤Cs*(a^(-(1/2:ℝ))*Z^(-ell i.val/2)) :=
        mul_le_mul_of_nonneg_right (hslot _ (hT i.val)) (by positivity)
      _=D*Z^(-ell i.val/2) := by dsimp [D];ring
  calc
    _≤∏i : J,D*Z^(-ell i.val/2) :=
      Finset.prod_le_prod₀
        (fun i _=>Finset.sum_nonneg (fun x _=>mul_nonneg
          (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
        (fun i _=>hone i)
    _=D^J.card*Z^(-lowUnselectedLength ell J/2) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Fintype.card_coe,←Real.rpow_sum_of_pos hz]
      congr 1
      rw [lowUnselectedLength]
      congr 1
      rw [←Finset.sum_div, ←Finset.sum_neg_distrib, (Finset.sum_coe_sort J (fun i=>-ell i))]
    _≤C*Z^(-lowUnselectedLength ell J/2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hz.le _)
      have hc : J.card≤K := by
        simpa using Finset.card_le_card (Finset.subset_univ J)
      calc
        D^J.card≤(max 1 D)^J.card :=
          pow_le_pow_left₀ hD.le (le_max_right _ _) _
        _≤(max 1 D)^K := pow_le_pow_right₀ (le_max_left _ _) hc
        _=C := rfl

lemma low_length_correction_absorbed
    (Etotal d : ℝ) (hd : 0≤d) (hEtotal1 : Etotal≤1/5) :
    max 0 (5*Etotal-1+d)/8-d/2≤0 := by
  have harg : 5*Etotal-1+d≤d := by linarith
  have hmax : max 0 (5*Etotal-1+d)≤d := max_le hd harg
  linarith

end SevenEighths.ProbePhysical
end

end OAI
