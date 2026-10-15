import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowRemoteMass
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.LowNominalGeometryGeneric

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma canonicalTuple_count_generic {K : ℕ} (Etotal : ℝ)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Etotal)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤
      (128*max 1 b)^K*Z^Etotal := by
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      apply Finset.prod_le_prod₀ (fun i _=>Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _)
          (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
        Fintype.card_fin,←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤_ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma compensation_scale_mass_bound_generic {K : ℕ}
    (η : HeckeFamily.Character) (C : CalibrationData)
    (Etotal lx ly : ℝ) (hxy : lx+ly=1-Etotal)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤Etotal)
    (b Z : ℝ) (hZ : 1≤Z) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=>compensationSubsetWeight η W (fun i=>Z^(ell i))
        (fun i=>(p i).val) J)
      (fun p=>Z^lx/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=>Z^ly/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=>W i.val)
      (fun p i=>elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=>Z^(ell i))
          (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val
          (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C
          (Z^lx/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^ly/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^(1-Etotal) := by
    have hcoeff : ‖compensationSubsetWeight η W (fun i=>Z^(ell i))
        (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val
          (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 :=
      (mul_le_of_le_one_left
        (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
        (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans
          (Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
            (fun (i : SelectedSlot J) _=>hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [lowPhysicalScale_source_generic C Etotal lx ly Z _ hz hxy]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=>hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right
    (canonicalTuple_count_generic Etotal ell hell hsum b Z hZ T hT hnorm)
    (show 0≤elementNorm C.generator*Z^(1-Etotal) by
      unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*
      (Z^Etotal*Z^(1-Etotal)) := by ring
    _=_ := by rw [←Real.rpow_add hz, show Etotal+(1-Etotal) = (1 : ℝ) by ring, Real.rpow_one]

end SevenEighths.ProbePhysical
end

end OAI
