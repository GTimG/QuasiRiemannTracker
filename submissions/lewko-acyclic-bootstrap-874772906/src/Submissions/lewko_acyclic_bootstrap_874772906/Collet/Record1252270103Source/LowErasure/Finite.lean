/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Whole original-slot deletion for an arbitrary row-only complex cofactor. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.LowErasure
noncomputable section
open scoped Classical BigOperators

/-- Squared finite norm; no factorization is required of the cofactor D. -/
def retainedNorm {Row Slot : Type*} (rows : Finset Row) (weight : Row→ℝ)
    (D : Row→ℂ) (slot : Row→Slot→ℂ) (F : Finset Slot) : ℝ :=
  ∑ r∈rows, ‖D r*∏j∈F,slot r j‖^2*weight r

def erasurePayment {Slot : Type*} (Z q pay : ℝ) (w : Slot→ℝ)
    (T F : Finset Slot) : ℝ := pay^(T\F).card * Z^(q*∑j∈T\F,w j)

lemma erasurePayment_nonneg {Slot : Type*} (Z q pay : ℝ) (w : Slot→ℝ)
    (T F : Finset Slot) (hZ : 0≤Z) (hp : 0≤pay) :
    0≤erasurePayment Z q pay w T F := by
  unfold erasurePayment
  positivity

theorem cofactor_product_erasure {Slot : Type*} (T F : Finset Slot) (hF : F⊆T)
    (D : ℂ) (slot : Slot→ℂ) (Z q pay : ℝ) (w : Slot→ℝ) (hZ : 0<Z)
    (hslot : ∀j∈T\F,‖slot j‖^2≤pay*Z^(q*w j)) :
    ‖D*∏j∈T,slot j‖^2 ≤ erasurePayment Z q pay w T F * ‖D*∏j∈F,slot j‖^2 := by
  have he : D*∏j∈T,slot j=(∏j∈T\F,slot j)*(D*∏j∈F,slot j) := by
    rw [←Finset.prod_sdiff hF]
    ring
  rw [he,norm_mul,mul_pow,norm_prod,←Finset.prod_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _≤∏j∈T\F,pay*Z^(q*w j) := Finset.prod_le_prod₀ (fun j _=>sq_nonneg _) hslot
    _=erasurePayment Z q pay w T F := by
      rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,←Finset.mul_sum]
      simp only [erasurePayment,Finset.prod_const]

theorem fixed_retained_norm {Row Slot : Type*} (rows : Finset Row)
    (weight : Row→ℝ) (D : Row→ℂ) (slot : Row→Slot→ℂ) (T F : Finset Slot)
    (hF : F⊆T) (hw : ∀r∈rows,0≤weight r) (Z q pay : ℝ) (w : Slot→ℝ)
    (hZ : 0<Z)
    (hslot : ∀r∈rows,weight r≠0 → ∀j∈T\F,‖slot r j‖^2≤pay*Z^(q*w j)) :
    retainedNorm rows weight D slot T ≤
      erasurePayment Z q pay w T F * retainedNorm rows weight D slot F := by
  unfold retainedNorm
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  by_cases hz : weight r=0
  · simp only [hz,mul_zero,le_refl]
  · exact (mul_le_mul_of_nonneg_right
      (cofactor_product_erasure T F hF (D r) (slot r) Z q pay w hZ (hslot r hr hz))
      (hw r hr)).trans_eq (by ring)

lemma retainedNorm_nonneg {Row Slot : Type*} (rows : Finset Row) (weight : Row→ℝ)
    (D : Row→ℂ) (slot : Row→Slot→ℂ) (F : Finset Slot) (hw : ∀r∈rows,0≤weight r) :
    0≤retainedNorm rows weight D slot F :=
  Finset.sum_nonneg (fun r hr => mul_nonneg (sq_nonneg _) (hw r hr))

lemma retainedNorm_mono_rows {Row Slot : Type*} (rows small : Finset Row)
    (hsmall : small⊆rows) (weight : Row→ℝ) (D : Row→ℂ) (slot : Row→Slot→ℂ)
    (F : Finset Slot) (hw : ∀r∈rows,0≤weight r) :
    retainedNorm small weight D slot F≤retainedNorm rows weight D slot F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hsmall
  intro r hr _
  exact mul_nonneg (sq_nonneg _) (hw r hr)
end
end QRH.Record1252270103Source.LowErasure
#print axioms QRH.Record1252270103Source.LowErasure.cofactor_product_erasure
#print axioms QRH.Record1252270103Source.LowErasure.fixed_retained_norm
