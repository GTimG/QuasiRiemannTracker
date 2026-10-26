/- Copyright (c) 2026 Sil. Apache-2.0.
Absolute aggregation for the actual annularly normalized marked coefficients.
Used only for the fixed-inducing principal estimate, not for physical moments.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.PrincipalUniform
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.KernelMarkedRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
namespace Candidate.FourthPower.PrincipalMarkedMass
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceMass
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelNaturalSlots KernelMarkedRows KernelAssignmentReindex KernelLabelledSlots
open KernelPunctureRows
local notation "Id" => Ideal ActualEisensteinCubic.O

theorem slot_mass (χ : Character) (atoms pool : Finset Id) (β : Id → ℂ)
    (P B : ℝ) (hP : 0 < P) (hB : 0 ≤ B)
    (hp : ∀ I ∈ pool, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P)
    (hβ : ∀ I ∈ pool, ‖β I‖ ≤ B) :
    (∑ I ∈ atoms, ‖slotTerm χ pool β P I‖) ≤ 256*B*Real.sqrt P := by
  let M := (Real.sqrt P)⁻¹*B
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (I : Id) : ‖slotTerm χ pool β P I‖ ≤ if I ∈ pool then M else 0 := by
    by_cases hi : I ∈ pool
    · simp only [slotTerm,hi,ite_true,norm_mul,norm_inv,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg P)]
      calc
        _ ≤ (Real.sqrt P)⁻¹*1*B := mul_le_mul
          (mul_le_mul_of_nonneg_left (idealCoeff_norm_le_one χ I) (by positivity))
          (hβ I hi) (norm_nonneg _) (by positivity)
        _ = _ := by dsimp [M]; ring
    · simp [slotTerm,hi]
  have hsub : pool ⊆ idealBall (2*P) := by
    intro I hi
    exact (mem_idealBall _ _).mpr ⟨(hp I hi).1.1,(hp I hi).2⟩
  have hc : (pool.card : ℝ) ≤ 256*P := by
    have hh : (pool.card : ℝ) ≤ (idealBall (2*P)).card := by
      exact_mod_cast Finset.card_le_card hsub
    exact hh.trans ((idealBall_card (2*P) (by positivity)).trans_eq (by ring))
  have hf : atoms.filter (fun I => I ∈ pool) ⊆ pool := fun _ h => (Finset.mem_filter.mp h).2
  have hcf : ((atoms.filter (fun I => I ∈ pool)).card : ℝ) ≤ pool.card := by
    exact_mod_cast Finset.card_le_card hf
  have hs : (Real.sqrt P)⁻¹*P=Real.sqrt P := by
    calc
      _ = (Real.sqrt P)⁻¹*(Real.sqrt P*Real.sqrt P) :=
        congrArg (fun x => (Real.sqrt P)⁻¹*x) (Real.mul_self_sqrt hP.le).symm
      _ = _ := inv_mul_cancel_left₀ (Real.sqrt_pos.mpr hP).ne' _
  calc
    _ ≤ ∑ I ∈ atoms, if I ∈ pool then M else 0 := Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ((atoms.filter (fun I => I ∈ pool)).card : ℝ)*M := by rw [← Finset.sum_filter]; simp
    _ ≤ (256*P)*M := mul_le_mul_of_nonneg_right (hcf.trans hc) hM
    _ = 256*B*((Real.sqrt P)⁻¹*P) := by dsimp [M]; ring
    _ = _ := by rw [hs]

theorem prime_slot_mass (χ : Character) (S : Finset PrimeIdeal) (pool : Finset Id)
    (β : Id → ℂ) (P B : ℝ) (hP : 0 < P) (hB : 0 ≤ B)
    (hp : ∀ I ∈ pool, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P)
    (hβ : ∀ I ∈ pool, ‖β I‖ ≤ B) :
    (∑ Q : S, ‖slotTerm χ pool β P Q.val.val‖) ≤ 256*B*Real.sqrt P := by
  have h := slot_mass χ (primeValues S) pool β P B hP hB hp hβ
  unfold primeValues at h
  rw [Finset.sum_image (by intro Q _ R _ hh; exact Subtype.val_injective hh)] at h
  rw [Finset.sum_coe_sort S (fun Q : PrimeIdeal => ‖slotTerm χ pool β P Q.val‖)]
  exact h

variable {ι : Type*} [Fintype ι]

theorem weighted_norm_le {A : Type*} [Fintype A] (a : ι → A → ℂ)
    (G : (ι → A) → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ slot, Function.Injective slot → (∏ i, a i (slot i)) ≠ 0 → ‖G slot‖ ≤ C) :
    ‖weightedSum a G‖ ≤ C*∏ i, ∑ p, ‖a i p‖ := by
  unfold weightedSum
  calc
    _ ≤ ∑ slot : ι → A, ‖if Function.Injective slot then G slot*∏ i, a i (slot i) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ slot : ι → A, C*∏ i, ‖a i (slot i)‖ := by
      apply Finset.sum_le_sum
      intro slot _
      by_cases hi : Function.Injective slot
      · rw [ite_eq_left hi,norm_mul]
        by_cases hz : (∏ i, a i (slot i))=0
        · rw [hz,norm_zero,mul_zero]
          exact mul_nonneg hC (Finset.prod_nonneg (fun i _ => norm_nonneg _))
        · rw [norm_prod]
          exact mul_le_mul_of_nonneg_right (hG slot hi hz)
            (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      · rw [ite_eq_right hi,norm_zero]
        exact mul_nonneg hC (Finset.prod_nonneg (fun i _ => norm_nonneg _))
    _ = _ := by rw [← Finset.mul_sum,← Fintype.prod_sum (fun i : ι => fun p : A => ‖a i p‖)]

theorem active_pool (χ : Character) (S : Finset PrimeIdeal)
    (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ) (slot : ι → S)
    (h : (∏ i, naturalCoefficients χ S pool β P i (slot i)) ≠ 0) :
    ∀ i, (slot i).val.val ∈ pool i := by
  intro i
  by_contra hi
  apply h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [naturalCoefficients,slotTerm,hi])

def supportIdeal (F : Id) (S : Finset PrimeIdeal) (slot : ι → S) : Id :=
  F*∏ i, (slot i).val.val

theorem support_nonzero (F : Id) (hF : F ≠ 0) (S : Finset PrimeIdeal) (slot : ι → S) :
    supportIdeal F S slot ≠ 0 :=
  mul_ne_zero hF (Finset.prod_ne_zero_iff.mpr (fun i _ => (slot i).val.property.ne_zero))

theorem support_divisor (F : Id) (S H : Finset PrimeIdeal) (slot : ι → S)
    (hH : ∀ Q ∈ H, Q.val ∣ F) (Q : S)
    (hQ : augmented S H (marked S slot) Q=true) : Q.val.val ∣ supportIdeal F S slot := by
  simp only [augmented,Bool.or_eq_true,decide_eq_true_eq] at hQ
  rcases hQ with hQ | hQ
  · obtain ⟨i,hi⟩ := (marked_true S slot Q).mp hQ
    rw [← hi]
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun i => (slot i).val.val) (Finset.mem_univ i)) F
  · exact dvd_mul_of_dvd_left (hH Q.val hQ) _

theorem support_norm_bound (F : Id) (S : Finset PrimeIdeal) (slot : ι → S)
    (P : ι → ℝ) (Z B : ℝ) (hZ : 1 ≤ Z)
    (hF : (Ideal.absNorm F : ℝ) ≤ Z^B)
    (hP : ∀ i, (Ideal.absNorm (slot i).val.val : ℝ) ≤ 2*P i)
    (hV : (∏ i, 2*P i) ≤ Z^B) :
    (Ideal.absNorm (supportIdeal F S slot) : ℝ) ≤ Z^(2*B) := by
  simp only [supportIdeal,map_mul,map_prod,Nat.cast_mul,Nat.cast_prod]
  calc
    _ ≤ Z^B*(∏ i, 2*P i) := mul_le_mul hF
      (Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hP i))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)) (by positivity)
    _ ≤ Z^B*Z^B := mul_le_mul_of_nonneg_left hV (by positivity)
    _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans_le hZ)]; congr 1; ring

end
end Candidate.FourthPower.PrincipalMarkedMass
