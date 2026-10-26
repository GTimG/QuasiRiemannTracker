/- Copyright (c) 2026 Sil. Apache-2.0.
Column sixth-power extraction for centrally normalized coefficients. The
coprimality mask depends on the row and is kept outside the common vector.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.SieveElementReference

set_option autoImplicit false
namespace Candidate.FourthPower.SieveCentralReference
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredExceptionalCount SexticSieve SixthDecomposition SieveDescent
open SieveReference SieveElementReference
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def reducedCoefficient (D : Id) (a : Id → ℂ) (J : Id) : ℂ := a (J*D^6)

def fiberSum (columns : Finset Id) (a : Id → ℂ) (D : Id) (x : O) : ℂ :=
  ∑ I ∈ rootFiber columns D, a I*idealRowHom x I

theorem column_mask (x : O) (J D : Id) (hD : Supported D) :
    idealRowHom x (J*D^6) = idealRowHom x J *
      (if IsCoprime D (Ideal.span {x}) then 1 else 0) := by
  rw [map_mul,map_pow,← idealRowHom_argument_pow _ 6 D hD,idealRowHom_sixth_mask _ D hD]

theorem fiber_identity (columns : Finset Id) (hc : ∀ I ∈ columns, Supported I)
    (a : Id → ℂ) (D : Id) (hD : Supported D) (x : O) :
    fiberSum columns a D x =
      (∑ J ∈ reducedRows columns D, reducedCoefficient D a J*idealRowHom x J)*
        (if IsCoprime D (Ideal.span {x}) then 1 else 0) := by
  rw [Finset.sum_mul,reducedRows,Finset.sum_image (remainder_injective_on_fiber columns hc D)]
  apply Finset.sum_congr rfl
  intro I hI
  obtain ⟨hI,hID⟩ := Finset.mem_filter.mp hI
  have he : sixthRemainder I*D^6 = I := by
    rw [← hID,sixth_normal_form I (hc I hI).1]
  rw [reducedCoefficient,he]
  have hv : idealRowHom x I = idealRowHom x (sixthRemainder I)*
      (if IsCoprime D (Ideal.span {x}) then 1 else 0) := by
    calc
      _ = idealRowHom x (sixthRemainder I*D^6) := congrArg (idealRowHom x) he.symm
      _ = _ := column_mask x _ D hD
  rw [hv]
  ring

theorem fiber_energy_le (rows : Finset O) (columns : Finset Id)
    (hc : ∀ I ∈ columns, Supported I) (a : Id → ℂ) (D : Id) (hD : Supported D) :
    (∑ x ∈ rows, ‖fiberSum columns a D x‖^2) ≤
      elementEnergy rows (reducedRows columns D) (reducedCoefficient D a) := by
  apply Finset.sum_le_sum
  intro x _
  rw [fiber_identity columns hc a D hD x]
  split_ifs <;> simp only [mul_one,mul_zero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)]
  · exact le_rfl
  · exact sq_nonneg _

theorem reduced_geometry (N : ℝ) (columns : Finset Id)
    (hc : ∀ I ∈ columns, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (D J : Id) (hJ : J ∈ reducedRows columns D) :
    Supported J ∧ PowerFree 6 J ∧ (Ideal.absNorm J : ℝ) ≤ N := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
  obtain ⟨hI,hID⟩ := Finset.mem_filter.mp hI
  have hs := (hc I hI).1
  have hq := norm_one_le (sixthQuotient_ne_zero I)
  have he := sixth_normal_form_norm I hs.1
  refine ⟨remainder_supported I hs,remainder_powerFree I,?_⟩
  have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hq (n := 6))
    (Nat.cast_nonneg (Ideal.absNorm (sixthRemainder I)) : (0 : ℝ) ≤ _)
  simpa only [mul_one,he] using hh.trans (by rw [he]; exact (hc I hI).2)

theorem reciprocal_mass (δ : ℝ) (hδ : 0 < δ) (N : ℝ) (hN : 0 < N)
    (F : Finset Id) (hF : ∀ J ∈ F, Supported J ∧ (Ideal.absNorm J : ℝ) ≤ N) :
    (∑ J ∈ F, (Ideal.absNorm J : ℝ)⁻¹) ≤ N^δ*rootMass (1+δ) := by
  have hJ (J : Id) (hJ : J ∈ F) :
      (Ideal.absNorm J : ℝ)⁻¹ ≤ N^δ*(Ideal.absNorm J : ℝ)^(-(1+δ)) := by
    have hn := norm_pos (hF J hJ).1.1
    have hp := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hn.le (hF J hJ).2 hδ.le)
      (Real.rpow_nonneg hn.le (-(1+δ)))
    rw [← Real.rpow_add hn] at hp
    convert hp using 1
    rw [show δ + -(1+δ) = -1 by ring,Real.rpow_neg_one]
  calc
    _ ≤ ∑ J ∈ F, N^δ*(Ideal.absNorm J : ℝ)^(-(1+δ)) := Finset.sum_le_sum hJ
    _ = N^δ*∑ J ∈ F, (Ideal.absNorm J : ℝ)^(-(1+δ)) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (finite_root_mass (1+δ) (by linarith) F (fun J hJ => (hF J hJ).1)) (by positivity)

theorem reduced_mass (δ : ℝ) (hδ : 0 < δ) (N A : ℝ) (hN : 0 < N) (hA : 0 ≤ A)
    (columns : Finset Id)
    (hc : ∀ I ∈ columns, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N)
    (a : Id → ℂ) (ha : ∀ I ∈ columns, ‖a I‖^2 ≤ A/(Ideal.absNorm I : ℝ))
    (D : Id) (hD : Supported D) :
    coefficientMass (reducedRows columns D) (reducedCoefficient D a) ≤
      (A/(Ideal.absNorm D : ℝ)^6)*(N^δ*rootMass (1+δ)) := by
  have hd := norm_pos hD.1
  have hterm (J : Id) (hJ : J ∈ reducedRows columns D) :
      ‖reducedCoefficient D a J‖^2 ≤
        (A/(Ideal.absNorm D : ℝ)^6)*(Ideal.absNorm J : ℝ)⁻¹ := by
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hI,hID⟩ := Finset.mem_filter.mp hI
    have he : sixthRemainder I*D^6 = I := by rw [← hID,sixth_normal_form I (hc I hI).1.1]
    have hn : (Ideal.absNorm I : ℝ) =
        (Ideal.absNorm (sixthRemainder I) : ℝ)*(Ideal.absNorm D : ℝ)^6 := by
      simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using
        congrArg (fun K : Id => (Ideal.absNorm K : ℝ)) he.symm
    rw [reducedCoefficient,he]
    apply (ha I hI).trans_eq
    rw [hn]
    ring
  calc
    _ ≤ ∑ J ∈ reducedRows columns D,
        (A/(Ideal.absNorm D : ℝ)^6)*(Ideal.absNorm J : ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (A/(Ideal.absNorm D : ℝ)^6)*
        ∑ J ∈ reducedRows columns D, (Ideal.absNorm J : ℝ)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reciprocal_mass δ hδ N hN _ (fun J hJ =>
        ⟨(reduced_geometry N columns hc D J hJ).1,(reduced_geometry N columns hc D J hJ).2.2⟩))
      (by positivity)

theorem root_cauchy (F : Finset Id) (hF : ∀ D ∈ F, Supported D) (f : Id → ℂ) :
    ‖∑ D ∈ F, f D‖^2 ≤
      (∑ D ∈ F, (Ideal.absNorm D : ℝ)^(-2 : ℝ))*
        (∑ D ∈ F, (Ideal.absNorm D : ℝ)^2*‖f D‖^2) := by
  have he : (∑ D ∈ F, ‖f D‖) =
      ∑ D ∈ F, (Ideal.absNorm D : ℝ)⁻¹*((Ideal.absNorm D : ℝ)*‖f D‖) := by
    apply Finset.sum_congr rfl
    intro D hD
    rw [← mul_assoc,inv_mul_cancel₀ (ne_of_gt (norm_pos (hF D hD).1)),one_mul]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le F f) 2
  rw [he] at hh
  apply hh.trans
  simpa only [mul_pow,Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_two,inv_pow] using
    Finset.sum_mul_sq_le_sq_mul_sq F
      (fun D => (Ideal.absNorm D : ℝ)⁻¹) (fun D => (Ideal.absNorm D : ℝ)*‖f D‖)

theorem summed_root_energy (rows : Finset O) (F : Finset Id)
    (hF : ∀ D ∈ F, Supported D) (f : Id → O → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ D ∈ F, (∑ x ∈ rows, ‖f D x‖^2) ≤ B/(Ideal.absNorm D : ℝ)^6) :
    (∑ x ∈ rows, ‖∑ D ∈ F, f D x‖^2) ≤ rootMass 2*rootMass 4*B := by
  have h₂ := rootMass_nonneg 2
  have h₄ := rootMass_nonneg 4
  have hsmall : (∑ D ∈ F, (Ideal.absNorm D : ℝ)^2 * ∑ x ∈ rows, ‖f D x‖^2) ≤
      rootMass 4*B := by
    calc
      _ ≤ ∑ D ∈ F, (Ideal.absNorm D : ℝ)^2*(B/(Ideal.absNorm D : ℝ)^6) :=
        Finset.sum_le_sum (fun D hD => mul_le_mul_of_nonneg_left (hf D hD) (sq_nonneg _))
      _ = (∑ D ∈ F, (Ideal.absNorm D : ℝ)^(-4 : ℝ))*B := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D hD
        have hn := ne_of_gt (norm_pos (hF D hD).1)
        rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_ofNat]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (finite_root_mass 4 (by norm_num) F hF) hB
  calc
    _ ≤ ∑ x ∈ rows, (∑ D ∈ F, (Ideal.absNorm D : ℝ)^(-2 : ℝ))*
        (∑ D ∈ F, (Ideal.absNorm D : ℝ)^2*‖f D x‖^2) :=
      Finset.sum_le_sum (fun x _ => root_cauchy F hF (fun D => f D x))
    _ = (∑ D ∈ F, (Ideal.absNorm D : ℝ)^(-2 : ℝ))*
        (∑ D ∈ F, (Ideal.absNorm D : ℝ)^2*∑ x ∈ rows, ‖f D x‖^2) := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
    _ ≤ rootMass 2*(rootMass 4*B) := mul_le_mul
      (finite_root_mass 2 (by norm_num) F hF) hsmall (by positivity) h₂
    _ = _ := by ring

/-- Both ideal power-free restrictions are gone. The remaining coefficient
hypothesis is the literal central normalization, with an explicit amplitude A. -/
theorem central_reference (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N A : ℝ, 1 ≤ M → 1 ≤ N → 0 ≤ A →
      ∀ (rows : Finset O) (columns : Finset Id),
      (∀ x ∈ rows, (Ideal.absNorm (Ideal.span {x}) : ℝ) ≤ M) →
      (∀ I ∈ columns, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ N) →
      ∀ a : Id → ℂ, (∀ I ∈ columns, ‖a I‖^2 ≤ A/(Ideal.absNorm I : ℝ)) →
        elementEnergy rows columns a ≤ C*(M*N)^ε*referenceMajorant M N*A := by
  obtain ⟨C,hC,hb⟩ := element_reference (ε/2) (by positivity)
  let K := (rootMass 2+1)*(rootMass 4+1)*C*(rootMass (1+ε/2)+1)
  have h₂ := rootMass_nonneg 2
  have h₄ := rootMass_nonneg 4
  have hδ := rootMass_nonneg (1+ε/2)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro M N A hM hN hA rows columns hr hc a ha
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hmaj := referenceMajorant_nonneg M N hM0.le hN0.le
  let F := columns.image sixthQuotient
  have hF : ∀ D ∈ F, Supported D := by
    intro D hD
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hD
    exact quotient_supported I (hc I hI).1
  let B := C*(M*N)^(ε/2)*referenceMajorant M N*A*(N^(ε/2)*rootMass (1+ε/2))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hf (D : Id) (hD : D ∈ F) :
      (∑ x ∈ rows, ‖fiberSum columns a D x‖^2) ≤ B/(Ideal.absNorm D : ℝ)^6 := by
    have hd := norm_pos (hF D hD).1
    calc
      _ ≤ elementEnergy rows (reducedRows columns D) (reducedCoefficient D a) :=
        fiber_energy_le rows columns (fun I hI => (hc I hI).1) a D (hF D hD)
      _ ≤ C*(M*N)^(ε/2)*referenceMajorant M N*
          coefficientMass (reducedRows columns D) (reducedCoefficient D a) :=
        hb M N hM hN rows _ hr (fun J hJ => reduced_geometry N columns hc D J hJ) _
      _ ≤ C*(M*N)^(ε/2)*referenceMajorant M N*
          ((A/(Ideal.absNorm D : ℝ)^6)*(N^(ε/2)*rootMass (1+ε/2))) :=
        mul_le_mul_of_nonneg_left (reduced_mass (ε/2) (by positivity) N A hN0 hA columns hc a ha D (hF D hD))
          (by positivity)
      _ = _ := by dsimp only [B]; ring
  have he : elementEnergy rows columns a = ∑ x ∈ rows, ‖∑ D ∈ F, fiberSum columns a D x‖^2 := by
    apply Finset.sum_congr rfl
    intro x _
    have heq := (Finset.sum_fiberwise_of_maps_to
      (fun I hI => Finset.mem_image.mpr ⟨I,hI,rfl⟩ : ∀ I ∈ columns, sixthQuotient I ∈ F)
      (fun I => a I*idealRowHom x I))
    exact congrArg (fun z : ℂ => ‖z‖^2) heq.symm
  have hp : (M*N)^(ε/2)*N^(ε/2) ≤ (M*N)^ε := by
    apply (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hN0.le (le_mul_of_one_le_left hN0.le hM) (by positivity : 0 ≤ ε/2))
      (by positivity : 0 ≤ (M*N)^(ε/2))).trans_eq
    rw [← Real.rpow_add (mul_pos hM0 hN0)]
    congr 1
    ring
  have hconstant : rootMass 2*rootMass 4*C*rootMass (1+ε/2) ≤ K :=
    mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul (le_add_of_nonneg_right zero_le_one)
        (le_add_of_nonneg_right zero_le_one) h₄ (by positivity)) hC.le)
      (le_add_of_nonneg_right zero_le_one) hδ (by positivity)
  rw [he]
  calc
    _ ≤ rootMass 2*rootMass 4*B := summed_root_energy rows F hF (fiberSum columns a) B hB hf
    _ = (rootMass 2*rootMass 4*C*rootMass (1+ε/2))*
        ((M*N)^(ε/2)*N^(ε/2))*referenceMajorant M N*A := by dsimp only [B]; ring
    _ ≤ K*(M*N)^ε*referenceMajorant M N*A := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul hconstant hp (by positivity) hK.le) hmaj) hA

end
end Candidate.FourthPower.SieveCentralReference
