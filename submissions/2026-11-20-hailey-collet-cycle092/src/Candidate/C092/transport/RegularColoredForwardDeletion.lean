/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual common-puncture Möbius expansion for two ordinary characters and
one mark character. The original uniform divisor majorant is unchanged. -/
import Candidate.C092.transport.RegularColoredForwardEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open Candidate.FourthPower
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [DecidableEq α]

def pairSignedCoefficient (χ₁ χ₂ χ : Character) (R D₁ D₂ : Finset Id)
    (J : Finset α) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ) : ℂ :=
  plainCoefficient χ₁ D₁ * plainCoefficient χ₂ D₂ * (-1 : ℂ)^J.card *
    ∏ i ∈ J, naturalSlot χ (pool i ∩ R) (β i) (P i)

/-- Exact commutation of a genuine common puncture with one fixed ordinary
color, including all ramified zeros. -/
theorem product_exclude_idealCoeff (χ ψ : Character) (R : Finset Id)
    (hR : ∀ I ∈ R, Prime I) (I : Id) :
    idealCoeff ((χ.excludePrimes R hR).product ψ) I =
      idealCoeff ((χ.product ψ).excludePrimes R hR) I := by
  simp only [idealCoeff_product,idealCoeff_excludePrimes]
  split_ifs <;> simp only [zero_mul]

/-- The forward ordinary polynomial after exact mask absorption is precisely
the independently colored punctured ordinary factor opened below. -/
theorem product_exclude_polynomial (χ ψ : Character) (R : Finset Id)
    (hR : ∀ I ∈ R, Prime I) (W : ℝ → ℂ) (X σ t : ℝ) :
    HeckeDyadic.polynomial ((χ.excludePrimes R hR).product ψ) false W X σ t =
      HeckeDyadic.polynomial ((χ.product ψ).excludePrimes R hR) false W X σ t := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,product_exclude_idealCoeff]

/-- Open the whole common puncture before norms. Each ordinary divisor
carries its own true character coefficient; every subset of removed marks
retains the original mark character and original coefficients. -/
theorem simultaneous_pair_deletion (χ₁ χ₂ χ : Character) (R : Finset Id)
    (hR : ∀ I ∈ R, Prime I) (W₁ W₂ : 𝓢(ℝ,ℂ)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (F : Finset α)
    (pool : α → Finset Id) (hp : ∀ i ∈ F, ∀ I ∈ pool i, Prime I)
    (β : α → Id → ℂ) (P : α → ℝ) :
    HeckeDyadic.polynomial (χ₁.excludePrimes R hR) false W₁ X₁ 0 0 *
      HeckeDyadic.polynomial (χ₂.excludePrimes R hR) false W₂ X₂ 0 0 *
      (∏ i ∈ F, naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i)) =
    ∑ D₁ ∈ R.powerset, ∑ D₂ ∈ R.powerset, ∑ J ∈ F.powerset,
      pairSignedCoefficient χ₁ χ₂ χ R D₁ D₂ J pool β P *
        (HeckeDyadic.polynomial χ₁ false W₁ (X₁/(Ideal.absNorm (∏ I ∈ D₁, I) : ℝ)) 0 0 *
         HeckeDyadic.polynomial χ₂ false W₂ (X₂/(Ideal.absNorm (∏ I ∈ D₂, I) : ℝ)) 0 0 *
         ∏ i ∈ F \ J, naturalSlot χ (pool i) (β i) (P i)) := by
  have hs : (∏ i ∈ F, naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i)) =
      ∑ J ∈ F.powerset, (-1 : ℂ)^J.card * (∏ i ∈ J, naturalSlot χ (pool i ∩ R) (β i) (P i)) *
        (∏ i ∈ F \ J, naturalSlot χ (pool i) (β i) (P i)) := by
    exact (Finset.prod_congr rfl (fun i hi => naturalSlot_delete χ R hR (pool i) (hp i hi) (β i) (P i))).trans
      (prod_sub_expansion F (fun i => naturalSlot χ (pool i) (β i) (P i))
        (fun i => naturalSlot χ (pool i ∩ R) (β i) (P i)))
  rw [normalized_finite_deletion_moebius χ₁ R hR W₁ (schwartz_decayTwo W₁) X₁ hX₁,
    normalized_finite_deletion_moebius χ₂ R hR W₂ (schwartz_decayTwo W₂) X₂ hX₂,hs]
  rw [Finset.sum_mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [pairSignedCoefficient,plainCoefficient]
  ring

/-- The independent ordinary coefficients obey the very same literal
uniform majorant, retaining the full harmonic divisor costs. -/
theorem pairSignedCoefficient_uniform (χ₁ χ₂ χ : Character) (R : Finset Id)
    (hR : ∀ I ∈ R, Prime I) (D₁ D₂ : Finset Id) (hD₁ : D₁ ⊆ R) (hD₂ : D₂ ⊆ R)
    (J : Finset α) (pool : α → Finset Id) (β : α → Id → ℂ) (P b M : α → ℝ)
    (hp : ∀ i ∈ J, ∀ I ∈ pool i, Prime I) (hP : ∀ i ∈ J, 0 < P i)
    (hM : ∀ i ∈ J, 0 ≤ M i) (hβ : ∀ i ∈ J, ∀ I ∈ pool i, ‖β i I‖ ≤ M i)
    (hs : ∀ i ∈ J, ∀ I ∈ pool i, β i I ≠ 0 → (I.absNorm : ℝ) ≤ b i * P i) :
    ‖pairSignedCoefficient χ₁ χ₂ χ R D₁ D₂ J pool β P‖ ≤ uniformMajorant R D₁ D₂ J b M := by
  have hn : ‖pairSignedCoefficient χ₁ χ₂ χ R D₁ D₂ J pool β P‖ ≤
      coefficientMajorant R D₁ D₂ J pool β P := by
    simp only [pairSignedCoefficient,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_prod]
    apply mul_le_mul
    · exact mul_le_mul (plainCoefficient_norm χ₁ D₁ (fun I hi => hR I (hD₁ hi)))
        (plainCoefficient_norm χ₂ D₂ (fun I hi => hR I (hD₂ hi))) (norm_nonneg _) (weight_nonneg _)
    · exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => naturalSlot_norm χ R (pool i) (β i) (P i))
    · positivity
    · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)
  apply hn.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_le_prod₀ (fun i _ => slotMass_nonneg _ _ _ _)
    (fun i hi => slotMass_bound R (pool i) (hp i hi) (β i) (P i) (b i) (M i)
      (hP i hi) (hM i hi) (hβ i hi) (hs i hi))

/-- Actual two-ordinary-character common-puncture estimate in an arbitrary
positive finite row norm. The constant precedes both ordinary characters,
mark characters, their profiles, finite rows and the full common puncture. -/
theorem finite_pair_shared_energy (F : Finset α) (b M : α → ℝ)
    (hM : ∀ j ∈ F, 0 ≤ M j) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ),
      (∀ u ∈ rows, 0 ≤ ρ u) →
      ∀ (R : Finset Id) (hR : ∀ I ∈ R, Prime I) (χ₁ χ₂ χ : Row → Character)
        (W₁ W₂ : Row → 𝓢(ℝ,ℂ)) (X₁ X₂ : Row → ℝ)
        (pool : Row → α → Finset Id) (β : Row → α → Id → ℂ) (P : Row → α → ℝ),
      (∀ u, 0 < X₁ u) → (∀ u, 0 < X₂ u) →
      (∀ u j, j ∈ F → ∀ I ∈ pool u j, Prime I) → (∀ u j, j ∈ F → 0 < P u j) →
      (∀ u j, j ∈ F → ∀ I ∈ pool u j, ‖β u j I‖ ≤ M j) →
      (∀ u j, j ∈ F → ∀ I ∈ pool u j, β u j I ≠ 0 → (I.absNorm : ℝ) ≤ b j * P u j) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ D₁ ∈ R.powerset, ∀ D₂ ∈ R.powerset, ∀ J ∈ F.powerset,
        (∑ u ∈ rows, ρ u * ‖HeckeDyadic.polynomial (χ₁ u) false (W₁ u)
            (X₁ u/(Ideal.absNorm (∏ I ∈ D₁, I) : ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ₂ u) false (W₂ u)
            (X₂ u/(Ideal.absNorm (∏ I ∈ D₂, I) : ℝ)) 0 0 *
          ∏ j ∈ F \ J, naturalSlot (χ u) (pool u j) (β u j) (P u j)‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u * ‖HeckeDyadic.polynomial ((χ₁ u).excludePrimes R hR) false (W₁ u) (X₁ u) 0 0 *
        HeckeDyadic.polynomial ((χ₂ u).excludePrimes R hR) false (W₂ u) (X₂ u) 0 0 *
        ∏ j ∈ F, naturalSlot ((χ u).excludePrimes R hR) (pool u j) (β u j) (P u j)‖^2) ≤
        C*(Ideal.absNorm (∏ I ∈ R, I) : ℝ)^ε*E := by
  obtain ⟨C,hC,hmass⟩ := uniform_mass_subpower F b M hM (ε/2) (half_pos hε)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro Row rows ρ hρ R hR χ₁ χ₂ χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE he
  let κ := {D : Finset Id // D ∈ R.powerset} × {D : Finset Id // D ∈ R.powerset} ×
    {J : Finset α // J ∈ F.powerset}
  let a (u : Row) (j : κ) := pairSignedCoefficient (χ₁ u) (χ₂ u) (χ u) R
    j.1.val j.2.1.val j.2.2.val (pool u) (β u) (P u)
  let f (j : κ) (u : Row) := HeckeDyadic.polynomial (χ₁ u) false (W₁ u)
    (X₁ u/(Ideal.absNorm (∏ I ∈ j.1.val, I) : ℝ)) 0 0 *
    HeckeDyadic.polynomial (χ₂ u) false (W₂ u)
    (X₂ u/(Ideal.absNorm (∏ I ∈ j.2.1.val, I) : ℝ)) 0 0 *
    ∏ k ∈ F \ j.2.2.val, naturalSlot (χ u) (pool u k) (β u k) (P u k)
  let m (j : κ) := uniformMajorant R j.1.val j.2.1.val j.2.2.val b M
  have hm (j : κ) : 0 ≤ m j := uniformMajorant_nonneg _ _ _ _ _ _
    (fun k hk => hM k (Finset.mem_powerset.mp j.2.2.property hk))
  have ha (u : Row) (j : κ) : ‖a u j‖ ≤ m j :=
    pairSignedCoefficient_uniform (χ₁ u) (χ₂ u) (χ u) R hR _ _
      (Finset.mem_powerset.mp j.1.property) (Finset.mem_powerset.mp j.2.1.property)
      _ (pool u) (β u) (P u) b M
      (fun k hk => hp u k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk => hP u k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk => hM k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk => hβ u k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk => hs u k (Finset.mem_powerset.mp j.2.2.property hk))
  have hh := KernelCollisionEnergy.weighted_physical_energy rows ρ
    (fun j u => a u j * f j u) f m E hρ hm
    (fun j u _ => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (ha u j) (norm_nonneg _))
    (fun j => he j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property)
  have hid (u : Row) : (∑ j : κ, a u j * f j u) =
      HeckeDyadic.polynomial ((χ₁ u).excludePrimes R hR) false (W₁ u) (X₁ u) 0 0 *
      HeckeDyadic.polynomial ((χ₂ u).excludePrimes R hR) false (W₂ u) (X₂ u) 0 0 *
      ∏ j ∈ F, naturalSlot ((χ u).excludePrimes R hR) (pool u j) (β u j) (P u j) := by
    exact (triple_sum R.powerset R.powerset F.powerset _).trans
      (simultaneous_pair_deletion (χ₁ u) (χ₂ u) (χ u) R hR (W₁ u) (W₂ u) (X₁ u) (X₂ u)
        (hX₁ u) (hX₂ u) F (pool u) (hp u) (β u) (P u)).symm
  have hmass' : (∑ j : κ, m j) ≤ C*(Ideal.absNorm (∏ I ∈ R, I) : ℝ)^(ε/2) :=
    (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J => uniformMajorant R D₁ D₂ J b M)).trans_le (hmass R hR)
  have hr : ((Ideal.absNorm (∏ I ∈ R, I) : ℝ)^(ε/2))^2 =
      (Ideal.absNorm (∏ I ∈ R, I) : ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hid] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => hm j)) hmass' 2) hE).trans_eq
      (by rw [mul_pow,hr]))

#print axioms product_exclude_idealCoeff
#print axioms product_exclude_polynomial
#print axioms simultaneous_pair_deletion
#print axioms pairSignedCoefficient_uniform
#print axioms finite_pair_shared_energy
end
end QRH.Cycle092.RegularColoredForward
