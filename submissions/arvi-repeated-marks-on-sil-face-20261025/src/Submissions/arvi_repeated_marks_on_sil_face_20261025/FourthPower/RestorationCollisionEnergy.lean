/- Copyright (c) 2026 Sil. Apache-2.0.
Restore the full original natural-slot product from its injective singleton
families. Genuine repeated blocks carry all their original half-powers.
The input estimates below are explicitly named transfer hypotheses.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RestorationFamily

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace Candidate.FourthPower.RestorationCollisionEnergy
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.SevenEighths.Record12518109GainDeletion
open KernelCollisionEnergy KernelCollisionMass KernelNaturalSlots
open KernelMarkedRows KernelRowProfiles KernelRowPools RestorationFamily
local notation "Id" => Ideal ActualEisensteinCubic.O
variable {α : Type*} [Fintype α]

theorem prime_pool_energy (δ B X : ℝ) (hδ : 0 < δ) (hX : 0 < X)
    (S : Finset PrimeIdeal)
    (hS : ∀ P ∈ S, Supported P.val ∧ (Ideal.absNorm P.val : ℝ) ≤ X) :
    (∑ P : S, (centralWeight B P.val.val)^2) ≤
      B^2*X^δ*SieveDescent.rootMass (1+δ) := by
  have hs : ∀ I ∈ primeValues S, Supported I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
    intro I hI
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
    exact hS P hP
  have he : (∑ P : S, (centralWeight B P.val.val)^2) =
      ∑ I : primeValues S, (centralWeight B I.val)^2 := by
    rw [Finset.sum_coe_sort S (fun P : PrimeIdeal => (centralWeight B P.val)^2),
      Finset.sum_coe_sort (primeValues S) (fun I : Id => (centralWeight B I)^2)]
    unfold primeValues
    rw [Finset.sum_image]
    intro P _ Q _ h
    exact Subtype.ext h
  rw [he]
  exact central_pool_energy δ B X hδ hX (primeValues S) hs

def collisionBeta (r : Setoid α) (S : Finset PrimeIdeal)
    (t : {q // ¬singletonBlock r q} → S) (β : α → Id → ℂ) :
    {q // singletonBlock r q} → Id → ℂ :=
  maskedBeta (fun q => β (singletonRepresentative r q))
    (fun _ I => ∀ j : {q // ¬singletonBlock r q}, I ≠ (t j).val.val)

theorem collision_coefficient (r : Setoid α) (S : Finset PrimeIdeal)
    (t : {q // ¬singletonBlock r q} → S) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (q : {q // singletonBlock r q}) (p : S) :
    naturalCoefficients χ S (fun q : {q // singletonBlock r q} => pool (singletonRepresentative r q))
      (collisionBeta r S t β) (fun q => P (singletonRepresentative r q)) q p =
      if ∀ j : {q // ¬singletonBlock r q}, p ≠ t j then
        naturalCoefficients χ S pool β P (singletonRepresentative r q) p else 0 := by
  unfold naturalCoefficients collisionBeta maskedBeta
  rw [slotTerm_mask]
  dsimp only
  have he : (∀ j : {q // ¬singletonBlock r q}, p.val.val ≠ (t j).val.val) ↔
      (∀ j : {q // ¬singletonBlock r q}, p ≠ t j) := by
    constructor
    · intro h j hj
      exact h j (congrArg (fun Q : S => Q.val.val) hj)
    · intro h j hj
      exact h j (Subtype.ext (Subtype.ext hj))
  simp only [he]

theorem collision_row (r : Setoid α) (S : Finset PrimeIdeal)
    (t : {q // ¬singletonBlock r q} → S) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    row true S χ (fun q : {q // singletonBlock r q} => pool (singletonRepresentative r q))
      (collisionBeta r S t β) (fun q => P (singletonRepresentative r q)) W₁ W₂ b X₁ X₂ =
      normalizedRow χ (supportedRectangle S b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂ *
        injectiveTuplePolynomial (fun q : {q // singletonBlock r q} => fun p : S =>
          if ∀ j : {q // ¬singletonBlock r q}, p ≠ t j then
            naturalCoefficients χ S pool β P (singletonRepresentative r q) p else 0) := by
  rw [unrestricted_row]
  congr 1
  apply congrArg injectiveTuplePolynomial
  funext q p
  exact collision_coefficient r S t χ pool β P q p

/-- Only a subpower cost is paid for all collision patterns and assignments.
The entire remaining injective polynomial is estimated together, with
common masked coefficients. There is no factor for the size of the prime pool. -/
theorem collision_energy_exact (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Ideal.absNorm Q.val : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, pool i ⊆ primeValues S) → (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ), 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ (r : Setoid α) (t : {q // ¬singletonBlock r q} → S),
        (∑ u ∈ rows, ρ u*‖row true S (χ u)
          (fun q : {q // singletonBlock r q} => pool (singletonRepresentative r q))
          (collisionBeta r S t β) (fun q => P (singletonRepresentative r q)) W₁ W₂ b X₁ X₂‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤ C*X^ε*E := by
  let k := Fintype.card α
  let δ := ε/(2*(k : ℝ)+1)
  have hd : 0 < 2*(k : ℝ)+1 := by positivity
  have hδ : 0 < δ := div_pos hε hd
  let Q := SieveDescent.rootMass (1+δ)+1
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact le_add_of_nonneg_left (SieveDescent.rootMass_nonneg _)
  let C := ((2 : ℝ)^(k*k)*(Q*(2*B)^k)^k)^2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro X hX S hS Row rows ρ χ pool β P hpool hP hp hβ W₁ W₂ b X₁ X₂ E hE hρ hroot
  have hX0 := zero_lt_one.trans_le hX
  have hB0 := zero_le_one.trans hB
  let L := Q*X^δ
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hQ (Real.one_le_rpow hX hδ.le)
  let a (u : Row) (i : α) (p : S) := naturalCoefficients (χ u) S pool β P i p
  let D (u : Row) := normalizedRow (χ u) (supportedRectangle S b X₁ X₂) (fun _ => 1) W₁ W₂ X₁ X₂
  have he (i : α) : (∑ p : S, (centralWeight (2*B) p.val.val)^2) ≤ L*(2*B)^2 := by
    calc
      _ ≤ (2*B)^2*X^δ*SieveDescent.rootMass (1+δ) := prime_pool_energy δ (2*B) X hδ hX0 S hS
      _ ≤ (2*B)^2*X^δ*Q := mul_le_mul_of_nonneg_left
        (by dsimp [Q]; linarith) (by positivity)
      _ = _ := by dsimp [L]; ring
  have hsingle (r : Setoid α) (t : {q // ¬singletonBlock r q} → S) :
      (∑ u ∈ rows, ρ u*‖D u*injectiveTuplePolynomial
        (fun q : {q // singletonBlock r q} => fun p : S =>
          if ∀ j : {q // ¬singletonBlock r q}, p ≠ t j then
            a u (singletonRepresentative r q) p else 0)‖^2) ≤ E := by
    have hh := hroot r t
    apply (le_of_eq ?_).trans hh
    apply Finset.sum_congr rfl
    intro u _
    rw [collision_row]
  have hb2 : 1 ≤ 2*B := by linarith
  have hv0 (i : α) (p : S) : 0 ≤ centralWeight (2*B) p.val.val :=
    centralWeight_nonneg (2*B) (by positivity) p.val.val
  have hv (i : α) (p : S) : centralWeight (2*B) p.val.val ≤ 2*B :=
    centralWeight_le (2*B) (by positivity) p.val.val (hS p.val p.property).1
  have ha (u : Row) (_hu : u ∈ rows) (i : α) (p : S) :
      ‖a u i p‖ ≤ centralWeight (2*B) p.val.val :=
    slotTerm_bound (χ u) (pool i) (β i) (P i) B (hP i) hB0 (hp i) (hβ i) p.val.val
  have hh : (∑ u ∈ rows, ρ u*‖D u*(∏ i, ∑ p, a u i p)‖^2) ≤
      ((2 : ℝ)^(k*k)*(L*(2*B)^k)^k)^2*E := by
    exact weighted_product_energy_of_singletons (Row:=Row) (I:=α) (A:=S) rows ρ a
      (fun _i : α => fun p : S => centralWeight (2*B) p.val.val) D (2*B) L E
      hρ hb2 hL hE hv0 hv he ha k (le_refl _) (by
        intro r t
        apply (le_of_eq ?_).trans (hsingle r t)
        apply Finset.sum_congr rfl
        intro u _
        apply congrArg (fun z : ℂ => ρ u*‖D u*z‖^2)
        unfold injectiveTuplePolynomial
        apply Finset.sum_congr (by ext; simp)
        intro s _
        split_ifs
        · apply Finset.prod_congr (by ext; simp)
          intro q _
          dsimp only
          by_cases hc : ∀ j : {q // ¬singletonBlock r q}, s q ≠ t j
          · rw [ite_eq_left hc,ite_eq_left hc]
          · rw [ite_eq_right hc,ite_eq_right hc]
        · rfl)
  have hcost : ((2 : ℝ)^(k*k)*(L*(2*B)^k)^k)^2 = C*X^(δ*(k : ℝ)*2) := by
    dsimp [L,C]
    rw [show Q*X^δ*(2*B)^k = (Q*(2*B)^k)*X^δ by ring,mul_pow]
    rw [mul_pow,mul_pow]
    rw [← Real.rpow_natCast (X^δ) k,← Real.rpow_mul hX0.le,
      ← Real.rpow_natCast (X^(δ*(k : ℝ))) 2,← Real.rpow_mul hX0.le]
    ring
  have hexp : δ*(k : ℝ)*2 ≤ ε := by
    have heq := div_mul_cancel₀ ε (ne_of_gt hd)
    change δ*(2*(k : ℝ)+1)=ε at heq
    nlinarith
  rw [hcost] at hh
  have hlast := hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hexp) hC.le) hE)
  simp_rw [fullRow_eq S _ pool β P W₁ W₂ b X₁ X₂ hpool]
  exact hlast

/-- Compatibility corollary with a stronger input. -/
theorem collision_energy (B ε : ℝ) (hB : 1 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ S : Finset PrimeIdeal,
      (∀ Q ∈ S, Supported Q.val ∧ (Ideal.absNorm Q.val : ℝ) ≤ X) →
      ∀ {Row : Type*} (rows : Finset Row) (ρ : Row → ℝ) (χ : Row → Character)
        (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ),
      (∀ i, pool i ⊆ primeValues S) → (∀ i, 0 < P i) →
      (∀ i I, I ∈ pool i → Supported I ∧ (Ideal.absNorm I : ℝ) ≤ 2*P i) →
      (∀ i I, I ∈ pool i → ‖β i I‖ ≤ B) →
      ∀ (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ E : ℝ), 0 ≤ E →
      (∀ u ∈ rows, 0 ≤ ρ u) →
      (∀ (r : Setoid α) (β' : {q // singletonBlock r q} → Id → ℂ),
        (∀ q I, I ∈ pool (singletonRepresentative r q) → ‖β' q I‖ ≤ B) →
        (∑ u ∈ rows, ρ u*‖row true S (χ u)
          (fun q : {q // singletonBlock r q} => pool (singletonRepresentative r q))
          β' (fun q => P (singletonRepresentative r q)) W₁ W₂ b X₁ X₂‖^2) ≤ E) →
      (∑ u ∈ rows, ρ u*‖fullRow S (χ u) pool β P W₁ W₂ b X₁ X₂‖^2) ≤ C*X^ε*E := by
  obtain ⟨C,hC,hbound⟩ := collision_energy_exact (α:=α) B ε hB hε
  refine ⟨C,hC,?_⟩
  intro X hX S hS Row rows ρ χ pool β P hpool hP hp hβ W₁ W₂ b X₁ X₂ E hE hρ hroot
  apply hbound X hX S hS rows ρ χ pool β P hpool hP hp hβ W₁ W₂ b X₁ X₂ E hE hρ
  intro r t
  exact hroot r (collisionBeta r S t β)
    (maskedBeta_bound _ _ _ B (zero_le_one.trans hB) (fun q=>hβ (singletonRepresentative r q)))

end
end Candidate.FourthPower.RestorationCollisionEnergy
