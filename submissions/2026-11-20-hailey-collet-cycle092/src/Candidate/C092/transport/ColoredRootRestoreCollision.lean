/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
The native collision proof with an arbitrary physical ordinary row factor.
All original central weights and natural marked coefficients are retained. -/
import Candidate.C092.transport.ColoredRootRestoreSigned
import Submissions.sil_density_split_20261026.CubeFree.FP.RestorationCollisionEnergy
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open OAI.SevenEighths.Record12518109GainDeletion
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP
open KernelCollisionEnergy KernelCollisionMass KernelNaturalSlots
open KernelMarkedRows KernelRowProfiles KernelRowPools RestorationFamily RestorationCollisionEnergy
local notation "Id" => Ideal HeckeFamily.O
variable {α : Type*} [Fintype α]

theorem collision_product_energy (B ε : ℝ) (hB : 1≤B) (hε : 0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ X:ℝ,1≤X → ∀ S:Finset PrimeIdeal,
      (∀ Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ)≤X) →
      ∀ {Row:Type*} (rows:Finset Row) (ρ:Row→ℝ) (χ:Row→Character)
        (pool:α→Finset Id) (β:α→Id→ℂ) (P:α→ℝ),
      (∀ i,pool i⊆primeValues S) → (∀ i,0<P i) →
      (∀ i I,I∈pool i → Supported I ∧ (I.absNorm:ℝ)≤2*P i) →
      (∀ i I,I∈pool i → ‖β i I‖≤B) →
      ∀ (D:Row→ℂ) (E:ℝ),0≤E → (∀ u∈rows,0≤ρ u) →
      (∀ (r:Setoid α) (t:{q // ¬singletonBlock r q}→S),
        (∑ u∈rows,ρ u*‖D u*injectiveTuplePolynomial
          (fun q:{q // singletonBlock r q}=>fun p:S=>
            if ∀ j:{q // ¬singletonBlock r q},p≠t j then
              naturalCoefficients (χ u) S pool β P (singletonRepresentative r q) p else 0)‖^2)≤E) →
      (∑ u∈rows,ρ u*‖D u*∏ i,CenteredMomentCommonMaskExpansion.naturalSlot
        (χ u) (pool i) (β i) (P i)‖^2)≤C*X^ε*E := by
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
  intro X hX S hS Row rows ρ χ pool β P hpool hP hp hβ D E hE hρ hroot
  have hX0 := zero_lt_one.trans_le hX
  have hB0 := zero_le_one.trans hB
  let L := Q*X^δ
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le hQ (Real.one_le_rpow hX hδ.le)
  let a (u : Row) (i : α) (p : S) := naturalCoefficients (χ u) S pool β P i p
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
    exact hroot r t
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
  dsimp only [a] at hlast
  simp only [naturalCoefficients] at hlast
  simp_rw [sum_prime_slot S _ _ _ _ (hpool _)] at hlast
  exact hlast


#print axioms collision_product_energy
end
end QRH.Cycle092.ColoredRootRestore
