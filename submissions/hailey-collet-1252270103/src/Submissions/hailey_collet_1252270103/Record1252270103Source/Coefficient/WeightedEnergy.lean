/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Finite absolute coefficient mass acts on the same completed positive norm.
The outside scalar may depend on the row and retain natural character zeros. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CoupledEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentRowNorm CenteredMomentRestrictedEnergy CanonicalQuadraticSieve
open CenteredMomentRestrictedWindow
local notation "O" => ActualEisensteinCubic.O

theorem norm_weighted_sum_sq {ι : Type*} (D : Finset ι) (w : ι→ℝ)
    (c f : ι→ℂ) (hw : ∀i∈D,0≤w i) (hc : ∀i∈D,‖c i‖≤w i) :
    ‖∑i∈D,c i*f i‖^2≤(∑i∈D,w i)*(∑i∈D,w i*‖f i‖^2) := by
  have hsum : ‖∑i∈D,c i*f i‖≤∑i∈D,w i*‖f i‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc i hi) (norm_nonneg _)
  apply (pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul D hw
    (fun i hi=>mul_nonneg (hw i hi) (sq_nonneg _))
  intro i hi
  apply le_of_eq
  ring

/-- This formulation needs only actual finite partial energies of each child;
it therefore applies before any choice of a row truncation. -/
theorem weighted_sum_energy_le {ι ρ : Type*} (D : Finset ι) (w E : ι→ℝ)
    (c f : ι→ρ→ℂ) (u : ρ→ℝ)
    (hw : ∀i∈D,0≤w i) (hu : ∀r,0≤u r)
    (hc : ∀i∈D,∀r,‖c i r‖≤w i)
    (hE : ∀i∈D,∀R : Finset ρ,∑r∈R,‖f i r‖^2*u r≤E i) :
    (∑'r,‖∑i∈D,c i r*f i r‖^2*u r)≤(∑i∈D,w i)*(∑i∈D,w i*E i) := by
  apply Real.tsum_le_of_sum_le (fun r=>mul_nonneg (sq_nonneg _) (hu r))
  intro R
  calc
    _ ≤ ∑r∈R,(∑i∈D,w i)*(∑i∈D,w i*(‖f i r‖^2*u r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have h := mul_le_mul_of_nonneg_right
        (norm_weighted_sum_sq D w (fun i=>c i r) (fun i=>f i r) hw (fun i hi=>hc i hi r)) (hu r)
      simpa only [Finset.sum_mul,mul_assoc] using h
    _ = (∑i∈D,w i)*(∑i∈D,w i*(∑r∈R,‖f i r‖^2*u r)) := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg hw)
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hE i hi R) (hw i hi)

theorem weighted_sum_energy_le_uniform {ι ρ : Type*} (D : Finset ι) (w : ι→ℝ)
    (E : ℝ) (c f : ι→ρ→ℂ) (u : ρ→ℝ)
    (hw : ∀i∈D,0≤w i) (hu : ∀r,0≤u r)
    (hc : ∀i∈D,∀r,‖c i r‖≤w i)
    (hE : ∀i∈D,∀R : Finset ρ,∑r∈R,‖f i r‖^2*u r≤E) :
    (∑'r,‖∑i∈D,c i r*f i r‖^2*u r)≤(∑i∈D,w i)^2*E := by
  apply (weighted_sum_energy_le D w (fun _=>E) c f u hw hu hc hE).trans_eq
  rw [←Finset.sum_mul]
  ring

/-- A divisor expansion is transferred through the literal smoothed positive
row energy. The common keep predicate and weight are unchanged; each child
retains its actual finite source and generator. -/
theorem restricted_energy_divisor_transfer {α ι : Type*} {β : ι→Type*}
    (keep : O→Prop) (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (b : α→ℂ)
    (D : Finset ι) (T : ∀i,Finset (β i)) (g : ∀i,β i→O)
    (hg : ∀i j,Supported (Ideal.span {g i j})) (d : ∀i,β i→ℂ)
    (c : ι→O→ℂ) (w : ι→ℝ) (hw : ∀i∈D,0≤w i)
    (hc : ∀i∈D,∀z,‖c i z‖≤w i)
    (hrow : ∀z,rowPolynomial S a b z=∑i∈D,c i z*rowPolynomial (T i) (g i) (d i) z)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    restrictedEnergy keep S a b W K≤
      (∑i∈D,w i)*(∑i∈D,w i*restrictedEnergy keep (T i) (g i) (d i) W K) := by
  let u := fun z : O=>if keep z then (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (z : O) : 0≤u z := by dsimp only [u];split_ifs;exact hW z;exact le_rfl
  have hs := restricted_hasSum_weighted keep S a ha b W K hK
  rw [←hs.tsum_eq]
  simp_rw [hrow]
  apply weighted_sum_energy_le D w
    (fun i=>restrictedEnergy keep (T i) (g i) (d i) W K) c
    (fun i z=>rowPolynomial (T i) (g i) (d i) z) u hw hu hc
  intro i hi R
  exact finite_weighted_le_restricted keep (T i) (g i) (hg i) (d i) W K hK hW R

end
end OAI.SevenEighths.Record1252270103Source

#print axioms OAI.SevenEighths.Record1252270103Source.norm_weighted_sum_sq
#print axioms OAI.SevenEighths.Record1252270103Source.restricted_energy_divisor_transfer
