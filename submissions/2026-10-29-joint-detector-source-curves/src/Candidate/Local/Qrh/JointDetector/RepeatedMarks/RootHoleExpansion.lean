/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! Whole-product Euler-hole expansion. Every deleted subproduct is retained;
no comparison of masked and unmasked prime sums in absolute value is used. -/
namespace Qrh.JointDetector.RepeatedMarks.RootHoleExpansion
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

/-- The exact original product identity, including all common-hole states. -/
theorem product_sub {ι : Type*} [DecidableEq ι] (slots : Finset ι) (Q D : ι → ℂ) :
    ∏ i ∈ slots, (Q i-D i) =
      ∑ s ∈ slots.powerset, (-1:ℂ)^s.card * (∏ i ∈ slots\s,Q i) * ∏ i ∈ s,D i :=
  Finset.prod_sub Q D slots

/-- Squared triangle/Cauchy with its exact finite number-of-terms cost. -/
theorem norm_sum_sq_le {κ : Type*} (s : Finset κ) (a : κ → ℂ) :
    ‖∑ k ∈ s,a k‖^2 ≤ (s.card:ℝ)*∑ k∈s,‖a k‖^2 := by
  have hn := norm_sum_le s a
  have hs : 0 ≤ ∑ k∈s,‖a k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun k => ‖a k‖)
  have hsq : ‖∑ k∈s,a k‖^2 ≤ (∑ k∈s,‖a k‖)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hsq.trans (by simpa using hc)

/-- A full moment follows by summing the exact expansion before applying
positivity. The error weights are common bounds for the deleted factors;
the survivor moments retain their unchanged original coefficients. -/
theorem moment_of_expansion {Row κ : Type*}
    (rows : Finset Row) (states : Finset κ) (masked : Row → ℂ)
    (term survivor : κ → Row → ℂ) (error bound : κ → ℝ)
    (hidentity : ∀ r∈rows,masked r=∑ k∈states,term k r)
    (herror : ∀ k∈states,0≤error k)
    (hterm : ∀ k∈states,∀ r∈rows,‖term k r‖^2≤error k*‖survivor k r‖^2)
    (hmoment : ∀ k∈states,∑ r∈rows,‖survivor k r‖^2≤bound k) :
    ∑ r∈rows,‖masked r‖^2 ≤ (states.card:ℝ)*∑ k∈states,error k*bound k := by
  calc
    _ ≤ ∑ r∈rows,(states.card:ℝ)*∑ k∈states,‖term k r‖^2 := by
      apply Finset.sum_le_sum
      intro r hr
      rw [hidentity r hr]
      exact norm_sum_sq_le states (fun k => term k r)
    _ = (states.card:ℝ)*∑ k∈states,∑ r∈rows,‖term k r‖^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (states.card:ℝ)*∑ k∈states,error k*bound k := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ ∑ r∈rows,error k*‖survivor k r‖^2 :=
          Finset.sum_le_sum fun r hr => hterm k hk r hr
        _ = error k*∑ r∈rows,‖survivor k r‖^2 := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmoment k hk) (herror k hk)

/-- A common pointwise hole error transports all surviving-subproduct moments.
Both finite powerset factors are paid explicitly; neither grows with scale. -/
theorem product_perturbation_moment {ι Row : Type*} [DecidableEq ι]
    (slots : Finset ι) (rows : Finset Row) (P : Row→ℂ) (Q D : ι→Row→ℂ)
    (E bound : ℝ) (hE : 1≤E)
    (hD : ∀i∈slots,∀u∈rows,‖D i u‖≤E)
    (hraw : ∀s∈slots.powerset,∑u∈rows,‖P u*(∏i∈slots\s,Q i u)‖^2≤bound) :
    ∑u∈rows,‖P u*(∏ i ∈ slots, (Q i u - D i u))‖^2 ≤
      (slots.powerset.card:ℝ)^2*E^(2*slots.card)*bound := by
  let survivor := fun s u=>P u*(∏i∈slots\s,Q i u)
  let term := fun s u=>(-1:ℂ)^s.card*survivor s u*(∏i∈s,D i u)
  have hE0 : 0≤E := zero_le_one.trans hE
  have hstate (s : Finset ι) (hs : s∈slots.powerset) :
      ∀u∈rows,‖term s u‖^2≤E^(2*slots.card)*‖survivor s u‖^2 := by
    intro u hu
    have hsub : s⊆slots := Finset.mem_powerset.mp hs
    have hp : ‖∏i∈s,D i u‖≤E^slots.card := by
      rw [norm_prod]
      calc
        (∏ i ∈ s, ‖D i u‖) ≤ (∏ _i ∈ s, E) :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i hi => hD i (hsub hi) u hu)
        _ = E^s.card := by simp
        _ ≤ E^slots.card := pow_le_pow_right₀ hE (Finset.card_le_card hsub)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hp 2
    have hnorm : ‖term s u‖^2=‖survivor s u‖^2*‖∏i∈s,D i u‖^2 := by
      simp [term,norm_mul,norm_pow,mul_pow]
    rw [hnorm]
    calc
      _ ≤ ‖survivor s u‖^2*(E^slots.card)^2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = _ := by rw [←pow_mul,Nat.mul_comm slots.card 2];ring
  have he := moment_of_expansion rows slots.powerset
    (fun u=>P u*(∏ i ∈ slots, (Q i u - D i u))) term survivor
    (fun _=>E^(2*slots.card)) (fun _=>bound)
    (fun u hu=>by
      rw [product_sub,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      dsimp [term,survivor]
      ring)
    (fun s hs=>pow_nonneg hE0 _) hstate hraw
  apply he.trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end
end Qrh.JointDetector.RepeatedMarks.RootHoleExpansion
