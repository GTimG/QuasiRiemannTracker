/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Recur
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.ProfileWide

/-!
# Inverse.Restore.Sep — profile separation of the main column

The main column `mCol c n (childLogTest W h) U S I L a X` couples the tuple image `T` and the
column subset `A` through the profile `W(N A · N T / X)`. With the wide separation
(`Select/ProfileWide.profile_separation_wide`, ratio `r = N T / Hp ∈ [2^{-K}, 1]` on the images
with nonzero injective mark), it is an integral against ONE Schwartz `b` of

`twSlots(t+h) · col c n (childLogTest Φ (t+h)) S (X / Hp)`,

where `twSlots τ = ∑_T mark_I(T) (∏_T c) · logPhase τ (log (N T / Hp))` is the twisted injective
slot sum (**`mCol_sep`**, with integrability). The separated column is independent of the tuple.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped BigOperators SchwartzMap
open MeasureTheory
open OAI OAI.SevenEighths.InverseMoment

variable {σ ι : Type*} [DecidableEq ι]

/-- The twisted injective slot sum (images `T ⊆ U` with `|T| = |I|`). -/
def twSlots (c : ι → ℂ) (n : ι → ℝ) (U : Finset ι) (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (Hp τ : ℝ) : ℂ :=
  ∑ T ∈ U.powerset.filter (fun T => T.card = I.card),
    primeMarkInj I L a T * ((∏ i ∈ T, c i) *
      FourierBridge.logPhase τ (Real.log ((∏ i ∈ T, n i) / Hp)))

omit [DecidableEq ι] in
theorem phase_term_integrable (Φ : ℝ → ℂ) (b : 𝓢(ℝ, ℂ)) (α h x : ℝ) :
    Integrable (fun t : ℝ => b t * (FourierBridge.logPhase (t + h) α *
      childLogTest Φ (t + h) x)) volume := by
  apply schwartz_mul_bounded_integrable b _ _ ‖Φ x‖
  · intro t
    rw [norm_mul, childLogTest, norm_mul, FourierBridge.logPhase_norm,
      FourierBridge.logPhase_norm]
    simp
  · unfold childLogTest
    have h1 : Continuous (fun t : ℝ => FourierBridge.logPhase (t + h) α) :=
      (FourierBridge.logPhase_continuous_left α).comp (continuous_id.add continuous_const)
    have h2 : Continuous (fun t : ℝ => FourierBridge.logPhase (t + h) (Real.log x)) :=
      (FourierBridge.logPhase_continuous_left (Real.log x)).comp
        (continuous_id.add continuous_const)
    exact h1.mul (continuous_const.mul h2)

omit [DecidableEq ι] in
/-- Finite sums commute with the integral against `b` (termwise integrable). -/
theorem integral_mul_sum' {α : Type*} (s : Finset α) (b : ℝ → ℂ) (c : α → ℂ) (g : α → ℝ → ℂ)
    (hint : ∀ i ∈ s, Integrable (fun t => b t * g i t)) :
    Integrable (fun t => b t * ∑ i ∈ s, c i * g i t) ∧
      ∫ t, b t * ∑ i ∈ s, c i * g i t = ∑ i ∈ s, c i * ∫ t, b t * g i t := by
  have hfun : (fun t => b t * ∑ i ∈ s, c i * g i t) = fun t => ∑ i ∈ s, c i * (b t * g i t) := by
    funext t; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfun]
  refine ⟨integrable_finset_sum s (fun i hi => (hint i hi).const_mul (c i)), ?_⟩
  rw [integral_finset_sum s (fun i hi => (hint i hi).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul (c i) _

/-- **Profile separation of the main column.** -/
theorem mCol_sep (c : ι → ℂ) (n : ι → ℝ) (hn : ∀ i, 0 < n i) (W Φ : ℝ → ℂ) (b : 𝓢(ℝ, ℂ))
    (K : ℕ)
    (hsep : ∀ r x hh : ℝ, 1 ≤ 2^K * r → r ≤ 1 → 0 < x →
      W (r * x) * FourierBridge.logPhase hh (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + hh) (Real.log r) * childLogTest Φ (t + hh) x * b t)
    (h : ℝ) (U S : Finset ι) (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (Hp X : ℝ) (hHp : 0 < Hp) (hX : 0 < X)
    (hratio : ∀ T ⊆ U, T.card = I.card → primeMarkInj I L a T ≠ 0 →
      1 ≤ 2^K * ((∏ i ∈ T, n i) / Hp) ∧ (∏ i ∈ T, n i) / Hp ≤ 1) :
    Integrable (fun t => b t * (twSlots c n U I L a Hp (t + h) *
      col c n (childLogTest Φ (t + h)) S (X / Hp))) ∧
    mCol c n (childLogTest W h) U S I L a X =
      ∫ t, b t * (twSlots c n U I L a Hp (t + h) *
        col c n (childLogTest Φ (t + h)) S (X / Hp)) := by
  set Ts := U.powerset.filter (fun T => T.card = I.card) with hTs
  set P := Ts ×ˢ S.powerset with hP
  -- coefficients and phases of the product expansion
  let cf : Finset ι × Finset ι → ℂ := fun q =>
    primeMarkInj I L a q.1 * (∏ i ∈ q.1, c i) * (∏ i ∈ q.2, c i)
  let g : Finset ι × Finset ι → ℝ → ℂ := fun q t =>
    FourierBridge.logPhase (t + h) (Real.log ((∏ i ∈ q.1, n i) / Hp)) *
      childLogTest Φ (t + h) ((∏ i ∈ q.2, n i) / (X / Hp))
  have hexp : ∀ t, twSlots c n U I L a Hp (t + h) * col c n (childLogTest Φ (t + h)) S (X / Hp) =
      ∑ q ∈ P, cf q * g q t := by
    intro t
    unfold twSlots col
    rw [Finset.sum_mul_sum, hP, Finset.sum_product]
    apply Finset.sum_congr rfl; intro T _
    apply Finset.sum_congr rfl; intro A _
    simp only [cf, g, childLogTest]
    ring
  have hint : ∀ q ∈ P, Integrable (fun t => b t * g q t) := by
    intro q _
    exact phase_term_integrable Φ b _ h _
  obtain ⟨hI, hval⟩ := integral_mul_sum' P b cf g hint
  refine ⟨?_, ?_⟩
  · simpa only [hexp] using hI
  simp only [hexp]
  rw [hval]
  unfold mCol col
  rw [hP, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro T hT
  have hTm := Finset.mem_filter.mp hT
  have hTU : T ⊆ U := Finset.mem_powerset.mp hTm.1
  by_cases hm : primeMarkInj I L a T = 0
  · simp only [cf, hm, zero_mul]
    simp
  obtain ⟨hr1, hr2⟩ := hratio T hTU hTm.2 hm
  have hNT : 0 < ∏ i ∈ T, n i := Finset.prod_pos (fun i _ => hn i)
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  have hNA : 0 < ∏ i ∈ A, n i := Finset.prod_pos (fun i _ => hn i)
  have key := hsep ((∏ i ∈ T, n i) / Hp) ((∏ i ∈ A, n i) / (X / Hp)) h hr1 hr2
    (by positivity)
  have hx : (∏ i ∈ T, n i) / Hp * ((∏ i ∈ A, n i) / (X / Hp)) =
      (∏ i ∈ A, n i) / (X / ∏ i ∈ T, n i) := by
    field_simp
  rw [hx] at key
  have hieq : (∫ t : ℝ, FourierBridge.logPhase (t + h) (Real.log ((∏ i ∈ T, n i) / Hp)) *
      childLogTest Φ (t + h) ((∏ i ∈ A, n i) / (X / Hp)) * b t) = ∫ t, b t * g (T, A) t := by
    apply integral_congr_ae
    filter_upwards with t
    simp only [g]
    ring
  simp only [cf]
  rw [childLogTest, key, hieq]
  ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mCol_sep
