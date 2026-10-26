/- Copyright (c) 2026 Sil. Apache-2.0.
Positive fourth-power pushforward. Zero frequency is explicitly excluded. -/
import Candidate.FourthPower.GaussTransfer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.FiniteOperator

set_option autoImplicit false
namespace Candidate.FourthPower.PositiveFamily
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic CanonicalQuadraticSieve
open CanonicalRowCompletion IdealMobiusDivisorSum CompletedGauss CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def frequency (z : Id × O) : O := (primaryGenerator z.1)^4*z.2

theorem frequency_span (D : Id) (hD : Supported D) (k : O) :
    Ideal.span {frequency (D,k)} = D^4 * Ideal.span {k} := by
  simp only [frequency, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_pow,
    (primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)).1]

theorem frequency_ne_zero (D : Id) (hD : Supported D) (k : O) (hk : k ≠ 0) :
    frequency (D,k) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (supported_primaryGenerator_ne_zero D hD)) hk

theorem fiber_card (Ds : Finset Id) (Ks : Finset O)
    (hDs : ∀ D ∈ Ds, Supported D) (r : O) (hr : r ≠ 0) :
    ((Ds ×ˢ Ks).filter (fun z => frequency z = r)).card ≤
      (idealDivisors (Ideal.span {r})).card := by
  have hI : (Ideal.span {r} : Id) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hr
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro z hz
    obtain ⟨hz,hfreq⟩ := Finset.mem_filter.mp hz
    have hs := hDs z.1 (Finset.mem_product.mp hz).1
    apply (mem_idealDivisors hI).mpr
    rw [← hfreq, frequency_span z.1 hs z.2]
    exact (dvd_pow_self z.1 (by decide : 4 ≠ 0)).mul_right _
  · intro z hz t ht hzt
    apply Prod.ext hzt
    have hfreq := (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp ht).2.symm
    change (primaryGenerator z.1)^4*z.2 = (primaryGenerator t.1)^4*t.2 at hfreq
    rw [hzt] at hfreq
    exact mul_left_cancel₀ (pow_ne_zero _ (supported_primaryGenerator_ne_zero t.1
      (hDs t.1 (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1))) hfreq

/-- Exact regrouping by output frequency. We keep the original nonnegative
weights and bound each fiber, so no cancellation is assumed. -/
theorem weighted_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ds : Finset Id) (Ks Rs : Finset O),
      (∀ D ∈ Ds, Supported D) → (∀ k ∈ Ks, k ≠ 0) →
      ∀ (w : Id → ℝ) (G : O → ℂ) (L T : ℝ), 0 ≤ L →
      (∀ D ∈ Ds, 0 ≤ w D ∧ w D ≤ L) →
      (∀ z ∈ Ds ×ˢ Ks, frequency z ∈ Rs) →
      (∀ r ∈ Rs, r ≠ 0 ∧ (Ideal.absNorm (Ideal.span {r}) : ℝ) ≤ T) →
      (∑ D ∈ Ds, w D * ∑ k ∈ Ks, ‖G (frequency (D,k))‖^2) ≤
        L*C*T^ε * ∑ r ∈ Rs, ‖G r‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks Rs hDs _hk w G L T hL hw hmap hRs
  have hweights : (∑ D ∈ Ds, w D * ∑ k ∈ Ks, ‖G (frequency (D,k))‖^2) ≤
      L * ∑ z ∈ Ds ×ˢ Ks, ‖G (frequency z)‖^2 := by
    rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro D hD
    exact mul_le_mul_of_nonneg_right (hw D hD).2 (Finset.sum_nonneg (fun k _ => sq_nonneg _))
  have hcount : (∑ z ∈ Ds ×ˢ Ks, ‖G (frequency z)‖^2) ≤
      (C*T^ε) * ∑ r ∈ Rs, ‖G r‖^2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmap, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hI : (Ideal.span {r} : Id) ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr (hRs r hr).1
    have hc : (((Ds ×ˢ Ks).filter (fun z => frequency z = r)).card : ℝ) ≤ C*T^ε := by
      calc
        _ ≤ ((idealDivisors (Ideal.span {r})).card : ℝ) :=
          Nat.cast_le.mpr (fiber_card Ds Ks hDs r (hRs r hr).1)
        _ ≤ C*(Ideal.absNorm (Ideal.span {r}) : ℝ)^ε := hdiv _ hI
        _ ≤ C*T^ε := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hRs r hr).2 hε.le) hC.le
    calc
      _ = (((Ds ×ˢ Ks).filter (fun z => frequency z = r)).card : ℝ) * ‖G r‖^2 := by
        rw [show (∑ z ∈ (Ds ×ˢ Ks).filter (fun z => frequency z = r), ‖G (frequency z)‖^2) =
          ∑ _z ∈ (Ds ×ˢ Ks).filter (fun z => frequency z = r), ‖G r‖^2 from
          Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2])]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  calc
    _ ≤ L * ∑ z ∈ Ds ×ˢ Ks, ‖G (frequency z)‖^2 := hweights
    _ ≤ L * ((C*T^ε) * ∑ r ∈ Rs, ‖G r‖^2) := mul_le_mul_of_nonneg_left hcount hL
    _ = _ := by ring

theorem frequency_norm_bound (D : Id) (hD : Supported D) (k : O) (W K : ℝ)
    (hW : 0 ≤ W) (hDnorm : (Ideal.absNorm D : ℝ) ≤ 2*W)
    (hknorm : (Ideal.absNorm (Ideal.span {k}) : ℝ) ≤ K) :
    (Ideal.absNorm (Ideal.span {frequency (D,k)}) : ℝ) ≤ 16*K*W^4 := by
  rw [frequency_span D hD k, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg D.absNorm) hDnorm 4
  calc
    _ ≤ (2*W)^4*K := mul_le_mul hpow hknorm (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

/-- The actual weighted common-column family has density W⁻¹ and output
frequency norm at most 16 K W⁴. This includes nonsquarefree D; restricting
to squarefree D or to a retained subfamily is therefore also allowed. -/
theorem actual_average (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ds : Finset Id) (Ks : Finset O),
      (∀ D ∈ Ds, Supported D) → (∀ k ∈ Ks, k ≠ 0) →
      ∀ (w : Id → ℝ) (W K L : ℝ), 0 < W → 0 ≤ L →
      (∀ D ∈ Ds, 0 ≤ w D ∧ w D ≤ L) →
      (∀ D ∈ Ds, (Ideal.absNorm D : ℝ) ≤ 2*W) →
      (∀ k ∈ Ks, (Ideal.absNorm (Ideal.span {k}) : ℝ) ≤ K) →
      ∀ {ι : Type*} (S : Finset ι) (a : ι → O)
        (ha : ∀ i, Supported (Ideal.span {a i})),
      (∀ i ∈ S, GaussTransfer.FifthFree (a i)) → ∀ b : ι → ℂ,
      (∑ D ∈ Ds, w D * ∑ k ∈ Ks,
        ‖∑ i ∈ S, b i * (idealRowHom (primaryGenerator D) (Ideal.span {a i}))^2 *
          gaussRow (a i) (ha i) k‖^2) / W ≤
      (L*C*(16*K*W^4)^ε/W) *
        ∑ r ∈ (Ds ×ˢ Ks).image frequency, ‖gaussPolynomial S a ha b r‖^2 := by
  obtain ⟨C,hC,hbound⟩ := weighted_pushforward ε hε
  refine ⟨C,hC,?_⟩
  intro Ds Ks hDs hk w W K L hW hL hw hDN hkN ι S a ha hf b
  have hR : ∀ r ∈ (Ds ×ˢ Ks).image frequency,
      r ≠ 0 ∧ (Ideal.absNorm (Ideal.span {r}) : ℝ) ≤ 16*K*W^4 := by
    intro r hr
    obtain ⟨⟨D,k⟩,hz,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hD,hk'⟩ := Finset.mem_product.mp hz
    exact ⟨frequency_ne_zero D (hDs D hD) k (hk k hk'),
      frequency_norm_bound D (hDs D hD) k W K hW.le (hDN D hD) (hkN k hk')⟩
  have hb := hbound Ds Ks ((Ds ×ˢ Ks).image frequency) hDs hk w
    (gaussPolynomial S a ha b) L (16*K*W^4) hL hw
    (fun z hz => Finset.mem_image.mpr ⟨z,hz,rfl⟩) hR
  simp_rw [GaussTransfer.whole_column S a ha hf b]
  change (∑ D ∈ Ds, w D * ∑ k ∈ Ks, ‖gaussPolynomial S a ha b (frequency (D,k))‖^2)/W ≤ _
  calc
    _ ≤ (L*C*(16*K*W^4)^ε *
        ∑ r ∈ (Ds ×ˢ Ks).image frequency, ‖gaussPolynomial S a ha b r‖^2)/W :=
      div_le_div_of_nonneg_right hb hW.le
    _ = _ := by ring

end
end Candidate.FourthPower.PositiveFamily
