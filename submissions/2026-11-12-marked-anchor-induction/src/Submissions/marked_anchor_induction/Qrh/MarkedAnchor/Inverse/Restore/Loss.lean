/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Child

/-!
# Inverse.Restore.Loss — the restoration loss of the punctures and the mask

* `prod_norm_le_of_mem`: distinct pool primes containing `m` have `∏ N P ≤ ‖m‖²`.
* **`restore_loss`**: `lamA 256 |I| · 12^(v+|I|) · lamA (v+|I|) |I| ≤ C_{K,η} (N t · ‖m‖²)^η`,
  `v = #(t ∪ {i | m ∈ (p i)})`, `|I| ≤ K` (`lamA_le_exp`, `pow_card_le_norm_rpow`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)

local notation "O" => ActualEisensteinCubic.O

theorem prod_norm_le_of_mem {ι : Type} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (V : Finset ι) (m : O)
    (hm : m ≠ 0) (hV : ∀ i ∈ V, m ∈ Ideal.span {p i}) :
    ∏ i ∈ V, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤ ‖eisEmbedding m‖^2 := by
  have hdvd : (∏ i ∈ V, Ideal.span {p i}) ∣ Ideal.span {m} := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      show IsCoprime (Ideal.span {p i}) (Ideal.span {p j})
      rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance
        (fun h => hij (hinj h))
    · intro i hi
      exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr (hV i hi))
  have h0 : Ideal.absNorm (Ideal.span {m}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hm
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (map_dvd Ideal.absNorm hdvd)
  rw [map_prod] at hle
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← Nat.cast_prod]
  exact_mod_cast hle

/-- **The restoration loss.** -/
theorem restore_loss (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → O)
      [∀ i, (Ideal.span {p i}).IsMaximal] (_hp : ∀ i, p i ≠ 0)
      (_hinj : Function.Injective (fun i => Ideal.span {p i})) [Fintype ι]
      (t : Finset ι) (m : O) (_hm : m ≠ 0) (k : ℕ) (_hk : k ≤ K) (Gt Nm : ℝ)
      (_hGt : FirstPassCubeLabels.primeProductNorm p t ≤ Gt) (_hNm : ‖eisEmbedding m‖^2 ≤ Nm),
      lamA 256 k * (12^((t ∪ Finset.univ.filter (fun i => m ∈ Ideal.span {p i})).card + k) *
        lamA ((t ∪ Finset.univ.filter (fun i => m ∈ Ideal.span {p i})).card + k : ℕ) k) ≤
        CL * (Gt * Nm)^η := by
  set c : ℝ := 12 * (4 : ℝ)^(K*K) with hc
  have hc1 : 1 ≤ c := by
    have : (1:ℝ) ≤ 4^(K*K) := one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨Cη, hCη, hpow⟩ := pow_card_le_norm_rpow c η hc1 hη
  set C1 : ℝ := lamA 256 K * (12^K * (4 * (1 + (K:ℝ))^(2*K))^K) with hC1
  have hC1pos : 0 < C1 := by
    have := one_le_lamA 256 (by norm_num) K
    positivity
  refine ⟨C1 * Cη, by positivity, ?_⟩
  intro ι _ p _ hp hinj _ t m hm k hk Gt Nm hGt hNm
  set Vm := Finset.univ.filter (fun i => m ∈ Ideal.span {p i}) with hVm
  set V := t ∪ Vm with hV
  set v := V.card with hv
  have hA0 : (0:ℝ) ≤ 256 := by norm_num
  -- the combinatorial factors
  have h1 : lamA 256 k ≤ lamA 256 K := lamA_mono 256 hA0 hk
  have h2 : (12:ℝ)^(v + k) ≤ 12^(v + K) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : lamA ((v + k : ℕ) : ℝ) k ≤ lamA ((v + K : ℕ) : ℝ) K := by
    calc lamA ((v + k : ℕ) : ℝ) k ≤ lamA ((v + K : ℕ) : ℝ) k :=
          lamA_mono_left (Nat.cast_nonneg _) (by exact_mod_cast (by omega : v + k ≤ v + K)) k
      _ ≤ lamA ((v + K : ℕ) : ℝ) K := lamA_mono _ (Nat.cast_nonneg _) hk
  have h4 := lamA_le_exp K v
  have hcomb : (12:ℝ)^(v + K) * lamA ((v + K : ℕ) : ℝ) K ≤
      (12^K * (4 * (1 + (K:ℝ))^(2*K))^K) * c^v := by
    calc (12:ℝ)^(v + K) * lamA ((v + K : ℕ) : ℝ) K
        ≤ 12^(v + K) * ((4 * (1 + (K:ℝ))^(2*K))^K * ((4 : ℝ)^(K*K))^v) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (12^K * (4 * (1 + (K:ℝ))^(2*K))^K) * c^v := by
          rw [hc, mul_pow, pow_add]; ring
  -- the counting factor
  have hP : ∀ i ∈ V, Ideal.span {p i} ≠ 0 := by
    intro i _; rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hp i
  have hcv := hpow (fun i => Ideal.span {p i}) V (hinj.injOn) hP
  have hN1 : ∀ i, (1:ℝ) ≤ (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
    intro i
    have : Ideal.absNorm (Ideal.span {p i}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hp i
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hprodV : ∏ i ∈ V, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤ Gt * Nm := by
    have hsplit := Finset.prod_union_inter (s₁ := t) (s₂ := Vm)
      (f := fun i => (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    have hint : 1 ≤ ∏ i ∈ t ∩ Vm, (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
      have h := Finset.prod_le_prod₀ (s := t ∩ Vm) (f := fun _ => (1:ℝ))
        (g := fun i => (Ideal.absNorm (Ideal.span {p i}) : ℝ)) (fun _ _ => zero_le_one)
        (fun i _ => hN1 i)
      simpa using h
    have ht : ∏ i ∈ t, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤ Gt := by
      refine le_trans (le_of_eq ?_) hGt
      rw [primeProductNorm_eq_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [primeN_eq_absNorm]
    have hm' : ∏ i ∈ Vm, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤ Nm :=
      (prod_norm_le_of_mem p hinj Vm m hm (fun i hi => (Finset.mem_filter.mp hi).2)).trans hNm
    have hV0 : 0 ≤ ∏ i ∈ V, (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
      Finset.prod_nonneg (fun i _ => (zero_le_one.trans (hN1 i)))
    have ht0 : 0 ≤ ∏ i ∈ t, (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
      Finset.prod_nonneg (fun i _ => (zero_le_one.trans (hN1 i)))
    have hVm0 : 0 ≤ ∏ i ∈ Vm, (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
      Finset.prod_nonneg (fun i _ => (zero_le_one.trans (hN1 i)))
    calc ∏ i ∈ V, (Ideal.absNorm (Ideal.span {p i}) : ℝ)
        ≤ (∏ i ∈ V, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) *
            ∏ i ∈ t ∩ Vm, (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
          le_mul_of_one_le_right hV0 hint
      _ = (∏ i ∈ t, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) *
            ∏ i ∈ Vm, (Ideal.absNorm (Ideal.span {p i}) : ℝ) := hsplit
      _ ≤ Gt * Nm := mul_le_mul ht hm' hVm0 (ht0.trans ht)
  have hV0 : 0 ≤ ∏ i ∈ V, (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
    Finset.prod_nonneg (fun i _ => (zero_le_one.trans (hN1 i)))
  have hcv' : c^v ≤ Cη * (Gt * Nm)^η :=
    hcv.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hV0 hprodV hη.le) hCη.le)
  have hL0 : 0 ≤ lamA ((v + k : ℕ) : ℝ) k := (zero_le_one).trans (one_le_lamA _ (Nat.cast_nonneg _) k)
  calc lamA 256 k * (12^(v + k) * lamA ((v + k : ℕ) : ℝ) k)
      ≤ lamA 256 K * (12^(v + K) * lamA ((v + K : ℕ) : ℝ) K) := by
        apply mul_le_mul h1 (mul_le_mul h2 h3 hL0 (by positivity)) (by positivity)
          ((zero_le_one).trans (one_le_lamA 256 hA0 K))
    _ ≤ lamA 256 K * ((12^K * (4 * (1 + (K:ℝ))^(2*K))^K) * (Cη * (Gt * Nm)^η)) := by
        apply mul_le_mul_of_nonneg_left _ ((zero_le_one).trans (one_le_lamA 256 hA0 K))
        exact hcomb.trans (mul_le_mul_of_nonneg_left hcv' (by positivity))
    _ = C1 * Cη * (Gt * Nm)^η := by rw [hC1]; ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.restore_loss
