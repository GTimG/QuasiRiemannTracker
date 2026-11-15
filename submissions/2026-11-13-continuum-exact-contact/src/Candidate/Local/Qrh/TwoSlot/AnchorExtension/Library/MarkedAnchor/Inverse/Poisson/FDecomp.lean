/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Diag
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Tail
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Fibre

/-!
# Inverse.Poisson.FDecomp — one label `f`: diagonal, in-ball rows, rapid tail

`‖∑_g ∑_{a,b} groupedTerm‖ ≤ ∑_g Y |Ŵ(0)| ‖D₀(g)‖
   + ∑_g ∑_E (Y/N e) (∑_{k ∈ Kin} ‖inner g E k‖ + ∑'_{k ∈ out} ‖inner g E k‖)`,
`Kin = {k : y(k) ∈ ball}` (finite), `out = {k ≠ 0 : y(k) ∉ ball}`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open OAI.FirstPassCubeLabels (primeProductNorm)

local notation "O" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem physRow_coeff_ne_zero (f : O) (hf : f ≠ 0) (g E : Finset ι) (hE : E ⊆ g) :
    f ^ 2 * (primeSubsetGenerator (fun i => Ideal.span {p i}) E * cofactor p g E) *
      cofactor p g E ≠ 0 := by
  have hG : primeSubsetGenerator (fun i => Ideal.span {p i}) E * cofactor p g E ≠ 0 := by
    rw [← cofactor_spec p g E hE]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hp i
  have hc : cofactor p g E ≠ 0 := right_ne_zero_of_mul hG
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hf) hG) hc

include hp in
theorem physRow_injective (f : O) (hf : f ≠ 0) (g E : Finset ι) (hE : E ⊆ g) :
    Function.Injective (physRow p f g E) := by
  intro k₁ k₂ h
  unfold physRow at h
  exact mul_left_cancel₀ (physRow_coeff_ne_zero p hp f hf g E hE) h

/-- The finitely many dual frequencies whose physical row lies in `ball`. -/
def kIn (f : O) (hf : f ≠ 0) (g E : Finset ι) (hE : E ⊆ g) (ball : Finset O) : Finset O :=
  ball.preimage (physRow p f g E)
    (Set.injOn_of_injective (physRow_injective p hp f hf g E hE))

theorem mem_kIn (f : O) (hf : f ≠ 0) (g E : Finset ι) (hE : E ⊆ g) (ball : Finset O) (k : O) :
    k ∈ kIn p hp f hf g E hE ball ↔ physRow p f g E k ∈ ball := by
  unfold kIn; rw [Finset.mem_preimage]

theorem inner_norm_summable (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (g E : Finset ι) :
    Summable (fun k : O => ‖inner p hp hcop hg pool Ψ m f H W Y g E k‖) := by
  have hpair : ∀ a b : Finset ι, Summable (fun k : O =>
      ‖innerPair p hp hcop hg Ψ m f H W Y g E k a b‖) :=
    fun a b => (innerPair_summable p hp hcop hg Ψ m f H W Y hY g E a b).norm
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    (summable_sum (s := (pool \ g).powerset) fun a _ =>
      summable_sum (s := (pool \ g).powerset) fun b _ => hpair a b)
  unfold inner
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  split_ifs <;> simp

/-- The tsum over nonzero frequencies splits into the in-ball finite part and the tail. -/
theorem tsum_split (F : O → ℝ) (hF0 : ∀ k, 0 ≤ F k) (hF : Summable F) (K : Finset O)
    (hK0 : (0 : O) ∉ K) :
    ∑' k : O, (if k = 0 then 0 else F k) ≤
      ∑ k ∈ K, F k + ∑' k : {k : O | k ≠ 0 ∧ k ∉ K}, F k := by
  have hpt : ∀ k : O, (if k = 0 then 0 else F k) =
      (↑K : Set O).indicator F k + {k : O | k ≠ 0 ∧ k ∉ K}.indicator F k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [Set.indicator, hK0]
    · by_cases hkK : k ∈ K
      · simp [Set.indicator, hk, hkK]
      · simp [Set.indicator, hk, hkK]
  have hs1 : Summable ((↑K : Set O).indicator F) := hF.indicator _
  have hs2 : Summable ({k : O | k ≠ 0 ∧ k ∉ K}.indicator F) := hF.indicator _
  rw [tsum_congr hpt, hs1.tsum_add hs2, tsum_subtype {k : O | k ≠ 0 ∧ k ∉ K} F]
  apply le_of_eq
  congr 1
  rw [← tsum_subtype (↑K : Set O) F]
  exact Finset.tsum_subtype' K F

include hp in
theorem cE_norm_le (hinj : Function.Injective (fun i => Ideal.span {p i})) (Y : ℝ) (hY : 0 ≤ Y)
    (E : Finset ι) :
    ‖((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
        (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))‖ ≤
      Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [prime_product_moebius _ hprime hinj, norm_div, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hY, abs_of_nonneg (by positivity)]

/-- The per-label decomposition. -/
theorem f_decomp (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f : O) (hf : f ≠ 0) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (ball : Finset O) (hball0 : (0 : O) ∉ ball) :
    ‖∑ g ∈ pool.powerset, ∑ a ∈ (pool \ g).powerset, ∑ b ∈ (pool \ g).powerset,
      (if Disjoint a b then groupedTerm p hp hcop hg Ψ m f H W Y g a b else 0)‖ ≤
      ∑ g ∈ pool.powerset, Y * ‖paperRadialFourier W 0‖ * ‖diagCoeff p hp hcop hg Ψ m f H g‖ +
      ∑ g ∈ pool.powerset, ∑ E ∈ g.powerset.attach,
        Y / ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.1)‖ ^ 2 *
          (∑ k ∈ kIn p hp f hf g E.1 (Finset.mem_powerset.mp E.2) ball,
              ‖inner p hp hcop hg pool Ψ m f H W Y g E.1 k‖ +
            ∑' k : {k : O | k ≠ 0 ∧ k ∉ kIn p hp f hf g E.1 (Finset.mem_powerset.mp E.2) ball},
              ‖inner p hp hcop hg pool Ψ m f H W Y g E.1 k‖) := by
  rw [← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [grouped_eq_inner p hp hcop hg pool Ψ m f H W Y hY g]
  set cE : Finset ι → ℂ := fun E =>
    (UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) * Y /
      (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ) with hcE
  have hsplitE : ∀ E : Finset ι, ∑' k : O, inner p hp hcop hg pool Ψ m f H W Y g E k =
      paperRadialFourier W 0 * diagCoeff p hp hcop hg Ψ m f H g +
        ∑' k : O, (if k = 0 then 0 else inner p hp hcop hg pool Ψ m f H W Y g E k) := by
    intro E
    rw [(inner_summable p hp hcop hg pool Ψ m f H W Y hY g E).tsum_eq_add_tsum_ite 0,
      inner_zero p hp hcop hg pool Ψ m f H W Y g E]
  conv_lhs => simp only [hsplitE, mul_add, Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← Finset.sum_mul, norm_mul]
    have hsum : ∑ E ∈ g.powerset, cE E = (Y : ℂ) * ∑ E ∈ g.powerset,
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro E _; simp only [hcE]; ring
    rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY, norm_mul]
    have hmd := mobius_density_bound p hp hinj g
    have h1 := norm_nonneg (paperRadialFourier W 0)
    have h2 := norm_nonneg (diagCoeff p hp hcop hg Ψ m f H g)
    calc Y * ‖∑ E ∈ g.powerset, ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 : ℝ))‖ *
        (‖paperRadialFourier W 0‖ * ‖diagCoeff p hp hcop hg Ψ m f H g‖)
        ≤ Y * 1 * (‖paperRadialFourier W 0‖ * ‖diagCoeff p hp hcop hg Ψ m f H g‖) := by gcongr
      _ = _ := by ring
  · rw [← Finset.sum_attach]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun E _ => ?_)
    have hE : E.1 ⊆ g := Finset.mem_powerset.mp E.2
    rw [norm_mul]
    apply mul_le_mul (cE_norm_le p hp hinj Y hY.le E.1) _ (norm_nonneg _) (by positivity)
    have hS := inner_norm_summable p hp hcop hg pool Ψ m f H W Y hY g E.1
    have hK0 : (0 : O) ∉ kIn p hp f hf g E.1 hE ball := by
      rw [mem_kIn]
      unfold physRow; rw [mul_zero]; exact hball0
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · refine hS.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      split_ifs <;> simp
    have hpt : ∀ k : O, ‖(if k = 0 then (0 : ℂ) else inner p hp hcop hg pool Ψ m f H W Y g E.1 k)‖ =
        (if k = 0 then 0 else ‖inner p hp hcop hg pool Ψ m f H W Y g E.1 k‖) := by
      intro k; split_ifs <;> simp
    rw [tsum_congr hpt]
    exact tsum_split _ (fun k => norm_nonneg _) hS _ hK0

end
end Qrh.MarkedAnchor.Inverse.Poisson
