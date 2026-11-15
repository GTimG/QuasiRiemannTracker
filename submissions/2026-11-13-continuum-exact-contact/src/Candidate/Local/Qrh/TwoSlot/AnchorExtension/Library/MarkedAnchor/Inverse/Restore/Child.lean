/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Tuple
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Inj
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseAssignedCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson

/-!
# Inverse.Restore.Child — the physical injective child moment from the main columns

* `col_mask`, `gCol_mask`: weights vanishing on a set `V` (the mask primes `p | m`) are the
  unmasked weights on the pools minus `V`.
* `rowCoprimeMask_one`: the mask with `m = 1` is trivial; `childWeight_mask` (masked = unmasked
  off `{p | m}`, `0` on it); `childWeight_norm_le` (`‖c y i‖ ≤ ‖p i‖⁻¹`); `primeN_two_le` (`N p ≥ 2`).
* **`mobiusChildSumInj_le_main`**: the positive physical injective child moment on the punctured
  pool `univ \ t` with mask `m` is `≤ lamA A |I| · 12^(v+|I|) · lamA (v+|I|) |I| · Mb`, where
  `v = #(t ∪ {p | m})`, `Mb` bounds the moments of the unmasked main columns
  `mCol (childWeight ψ 1 y) (primeN p) Φ univ univ I'` (`I' ⊆ I`) at the scales reduced by the
  removed slots (`X' ∏_{I \ I'} h ≤ Xc`, slot floors `h i ≤ N P` on `lists i`), and `A`
  bounds the frozen masses `∑_{P ∈ L i} ‖a i P‖ / N P`.
* Counting: `pow_card_le_norm_rpow` (`c^#V ≤ C_{c,η} (∏_V N P)^η` for distinct nonzero prime
  ideals), `lamA_le_exp` (`lamA (v+K) K ≤ C_K (4^(K·K))^v`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)
open Qrh.MarkedAnchor.Inverse.Poisson

local notation "O" => ActualEisensteinCubic.O

/-! ## Masks -/

section Mask
variable {σ ι : Type*} [DecidableEq ι]

theorem col_mask (c c' : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (V : Finset ι)
    (hV : ∀ p ∈ V, c p = 0) (hc : ∀ p, p ∉ V → c p = c' p) (S : Finset ι) (X : ℝ) :
    col c n Φ S X = col c' n Φ (S \ V) X := by
  unfold col
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · exact Finset.powerset_mono.mpr Finset.sdiff_subset
  · intro A hA
    simp only [Finset.mem_sdiff, Finset.mem_powerset] at hA
    have : ∃ p ∈ A, p ∈ V := by
      by_contra h
      push_neg at h
      exact hA.2 (fun x hx => Finset.mem_sdiff.mpr ⟨hA.1 hx, h x hx⟩)
    obtain ⟨p, hpA, hpV⟩ := this
    rw [Finset.prod_eq_zero hpA (hV p hpV), zero_mul]
  · intro A hA
    rw [Finset.prod_congr rfl (fun p hp => hc p (Finset.mem_sdiff.mp
      (Finset.mem_powerset.mp hA hp)).2)]

theorem gCol_mask (c c' : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (V : Finset ι)
    (hV : ∀ p ∈ V, c p = 0) (hc : ∀ p, p ∉ V → c p = c' p) (U S : Finset ι) (I : Finset σ)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    gCol c n Φ U S I L a X = gCol c' n Φ (U \ V) (S \ V) I L a X := by
  unfold gCol
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
    exact ⟨hT.1.trans Finset.sdiff_subset, hT.2⟩
  · intro T hT
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_powerset, not_and] at hT
    have : ∃ p ∈ T, p ∈ V := by
      by_contra h
      push_neg at h
      exact hT.2 (fun x hx => Finset.mem_sdiff.mpr ⟨hT.1.1 hx, h x hx⟩) hT.1.2
    obtain ⟨p, hpT, hpV⟩ := this
    rw [Finset.prod_eq_zero hpT (hV p hpV), zero_mul, mul_zero]
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    have hTV : ∀ p ∈ T, p ∉ V := fun p hp => (Finset.mem_sdiff.mp (hT.1 hp)).2
    rw [Finset.prod_congr rfl (fun p hp => hc p (hTV p hp)),
      col_mask c c' n Φ V hV hc (S \ T)]
    congr 3
    ext x; simp only [Finset.mem_sdiff]; tauto

end Mask

/-! ## The child weights -/

section Weights
variable {ι : Type} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem primeN_eq_absNorm (i : ι) : primeN p i = (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  unfold primeN
  exact eisEmbedding_norm_sq_eq_absNorm_span (p i)

omit [DecidableEq ι] in
theorem primeN_two_le (hp : ∀ i, p i ≠ 0) (i : ι) : 2 ≤ primeN p i := by
  rw [primeN_eq_absNorm]
  have h0 : Ideal.absNorm (Ideal.span {p i}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hp i
  have h1 : Ideal.absNorm (Ideal.span {p i}) ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top
  have : 2 ≤ Ideal.absNorm (Ideal.span {p i}) := by omega
  exact_mod_cast this

omit [DecidableEq ι] in
theorem norm_eis_pos (hp : ∀ i, p i ≠ 0) (i : ι) : 0 < ‖eisEmbedding (p i)‖ :=
  norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero (hp i))

omit [DecidableEq ι] in
theorem rowCoprimeMask_singleton (P : ι → Ideal O) (i : ι) (u : O) :
    rowCoprimeMask P {i} u = if u ∈ P i then 0 else 1 := by
  unfold rowCoprimeMask
  by_cases h : u ∈ P i
  · rw [if_pos ⟨i, Finset.mem_singleton_self i, h⟩, if_pos h]
  · rw [if_neg, if_neg h]
    rintro ⟨j, hj, hu⟩
    rw [Finset.mem_singleton] at hj
    subst hj; exact h hu

omit [DecidableEq ι] in
theorem rowCoprimeMask_one (i : ι) :
    rowCoprimeMask (fun i => Ideal.span {p i}) {i} 1 = 1 := by
  unfold rowCoprimeMask
  rw [if_neg]
  rintro ⟨j, hj, h1⟩
  rw [Finset.mem_singleton] at hj
  subst hj
  exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top
    ((Ideal.eq_top_iff_one _).mpr h1)

omit [DecidableEq ι] in
theorem childWeight_mask (ψ : O →* ℂ) (m y : O) (i : ι) :
    childWeight p hg ψ m y i =
      if m ∈ Ideal.span {p i} then 0 else childWeight p hg ψ 1 y i := by
  unfold childWeight
  rw [rowCoprimeMask_one p i, rowCoprimeMask_singleton]
  by_cases hm : m ∈ Ideal.span {p i} <;> simp [hm]

omit [DecidableEq ι] in
theorem childWeight_norm_le (ψ : O →* ℂ) (hψ : ∀ x, ‖ψ x‖ ≤ 1) (m y : O) (i : ι) :
    ‖childWeight p hg ψ m y i‖ ≤ ‖eisEmbedding (p i)‖⁻¹ := by
  unfold childWeight
  rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have h1 := hψ (p i)
  have h2 : ‖rowCoprimeMask (fun i => Ideal.span {p i}) {i} m‖ ≤ 1 := by
    unfold rowCoprimeMask; split_ifs <;> simp
  have h3 := finiteSquarefreeRow_norm_le_one (fun i => Ideal.span {p i}) hg {i} y
  have h0 : 0 ≤ ‖eisEmbedding (p i)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  calc ‖ψ (p i)‖ * ‖rowCoprimeMask (fun i => Ideal.span {p i}) {i} m‖ *
        ‖finiteSquarefreeRow (fun i => Ideal.span {p i}) hg {i} y‖ * ‖eisEmbedding (p i)‖⁻¹
      ≤ 1 * 1 * 1 * ‖eisEmbedding (p i)‖⁻¹ := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem inv_norm_sq_eq (i : ι) :
    (‖eisEmbedding (p i)‖⁻¹)^2 = (primeN p i)⁻¹ := by
  unfold primeN; rw [inv_pow]

end Weights

/-! ## The physical child moment -/

/-- **The positive physical injective child moment is bounded by the unmasked main columns.** -/
theorem mobiusChildSumInj_le_main {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (t : Finset ι) (ψ : O →* ℂ)
    (hψ : ∀ x, ‖ψ x‖ ≤ 1) (m : O) {σ : Type} (I : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (b : ℝ) (hb : 0 ≤ b) (hΦ : ∀ x, b < x → Φ x = 0)
    (Xc : ℝ) (hXc : 0 < Xc) (Z Hc : ℝ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ i ∈ I, ∑ P ∈ lists i, ‖a i P‖ * (primeN p P)⁻¹ ≤ A)
    (ha : ∀ i ∈ I, ∀ P ∈ lists i, ‖a i P‖ ≤ 1) (h : σ → ℝ) (hh0 : ∀ i ∈ I, 0 ≤ h i)
    (hhn : ∀ i ∈ I, ∀ P ∈ lists i, h i ≤ primeN p P) (Mb : ℝ)
    (hM : ∀ I' ⊆ I, ∀ X' : ℝ, 0 < X' → X' * ∏ i ∈ I \ I', h i ≤ Xc →
      ∑ y ∈ nonzeroChildFrequencyBall 1 (Z^Hc),
        ‖mCol (childWeight p hg ψ 1 y) (primeN p) Φ Finset.univ Finset.univ I' lists a X'‖^2 ≤ Mb) :
    mobiusChildSumInj p hg (Finset.univ \ t) ψ m I lists a Φ Xc false Z Hc ≤
      lamA A I.card * (12^((t ∪ Finset.univ.filter (fun i => m ∈ Ideal.span {p i})).card + I.card) *
        (lamA ((t ∪ Finset.univ.filter (fun i => m ∈ Ideal.span {p i})).card + I.card : ℕ)
          I.card * Mb)) := by
  set Vm := Finset.univ.filter (fun i => m ∈ Ideal.span {p i}) with hVm
  set S := (Finset.univ \ t) \ Vm with hS
  have hSV : Finset.univ \ S = t ∪ Vm := by
    ext x; simp only [hS, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and]; tauto
  have hrow : ∀ y, mobiusChildRowInj p hg (Finset.univ \ t) ψ m I lists a Φ Xc false y =
      gCol (childWeight p hg ψ 1 y) (primeN p) Φ S S I lists a Xc := by
    intro y
    rw [mobiusChildRowInj_eq_markedColInj p hp hinj hg, markedColInj_eq_gCol,
      gCol_mask (childWeight p hg ψ m y) (childWeight p hg ψ 1 y) (primeN p) Φ Vm]
    · intro i hi
      rw [childWeight_mask, if_pos (Finset.mem_filter.mp hi).2]
    · intro i hi
      rw [childWeight_mask, if_neg (fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))]
  unfold mobiusChildSumInj
  simp_rw [hrow]
  have h := gCol_full_moment_le (nonzeroChildFrequencyBall 1 (Z^Hc))
    (fun y => childWeight p hg ψ 1 y) (primeN p) Φ b hb hΦ lists a
    (fun i => ‖eisEmbedding (p i)‖⁻¹)
    (fun i => lt_of_lt_of_le (by norm_num) (primeN_two_le p hp i))
    (fun i => inv_nonneg.mpr (norm_nonneg _))
    (fun i => by
      show (‖eisEmbedding (p i)‖⁻¹)^2 ≤ 1/2
      rw [inv_norm_sq_eq p i, one_div]
      exact inv_anti₀ (by norm_num) (primeN_two_le p hp i))
    (fun y _ i => childWeight_norm_le p hg ψ hψ 1 y i) A hA0 I
    (fun i hi => by
      refine le_trans (le_of_eq ?_) (hA i hi)
      apply Finset.sum_congr rfl
      intro P _
      rw [inv_norm_sq_eq p P])
    ha h hh0 hhn Finset.univ S (Finset.subset_univ S) Xc hXc Mb hM
  rwa [hSV] at h

/-! ## Counting -/

/-- `c^#V ≤ C (∏_V N P)^η` for distinct nonzero ideals `P i` (`i ∈ V`). -/
theorem pow_card_le_norm_rpow (c η : ℝ) (hc : 1 ≤ c) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} (P : ι → Ideal O) (V : Finset ι),
      Set.InjOn P V → (∀ i ∈ V, P i ≠ 0) →
      c ^ V.card ≤ C * (∏ i ∈ V, (Ideal.absNorm (P i) : ℝ)) ^ η := by
  set B : ℝ := c ^ (1/η) with hB
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by linarith) _
  refine ⟨c ^ (⌊128 * B⌋₊ + 1), pow_pos (by linarith) _, ?_⟩
  intro ι P V hinj hne
  set Vs := V.filter (fun i => (Ideal.absNorm (P i) : ℝ) ≤ B) with hVs
  set Vb := V.filter (fun i => ¬ (Ideal.absNorm (P i) : ℝ) ≤ B) with hVb
  have hcard : Vs.card + Vb.card = V.card := Finset.card_filter_add_card_filter_not _
  have hN1 : ∀ i ∈ V, (1 : ℝ) ≤ Ideal.absNorm (P i) := by
    intro i hi
    have : Ideal.absNorm (P i) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne i hi
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  -- small primes: at most `128 B` of them
  have hsmall : (Vs.card : ℝ) ≤ 128 * B := by
    have himg : (Vs.image P).card = Vs.card :=
      Finset.card_image_of_injOn (hinj.mono (by
        intro x hx; exact (Finset.mem_filter.mp hx).1))
    rw [← himg]
    apply SevenEighths.DetectorDictionaryInverseAssignedCount.list_card_le _ hB0
    intro J hJ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨hne i (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  have hsmallN : Vs.card ≤ ⌊128 * B⌋₊ := Nat.le_floor hsmall
  -- big primes: `N P ^ η ≥ c`
  have hbig : c ^ Vb.card ≤ (∏ i ∈ Vb, (Ideal.absNorm (P i) : ℝ)) ^ η := by
    rw [← Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _), ← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ => by linarith)
    intro i hi
    have hBi : B < Ideal.absNorm (P i) := lt_of_not_ge (Finset.mem_filter.mp hi).2
    calc c = B ^ η := by
          rw [hB, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hη.ne', Real.rpow_one]
      _ ≤ (Ideal.absNorm (P i) : ℝ) ^ η := Real.rpow_le_rpow hB0 hBi.le hη.le
  have hprod : (∏ i ∈ Vb, (Ideal.absNorm (P i) : ℝ)) ≤ ∏ i ∈ V, (Ideal.absNorm (P i) : ℝ) := by
    rw [← Finset.prod_filter_mul_prod_filter_not V (fun i => (Ideal.absNorm (P i) : ℝ) ≤ B)]
    have h1 : 1 ≤ ∏ i ∈ Vs, (Ideal.absNorm (P i) : ℝ) := by
      have h : (∏ _i ∈ Vs, (1:ℝ)) ≤ ∏ i ∈ Vs, (Ideal.absNorm (P i) : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
          (fun i hi => hN1 i (Finset.mem_filter.mp hi).1)
      simpa using h
    have h2 : 0 ≤ ∏ i ∈ Vb, (Ideal.absNorm (P i) : ℝ) :=
      Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    rw [← hVs, ← hVb]
    nlinarith
  have hprod0 : 0 ≤ ∏ i ∈ Vb, (Ideal.absNorm (P i) : ℝ) :=
    Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
  calc c ^ V.card = c ^ Vs.card * c ^ Vb.card := by rw [← pow_add, hcard]
    _ ≤ c ^ (⌊128 * B⌋₊ + 1) * (∏ i ∈ V, (Ideal.absNorm (P i) : ℝ)) ^ η := by
        apply mul_le_mul _ (hbig.trans (Real.rpow_le_rpow hprod0 hprod hη.le))
          (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
        exact pow_le_pow_right₀ hc (by omega)

theorem lamA_le_exp (K v : ℕ) :
    lamA ((v + K : ℕ) : ℝ) K ≤ (4 * (1 + (K : ℝ))^(2*K))^K * ((4 : ℝ)^(K*K))^v := by
  unfold lamA
  have h2v : (1 : ℝ) + v ≤ 2^v := by
    have := Nat.lt_two_pow_self (n := v)
    have h : (v : ℝ) < 2^v := by exact_mod_cast this
    have h1 : (1 : ℝ) ≤ 2^v := one_le_pow₀ (by norm_num)
    have : (v : ℝ) + 1 ≤ 2^v := by
      have : v + 1 ≤ 2^v := this
      exact_mod_cast this
    linarith
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hb : (1 : ℝ) + ((v + K : ℕ) : ℝ) ≤ (1 + K) * 2^v := by
    push_cast
    have : (1 : ℝ) ≤ 2^v := one_le_pow₀ (by norm_num)
    nlinarith
  have hX : (1 + ((v + K : ℕ) : ℝ))^(2*K) ≤ (1 + K)^(2*K) * (4 : ℝ)^(K*v) := by
    calc (1 + ((v + K : ℕ) : ℝ))^(2*K) ≤ ((1 + K) * 2^v)^(2*K) :=
          pow_le_pow_left₀ (by positivity) hb _
      _ = (1 + K)^(2*K) * (4 : ℝ)^(K*v) := by
          rw [mul_pow, ← pow_mul, show (4 : ℝ) = 2^2 by norm_num, ← pow_mul]
          congr 2; ring
  have hX1 : (1 : ℝ) ≤ (1 + K)^(2*K) * (4 : ℝ)^(K*v) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by norm_num))
  calc (2 + 2 * (1 + ((v + K : ℕ) : ℝ))^(2*K))^K
      ≤ (4 * ((1 + K)^(2*K) * (4 : ℝ)^(K*v)))^K := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
    _ = (4 * (1 + (K : ℝ))^(2*K))^K * ((4 : ℝ)^(K*K))^v := by
        rw [← mul_assoc, mul_pow, ← pow_mul, ← pow_mul]
        congr 2; ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mobiusChildSumInj_le_main
#print axioms Qrh.MarkedAnchor.Inverse.Restore.pow_card_le_norm_rpow
#print axioms Qrh.MarkedAnchor.Inverse.Restore.lamA_le_exp
