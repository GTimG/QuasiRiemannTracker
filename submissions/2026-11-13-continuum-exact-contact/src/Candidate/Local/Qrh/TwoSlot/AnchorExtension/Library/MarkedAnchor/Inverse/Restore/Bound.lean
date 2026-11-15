/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Diff
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Moment

/-!
# Inverse.Restore.Bound — the physical child moment from the main-term moments

Rows `y ∈ Y`, row-dependent prime weights `c y` with `‖c y p‖ ≤ κ p`, norms `n ≥ 1`. Three
reductions of row moments `∑_y ‖·‖²`:

* **`gCol_moment_le`** (frozen terms, strong induction on `|I|` from `Diff.mCol_sub_gCol`): the
  physical exact-image column `gCol U S I X` is bounded by `lamA A |I|` times a bound for the
  main columns `mCol (U ∩ S') S' I' X'` (`I' ⊆ I`, `#(S \ S') + |I'| ≤ |I|`, `X' ≤ X`), where
  `A` bounds the frozen slot masses `∑_{p ∈ L i} ‖a i p‖ κ p²` (`frozen_mass_le`).
* **`mCol_moment_avoid`** (column side, `Moment.moment_avoid` for `mCol`): restoring a set `T`
  of avoided column primes costs `∏_T (1-κ)^{-2}`.
* **`mCol_avoid_tuple_le`** (tuple side, `mCol_tuple_split`): restoring a set `V` of primes
  forbidden to the tuples costs `lamA #V |I|` (requires `κ ≤ 1`, `‖a‖ ≤ 1`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators

variable {σ ι ρ : Type*} [DecidableEq ι]

/-! ## Frozen masses -/

theorem norm_primeMarkInj_insert_le (F : Finset σ) (i0 : σ) (hi0 : i0 ∉ F) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (B : Finset ι) :
    ‖primeMarkInj (insert i0 F) L a B‖ ≤
      ∑ p ∈ (L i0).filter (· ∈ B), ‖a i0 p‖ * ‖primeMarkInj F L a (B.erase p)‖ := by
  rw [primeMarkInj_insert F i0 hi0]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro p _
  rw [norm_mul]

/-- Double counting `(B, p ∈ B) ↔ (p, B \ {p})`. -/
theorem sum_card_succ_erase (U : Finset ι) (k : ℕ) (g : ι → Finset ι → ℝ) :
    ∑ B ∈ U.powerset.filter (fun B => B.card = k + 1), ∑ p ∈ B, g p B =
      ∑ p ∈ U, ∑ B ∈ (U.erase p).powerset.filter (fun B => B.card = k), g p (insert p B) := by
  rw [Finset.sum_comm' (t' := U)
    (s' := fun p => (U.powerset.filter (fun B => B.card = k + 1)).filter (fun B => p ∈ B))]
  · apply Finset.sum_congr rfl
    intro p hpU
    apply Finset.sum_nbij' (fun B => B.erase p) (fun B => insert p B)
    · intro B hB
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hB ⊢
      refine ⟨Finset.erase_subset_erase p hB.1.1, ?_⟩
      rw [Finset.card_erase_of_mem hB.2, hB.1.2]; simp
    · intro B hB
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hB ⊢
      have hpB : p ∉ B := fun h => Finset.notMem_erase p U (hB.1 h)
      refine ⟨⟨Finset.insert_subset hpU (hB.1.trans (Finset.erase_subset p U)), ?_⟩,
        Finset.mem_insert_self p B⟩
      rw [Finset.card_insert_of_notMem hpB, hB.2]
    · intro B hB
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hB
      exact Finset.insert_erase hB.2
    · intro B hB
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hB
      exact Finset.erase_insert (fun h => Finset.notMem_erase p U (hB.1 h))
    · intro B hB
      simp only [Finset.mem_filter, Finset.mem_powerset] at hB
      rw [Finset.insert_erase hB.2]
  · intro B p
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, h1 h3⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, _⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- **Frozen mass**: `∑_{B ⊆ U, |B| = |F|} ‖mark_F(B)‖ ∏_B w ≤ ∏_{i∈F} ∑_{p ∈ L i ∩ U} ‖a i p‖ w p`. -/
theorem frozen_mass_le (L : σ → Finset ι) (a : σ → ι → ℂ) (w : ι → ℝ) (hw : ∀ p, 0 ≤ w p) :
    ∀ (F : Finset σ) (U : Finset ι),
      ∑ B ∈ U.powerset.filter (fun B => B.card = F.card),
          ‖primeMarkInj F L a B‖ * ∏ p ∈ B, w p ≤
        ∏ i ∈ F, ∑ p ∈ (L i).filter (· ∈ U), ‖a i p‖ * w p := by
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro U
    rw [sum_card_empty U (fun B => ‖primeMarkInj (∅ : Finset σ) L a B‖ * ∏ p ∈ B, w p)]
    simp [primeMarkInj_empty_slots]
  | @insert i0 F hi0 ih =>
    intro U
    have hmass0 : ∀ V : Finset ι, 0 ≤ ∏ i ∈ F, ∑ p ∈ (L i).filter (· ∈ V), ‖a i p‖ * w p :=
      fun V => Finset.prod_nonneg fun i _ =>
        Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (hw p)
    rw [Finset.card_insert_of_notMem hi0, Finset.prod_insert hi0]
    set g : ι → Finset ι → ℝ := fun p B =>
      if p ∈ L i0 then ‖a i0 p‖ * ‖primeMarkInj F L a (B.erase p)‖ * ∏ q ∈ B, w q else 0
      with hg
    calc ∑ B ∈ U.powerset.filter (fun B => B.card = F.card + 1),
          ‖primeMarkInj (insert i0 F) L a B‖ * ∏ p ∈ B, w p
        ≤ ∑ B ∈ U.powerset.filter (fun B => B.card = F.card + 1), ∑ p ∈ B, g p B := by
          apply Finset.sum_le_sum
          intro B _
          have h1 := norm_primeMarkInj_insert_le F i0 hi0 L a B
          have h2 : 0 ≤ ∏ p ∈ B, w p := Finset.prod_nonneg fun p _ => hw p
          calc _ ≤ (∑ p ∈ (L i0).filter (· ∈ B),
                ‖a i0 p‖ * ‖primeMarkInj F L a (B.erase p)‖) * ∏ p ∈ B, w p :=
                mul_le_mul_of_nonneg_right h1 h2
            _ = ∑ p ∈ B, g p B := by
                rw [Finset.sum_mul, Finset.sum_filter, Finset.sum_ite_mem]
                simp only [hg]
                rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_comm]
      _ = ∑ p ∈ U, ∑ B ∈ (U.erase p).powerset.filter (fun B => B.card = F.card),
            g p (insert p B) := sum_card_succ_erase U F.card g
      _ = ∑ p ∈ U, (if p ∈ L i0 then ‖a i0 p‖ * w p *
            ∑ B ∈ (U.erase p).powerset.filter (fun B => B.card = F.card),
              ‖primeMarkInj F L a B‖ * ∏ q ∈ B, w q else 0) := by
          apply Finset.sum_congr rfl
          intro p _
          split_ifs with hp
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro B hB
            simp only [Finset.mem_filter, Finset.mem_powerset] at hB
            have hpB : p ∉ B := fun h => Finset.notMem_erase p U (hB.1 h)
            simp only [hg, if_pos hp, Finset.erase_insert hpB, Finset.prod_insert hpB]
            ring
          · simp [hg, hp]
      _ ≤ ∑ p ∈ U, (if p ∈ L i0 then ‖a i0 p‖ * w p *
            ∏ i ∈ F, ∑ p ∈ (L i).filter (· ∈ U), ‖a i p‖ * w p else 0) := by
          apply Finset.sum_le_sum
          intro p _
          split_ifs with hp
          · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (hw p))
            refine (ih (U.erase p)).trans ?_
            apply Finset.prod_le_prod₀
            · intro i _
              exact Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (hw q)
            · intro i _
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro q hq
                simp only [Finset.mem_filter] at hq ⊢
                exact ⟨hq.1, Finset.mem_of_mem_erase hq.2⟩
              · intro q _ _
                exact mul_nonneg (norm_nonneg _) (hw q)
          · exact le_rfl
      _ = (∑ p ∈ (L i0).filter (· ∈ U), ‖a i0 p‖ * w p) *
            ∏ i ∈ F, ∑ p ∈ (L i).filter (· ∈ U), ‖a i p‖ * w p := by
          rw [Finset.sum_mul, Finset.sum_filter, Finset.sum_ite_mem, ← Finset.sum_filter,
            Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- Sum of the masses over the nonempty slot subsets. -/
theorem mass_powerset_le (I : Finset σ) (m : Finset σ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hm : ∀ F ⊆ I, m F ≤ A ^ F.card) (hm0 : ∀ F ⊆ I, 0 ≤ m F) :
    ∑ F ∈ I.powerset \ {∅}, m F ≤ (1 + A) ^ I.card := by
  calc ∑ F ∈ I.powerset \ {∅}, m F ≤ ∑ F ∈ I.powerset, m F := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        intro F hF _
        exact hm0 F (Finset.mem_powerset.mp hF)
    _ ≤ ∑ F ∈ I.powerset, A ^ F.card :=
        Finset.sum_le_sum fun F hF => hm F (Finset.mem_powerset.mp hF)
    _ = (1 + A) ^ I.card := by
        have h := Finset.prod_add (fun _ : σ => A) (fun _ : σ => (1 : ℝ)) I
        simp only [Finset.prod_const, one_pow, mul_one] at h
        rw [add_comm 1 A, h]

/-! ## The generic recursion step -/

theorem norm_sub_sq_le (x y : ℂ) : ‖x - y‖^2 ≤ 2 * ‖x‖^2 + 2 * ‖y‖^2 := by
  have h := norm_sub_le x y
  have h0 := norm_nonneg (x - y)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]

/-- One step: `G = M - ∑_j w_j v_j` with `‖w_j‖ ≤ W_j`. -/
theorem rec_step {κ : Type*} (Y : Finset ρ) (Gv Mv : ρ → ℂ) (s : Finset κ)
    (w v : κ → ρ → ℂ) (W : κ → ℝ) (hW0 : ∀ j ∈ s, 0 ≤ W j)
    (hW : ∀ j ∈ s, ∀ y ∈ Y, ‖w j y‖ ≤ W j)
    (hG : ∀ y ∈ Y, Gv y = Mv y - ∑ j ∈ s, w j y * v j y)
    (Mb Lb Wb : ℝ) (hLb : 0 ≤ Lb) (hM : ∑ y ∈ Y, ‖Mv y‖^2 ≤ Mb)
    (hv : ∀ j ∈ s, ∑ y ∈ Y, ‖v j y‖^2 ≤ Lb) (hWb : ∑ j ∈ s, W j ≤ Wb) :
    ∑ y ∈ Y, ‖Gv y‖^2 ≤ 2 * Mb + 2 * (Wb^2 * Lb) := by
  have hS0 : 0 ≤ ∑ j ∈ s, W j := Finset.sum_nonneg hW0
  have h1 : ∀ y ∈ Y, ‖Gv y‖^2 ≤ 2 * ‖Mv y‖^2 +
      2 * ((∑ j ∈ s, W j) * ∑ j ∈ s, W j * ‖v j y‖^2) := by
    intro y hy
    rw [hG y hy]
    refine (norm_sub_sq_le _ _).trans ?_
    have := norm_sum_sq_le_weighted s (fun j => w j y) (fun j => v j y) W
      (fun j hj => hW j hj y hy)
    linarith
  calc ∑ y ∈ Y, ‖Gv y‖^2
      ≤ ∑ y ∈ Y, (2 * ‖Mv y‖^2 + 2 * ((∑ j ∈ s, W j) * ∑ j ∈ s, W j * ‖v j y‖^2)) :=
        Finset.sum_le_sum h1
    _ = 2 * ∑ y ∈ Y, ‖Mv y‖^2 +
          2 * ((∑ j ∈ s, W j) * ∑ j ∈ s, W j * ∑ y ∈ Y, ‖v j y‖^2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_comm]
        congr 3
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ ≤ 2 * Mb + 2 * ((∑ j ∈ s, W j) * ∑ j ∈ s, W j * Lb) := by
        gcongr with j hj
        · exact hW0 j hj
        · exact hv j hj
    _ = 2 * Mb + 2 * ((∑ j ∈ s, W j)^2 * Lb) := by rw [← Finset.sum_mul]; ring
    _ ≤ 2 * Mb + 2 * (Wb^2 * Lb) := by gcongr

/-- The recursion constant. -/
def lamA (A : ℝ) (k : ℕ) : ℝ := (2 + 2 * (1 + A)^(2*k))^k

theorem lamA_base_one_le (A : ℝ) (hA : 0 ≤ A) (k : ℕ) : 1 ≤ 2 + 2 * (1 + A)^(2*k) := by
  have : 0 ≤ (1 + A)^(2*k) := pow_nonneg (by linarith) _
  linarith

theorem one_le_lamA (A : ℝ) (hA : 0 ≤ A) (k : ℕ) : 1 ≤ lamA A k :=
  one_le_pow₀ (lamA_base_one_le A hA k)

theorem lamA_mono (A : ℝ) (hA : 0 ≤ A) {k k' : ℕ} (h : k' ≤ k) : lamA A k' ≤ lamA A k := by
  unfold lamA
  have h1 : (1 + A)^(2*k') ≤ (1 + A)^(2*k) := pow_le_pow_right₀ (by linarith) (by omega)
  calc (2 + 2 * (1 + A)^(2*k'))^k' ≤ (2 + 2 * (1 + A)^(2*k))^k' := by
        apply pow_le_pow_left₀ (by linarith [lamA_base_one_le A hA k']); linarith
    _ ≤ (2 + 2 * (1 + A)^(2*k))^k := pow_le_pow_right₀ (lamA_base_one_le A hA k) h

theorem lamA_mono_left {A A' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (k : ℕ) : lamA A k ≤ lamA A' k := by
  unfold lamA
  have h1 : (1 + A)^(2*k) ≤ (1 + A')^(2*k) := pow_le_pow_left₀ (by linarith) (by linarith) _
  apply pow_le_pow_left₀ (by linarith [lamA_base_one_le A hA k]); linarith

theorem lamA_step (A : ℝ) (hA : 0 ≤ A) (k : ℕ) (hk : 1 ≤ k) (Mb : ℝ) (hMb : 0 ≤ Mb) :
    2 * Mb + 2 * (((1 + A)^k)^2 * (lamA A (k-1) * Mb)) ≤ lamA A k * Mb := by
  have hb := lamA_base_one_le A hA k
  set b := 2 + 2 * (1 + A)^(2*k) with hbdef
  have hl : lamA A (k-1) ≤ b^(k-1) := by
    unfold lamA
    have h1 : (1 + A)^(2*(k-1)) ≤ (1 + A)^(2*k) := pow_le_pow_right₀ (by linarith) (by omega)
    apply pow_le_pow_left₀ (by linarith [lamA_base_one_le A hA (k-1)]); linarith
  have hl0 : 0 ≤ lamA A (k-1) := le_trans zero_le_one (one_le_lamA A hA _)
  have hb1 : 1 ≤ b^(k-1) := one_le_pow₀ hb
  have hk' : lamA A k = b * b^(k-1) := by
    unfold lamA; rw [← hbdef, ← pow_succ']; congr 1; omega
  have hsq : ((1 + A)^k)^2 = (1 + A)^(2*k) := by rw [← pow_mul, mul_comm]
  rw [hk', hsq]
  have hp : 0 ≤ (1 + A)^(2*k) := pow_nonneg (by linarith) _
  have e1 : (1 + A)^(2*k) * lamA A (k-1) ≤ (1 + A)^(2*k) * b^(k-1) :=
    mul_le_mul_of_nonneg_left hl hp
  calc 2 * Mb + 2 * ((1 + A)^(2*k) * (lamA A (k-1) * Mb))
      = (2 + 2 * ((1 + A)^(2*k) * lamA A (k-1))) * Mb := by ring
    _ ≤ (2 * b^(k-1) + 2 * ((1 + A)^(2*k) * b^(k-1))) * Mb := by
        apply mul_le_mul_of_nonneg_right _ hMb; linarith
    _ = b * b^(k-1) * Mb := by rw [hbdef]; ring

/-! ## Physical column → main columns (frozen terms) -/

theorem one_le_prod_n (n : ι → ℝ) (hn : ∀ i, 1 ≤ n i) (B : Finset ι) : 1 ≤ ∏ i ∈ B, n i := by
  have h : (∏ _i ∈ B, (1:ℝ)) ≤ ∏ i ∈ B, n i := by
    gcongr with i _
    exact hn i
  simpa using h

/-- A nonzero injective mark forces the image norms above the slot floors `h`. -/
theorem prod_le_of_mark_ne_zero (L : σ → Finset ι) (a : σ → ι → ℂ) (n : ι → ℝ) (h : σ → ℝ)
    (hn : ∀ i, 1 ≤ n i) :
    ∀ (F : Finset σ) (B : Finset ι), (∀ i ∈ F, 0 ≤ h i) → (∀ i ∈ F, ∀ p ∈ L i, h i ≤ n p) →
      primeMarkInj F L a B ≠ 0 → ∏ i ∈ F, h i ≤ ∏ p ∈ B, n p := by
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro B _ _ _
    simpa using one_le_prod_n n hn B
  | @insert i0 F hi0 ih =>
    intro B hh0 hhn hm
    rw [primeMarkInj_insert F i0 hi0] at hm
    obtain ⟨p, hp, hpm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hp' := Finset.mem_filter.mp hp
    have hm' : primeMarkInj F L a (B.erase p) ≠ 0 := right_ne_zero_of_mul hpm
    have h1 := ih (B.erase p) (fun i hi => hh0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hhn i (Finset.mem_insert_of_mem hi)) hm'
    rw [Finset.prod_insert hi0, ← Finset.mul_prod_erase B n hp'.2]
    have h0 : 0 ≤ ∏ i ∈ F, h i :=
      Finset.prod_nonneg fun i hi => hh0 i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul (hhn i0 (Finset.mem_insert_self i0 F) p hp'.1) h1 h0
      (le_trans zero_le_one (hn p))

theorem prod_sdiff_split (h : σ → ℝ) (I F I'' : Finset σ) (hF : F ⊆ I) (hI'' : I'' ⊆ I \ F) :
    ∏ i ∈ I \ I'', h i = (∏ i ∈ (I \ F) \ I'', h i) * ∏ i ∈ F, h i := by
  have hsub : F ⊆ I \ I'' := fun x hx =>
    Finset.mem_sdiff.mpr ⟨hF hx, fun h' => (Finset.mem_sdiff.mp (hI'' h')).2 hx⟩
  rw [← Finset.prod_sdiff hsub]
  congr 1
  apply Finset.prod_congr _ (fun _ _ => rfl)
  ext x; simp only [Finset.mem_sdiff]; tauto

/-- Scale bookkeeping of one recursion step: removing the slots `F` divides the scale by
`P ≥ ∏_F h`. -/
theorem scale_step (h : σ → ℝ) (I F I'' : Finset σ) (hF : F ⊆ I) (hI'' : I'' ⊆ I \ F)
    (hh0 : ∀ i ∈ I, 0 ≤ h i) (X X'' P : ℝ) (hP : 0 < P) (hFP : ∏ i ∈ F, h i ≤ P)
    (hX'' : X'' * ∏ i ∈ (I \ F) \ I'', h i ≤ X / P) (hX : 0 ≤ X) :
    X'' * ∏ i ∈ I \ I'', h i ≤ X := by
  rw [prod_sdiff_split h I F I'' hF hI'', ← mul_assoc]
  have hF0 : 0 ≤ ∏ i ∈ F, h i := Finset.prod_nonneg fun i hi => hh0 i (hF hi)
  calc (X'' * ∏ i ∈ (I \ F) \ I'', h i) * ∏ i ∈ F, h i ≤ X / P * P :=
        mul_le_mul hX'' hFP hF0 (div_nonneg hX hP.le)
    _ = X := by field_simp

theorem prod_sdiff_self_one (h : σ → ℝ) (I : Finset σ) : ∏ i ∈ I \ I, h i = 1 := by
  rw [Finset.sdiff_self, Finset.prod_empty]

/-- **The physical exact-image column is bounded by the main columns.** The main columns are
needed only at the reduced scales: removing the slots `I \ I'` divides the scale by at least
`∏_{I \ I'} h` (slot floors `h i ≤ n p` on `L i`). -/
theorem gCol_moment_le (Y : Finset ρ) (c : ρ → ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (κ : ι → ℝ) (hn : ∀ i, 1 ≤ n i)
    (hκ0 : ∀ p, 0 ≤ κ p) (hc : ∀ y ∈ Y, ∀ p, ‖c y p‖ ≤ κ p) (A : ℝ) (hA0 : 0 ≤ A) (Mb : ℝ)
    (h : σ → ℝ) :
    ∀ (k : ℕ) (I : Finset σ), I.card ≤ k →
    (∀ i ∈ I, ∑ p ∈ L i, ‖a i p‖ * κ p ^ 2 ≤ A) →
    (∀ i ∈ I, 0 ≤ h i) → (∀ i ∈ I, ∀ p ∈ L i, h i ≤ n p) →
    ∀ (U S : Finset ι), U ⊆ S → ∀ X : ℝ, 0 < X →
    (∀ I' ⊆ I, ∀ S' ⊆ S, (S \ S').card + I'.card ≤ I.card → ∀ X' : ℝ, 0 < X' →
      X' * ∏ i ∈ I \ I', h i ≤ X →
      ∑ y ∈ Y, ‖mCol (c y) n Φ (U ∩ S') S' I' L a X'‖^2 ≤ Mb) →
    ∑ y ∈ Y, ‖gCol (c y) n Φ U S I L a X‖^2 ≤ lamA A I.card * Mb := by
  have hn' : ∀ i, n i ≠ 0 := fun i => (lt_of_lt_of_le one_pos (hn i)).ne'
  have hempty : ∀ (U S : Finset ι), U ⊆ S → ∀ X : ℝ, 0 < X →
      (∀ I' ⊆ (∅ : Finset σ), ∀ S' ⊆ S, (S \ S').card + I'.card ≤ (∅ : Finset σ).card →
        ∀ X' : ℝ, 0 < X' → X' * ∏ i ∈ (∅ : Finset σ) \ I', h i ≤ X →
        ∑ y ∈ Y, ‖mCol (c y) n Φ (U ∩ S') S' I' L a X'‖^2 ≤ Mb) →
      ∑ y ∈ Y, ‖gCol (c y) n Φ U S (∅ : Finset σ) L a X‖^2 ≤ lamA A (∅ : Finset σ).card * Mb := by
    intro U S _ X hX hM
    have h := hM ∅ (Finset.empty_subset _) S (subset_refl S) (by simp) X hX (by simp)
    simp only [mCol_empty] at h
    simp only [gCol_empty, Finset.card_empty, lamA, pow_zero, one_mul]
    exact h
  intro k
  induction k with
  | zero =>
    intro I hI _ _ _ U S hUS X hX hM
    have hI0 : I = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hI)
    subst hI0
    exact hempty U S hUS X hX hM
  | succ k ih =>
    intro I hI hA hh0 hhn U S hUS X hX hM
    by_cases hIe : I = ∅
    · subst hIe
      exact hempty U S hUS X hX hM
    have hIpos : 1 ≤ I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hIe)
    have hMtop := hM I (subset_refl I) S (subset_refl S) (by simp) X hX
      (by rw [prod_sdiff_self_one, mul_one])
    have hMb0 : 0 ≤ Mb := le_trans (Finset.sum_nonneg (fun y _ => sq_nonneg _)) hMtop
    set s0 := (I.powerset \ {∅}).sigma
      (fun F => U.powerset.filter (fun B => B.card = F.card)) with hs0
    set s := s0.filter (fun j => primeMarkInj j.1 L a j.2 ≠ 0) with hs
    have hmem : ∀ j ∈ s, j.1 ⊆ I ∧ j.1 ≠ ∅ ∧ j.2 ⊆ U ∧ j.2.card = j.1.card ∧
        primeMarkInj j.1 L a j.2 ≠ 0 := by
      intro j hj
      rw [hs, Finset.mem_filter] at hj
      have hj1 := hj.1
      simp only [hs0, Finset.mem_sigma, Finset.mem_sdiff, Finset.mem_powerset,
        Finset.mem_singleton, Finset.mem_filter] at hj1
      exact ⟨hj1.1.1, hj1.1.2, hj1.2.1, hj1.2.2, hj.2⟩
    have hG : ∀ y ∈ Y, gCol (c y) n Φ U S I L a X = mCol (c y) n Φ U S I L a X -
        ∑ j ∈ s, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i ^ 2) *
          gCol (c y) n Φ (U \ j.2) (S \ j.2) (I \ j.1) L a (X / ∏ i ∈ j.2, n i ^ 2) := by
      intro y _
      have h := mCol_sub_gCol (c y) n Φ U S hUS hn' I L a X
      rw [Finset.sum_sigma'] at h
      have e : ∑ j ∈ s0, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i ^ 2) *
          gCol (c y) n Φ (U \ j.2) (S \ j.2) (I \ j.1) L a (X / ∏ i ∈ j.2, n i ^ 2) =
          ∑ j ∈ s0, primeMarkInj j.1 L a j.2 * ((∏ i ∈ j.2, c y i ^ 2) *
          gCol (c y) n Φ (U \ j.2) (S \ j.2) (I \ j.1) L a (X / ∏ i ∈ j.2, n i ^ 2)) :=
        Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
      have ef : ∑ j ∈ s, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i ^ 2) *
          gCol (c y) n Φ (U \ j.2) (S \ j.2) (I \ j.1) L a (X / ∏ i ∈ j.2, n i ^ 2) =
          ∑ j ∈ s0, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i ^ 2) *
          gCol (c y) n Φ (U \ j.2) (S \ j.2) (I \ j.1) L a (X / ∏ i ∈ j.2, n i ^ 2) := by
        rw [hs]
        apply Finset.sum_filter_of_ne
        intro j _ hne hm
        apply hne
        rw [hm, zero_mul, zero_mul]
      rw [ef, e, hs0, ← h]; ring
    have hrec := rec_step Y (fun y => gCol (c y) n Φ U S I L a X)
      (fun y => mCol (c y) n Φ U S I L a X) s
      (fun j y => primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i ^ 2)
      (fun j y => gCol (c y) n Φ (U \ j.2) (S \ j.2) (I \ j.1) L a (X / ∏ i ∈ j.2, n i ^ 2))
      (fun j => ‖primeMarkInj j.1 L a j.2‖ * ∏ i ∈ j.2, κ i ^ 2)
      (fun j _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => sq_nonneg _))
      (by
        intro j _ y hy
        rw [norm_mul, norm_prod]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        intro i _
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hc y hy i) 2)
      hG Mb (lamA A (I.card - 1) * Mb) ((1 + A)^I.card)
      (mul_nonneg (le_trans zero_le_one (one_le_lamA A hA0 _)) hMb0)
      (by rwa [Finset.inter_eq_left.mpr hUS] at hMtop)
      (by
        intro j hj
        obtain ⟨hFI, hFne, hBU, hBF, hmark⟩ := hmem j hj
        have hFpos : 1 ≤ j.1.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hFne)
        have hIF : (I \ j.1).card + j.1.card = I.card := Finset.card_sdiff_add_card_eq_card hFI
        have hBS : j.2 ⊆ S := hBU.trans hUS
        have hP : 1 ≤ ∏ i ∈ j.2, n i ^ 2 :=
          one_le_prod_n (fun i => n i ^ 2) (fun i => one_le_pow₀ (hn i)) j.2
        have hX2 : 0 < X / ∏ i ∈ j.2, n i ^ 2 := div_pos hX (lt_of_lt_of_le one_pos hP)
        have hFP : ∏ i ∈ j.1, h i ≤ ∏ i ∈ j.2, n i ^ 2 := by
          refine (prod_le_of_mark_ne_zero L a n h hn j.1 j.2 (fun i hi => hh0 i (hFI hi))
            (fun i hi => hhn i (hFI hi)) hmark).trans ?_
          apply Finset.prod_le_prod₀ (fun i _ => le_trans zero_le_one (hn i))
          intro i _
          nlinarith [hn i]
        have hcall := ih (I \ j.1) (by omega)
          (fun i hi => hA i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hh0 i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hhn i (Finset.mem_sdiff.mp hi).1) (U \ j.2) (S \ j.2)
          (Finset.sdiff_subset_sdiff hUS le_rfl) _ hX2 (by
            intro I'' hI'' S'' hS'' hcard X'' hX'' hX''le
            have hSc1 := Finset.card_sdiff_add_card_eq_card (hS''.trans Finset.sdiff_subset)
            have hSc2 := Finset.card_sdiff_add_card_eq_card hS''
            have hSc3 := Finset.card_sdiff_add_card_eq_card hBS
            have heq : (U \ j.2) ∩ S'' = U ∩ S'' := by
              ext x
              simp only [Finset.mem_inter, Finset.mem_sdiff]
              constructor
              · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
              · rintro ⟨h1, h3⟩
                exact ⟨⟨h1, (Finset.mem_sdiff.mp (hS'' h3)).2⟩, h3⟩
            rw [heq]
            apply hM I'' (hI''.trans Finset.sdiff_subset) S''
              (hS''.trans Finset.sdiff_subset) (by omega) X'' hX''
            exact scale_step h I j.1 I'' hFI hI'' hh0 X X'' _ (lt_of_lt_of_le one_pos hP) hFP
              hX''le hX.le)
        refine hcall.trans (mul_le_mul_of_nonneg_right ?_ hMb0)
        apply lamA_mono A hA0
        omega)
      (by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => sq_nonneg _)))
          ?_
        rw [hs0, ← Finset.sum_sigma' (I.powerset \ {∅})
          (fun F => U.powerset.filter (fun B => B.card = F.card))
          (fun F B => ‖primeMarkInj F L a B‖ * ∏ i ∈ B, κ i ^ 2)]
        apply mass_powerset_le I _ A hA0
        · intro F hF
          refine (frozen_mass_le L a (fun i => κ i ^ 2) (fun i => sq_nonneg _) F U).trans ?_
          rw [← Finset.prod_const]
          apply Finset.prod_le_prod₀
          · intro i _
            exact Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)
          · intro i hi
            refine le_trans ?_ (hA i (hF hi))
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro p _ _
            exact mul_nonneg (norm_nonneg _) (sq_nonneg _)
        · intro F _
          exact Finset.sum_nonneg fun B _ =>
            mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => sq_nonneg _))
    exact hrec.trans (lamA_step A hA0 I.card hIpos Mb hMb0)

/-! ## Column side: restoring avoided column primes in the main columns -/

theorem mCol_avoid_finite (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hΦ : ∀ x, b < x → Φ x = 0) (hn : ∀ i, 1 ≤ n i) (U S : Finset ι) (I : Finset σ)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (p : ι) (hp : p ∉ S)
    (J : ℕ) (X : ℝ) (hX : 0 < X) (hJ : b * X < n p ^ J) :
    mCol c n Φ U S I L a X =
      ∑ j ∈ Finset.range J, (-c p)^j * mCol c n Φ U (insert p S) I L a (X / n p ^ j) := by
  unfold mCol
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  have hP := one_le_prod_n n hn T
  have hP0 : 0 < ∏ i ∈ T, n i := lt_of_lt_of_le one_pos hP
  have hJ' : b * (X / ∏ i ∈ T, n i) < n p ^ J :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (div_le_self hX.le hP) hb) hJ
  rw [col_avoid_finite c n Φ b hΦ hn S p hp J _ (div_pos hX hP0) hJ', Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_right_comm]
  ring

theorem mCol_moment_avoid_one (c : ρ → ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hΦ : ∀ x, b < x → Φ x = 0) (hn : ∀ i, 1 ≤ n i) (Y : Finset ρ) (U S : Finset ι)
    (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (p : ι)
    (hp : p ∉ S) (hnp : 1 < n p) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ < 1)
    (hc : ∀ y ∈ Y, ‖c y p‖ ≤ κ) (X B : ℝ)
    (hB : ∀ s, 0 < s → s ≤ X → ∑ y ∈ Y, ‖mCol (c y) n Φ U (insert p S) I L a s‖^2 ≤ B) :
    ∀ s, 0 < s → s ≤ X → ∑ y ∈ Y, ‖mCol (c y) n Φ U S I L a s‖^2 ≤ ((1-κ)⁻¹)^2 * B := by
  intro s hs hsX
  have hB0 : 0 ≤ B := (Finset.sum_nonneg fun y _ => sq_nonneg _).trans (hB s hs hsX)
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (b * s) hnp
  have hnp0 : 0 < n p := lt_trans one_pos hnp
  set G := ∑ j ∈ Finset.range J, κ^j with hG
  have hG0 : 0 ≤ G := Finset.sum_nonneg fun j _ => pow_nonneg hκ0 j
  have hGle : G ≤ (1-κ)⁻¹ := geom_real_le κ hκ0 hκ J
  have hscale : ∀ j, 0 < s / n p ^ j ∧ s / n p ^ j ≤ X := by
    intro j
    have hpj : 1 ≤ n p ^ j := one_le_pow₀ hnp.le
    exact ⟨div_pos hs (pow_pos hnp0 j), (div_le_self hs.le hpj).trans hsX⟩
  have hy : ∀ y ∈ Y, ‖mCol (c y) n Φ U S I L a s‖^2 ≤
      G * ∑ j ∈ Finset.range J, κ^j * ‖mCol (c y) n Φ U (insert p S) I L a (s / n p ^ j)‖^2 := by
    intro y hyY
    rw [mCol_avoid_finite (c y) n Φ b hb hΦ hn U S I L a p hp J s hs hJ]
    apply norm_sum_sq_le_weighted
    intro j _
    rw [norm_pow, norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (hc y hyY) j
  calc ∑ y ∈ Y, ‖mCol (c y) n Φ U S I L a s‖^2
      ≤ ∑ y ∈ Y, G * ∑ j ∈ Finset.range J,
          κ^j * ‖mCol (c y) n Φ U (insert p S) I L a (s / n p ^ j)‖^2 := Finset.sum_le_sum hy
    _ = G * ∑ j ∈ Finset.range J,
          κ^j * ∑ y ∈ Y, ‖mCol (c y) n Φ U (insert p S) I L a (s / n p ^ j)‖^2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ ≤ G * ∑ j ∈ Finset.range J, κ^j * B := by
        apply mul_le_mul_of_nonneg_left _ hG0
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hB _ (hscale j).1 (hscale j).2) (pow_nonneg hκ0 j)
    _ = G * G * B := by rw [← Finset.sum_mul]; ring
    _ ≤ (1-κ)⁻¹ * (1-κ)⁻¹ * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact mul_le_mul hGle hGle hG0 (hG0.trans hGle)
    _ = ((1-κ)⁻¹)^2 * B := by ring

/-- **Restoring a set `T` of avoided column primes** in the main columns. -/
theorem mCol_moment_avoid (c : ρ → ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hΦ : ∀ x, b < x → Φ x = 0) (hn : ∀ i, 1 ≤ n i) (Y : Finset ρ) (U : Finset ι)
    (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (κ : ι → ℝ)
    (T : Finset ι) (hT : ∀ p ∈ T, 1 < n p ∧ 0 ≤ κ p ∧ κ p < 1 ∧ ∀ y ∈ Y, ‖c y p‖ ≤ κ p)
    (S : Finset ι) (hST : Disjoint S T) (X B : ℝ)
    (hB : ∀ s, 0 < s → s ≤ X → ∑ y ∈ Y, ‖mCol (c y) n Φ U (S ∪ T) I L a s‖^2 ≤ B) :
    ∀ s, 0 < s → s ≤ X →
      ∑ y ∈ Y, ‖mCol (c y) n Φ U S I L a s‖^2 ≤ (∏ p ∈ T, ((1-κ p)⁻¹)^2) * B := by
  induction T using Finset.induction_on generalizing S B with
  | empty => simpa using hB
  | @insert p T hpT ih =>
    have hp := hT p (Finset.mem_insert_self p T)
    have hT' : ∀ q ∈ T, 1 < n q ∧ 0 ≤ κ q ∧ κ q < 1 ∧ ∀ y ∈ Y, ‖c y q‖ ≤ κ q :=
      fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have hpS : p ∉ S := fun h => Finset.disjoint_left.mp hST h (Finset.mem_insert_self p T)
    have hST' : Disjoint (insert p S) T := by
      rw [Finset.disjoint_insert_left]
      exact ⟨hpT, Finset.disjoint_of_subset_right (Finset.subset_insert p T) hST⟩
    have hB' : ∀ s, 0 < s → s ≤ X →
        ∑ y ∈ Y, ‖mCol (c y) n Φ U (insert p S ∪ T) I L a s‖^2 ≤ B := by
      intro s hs hsX
      have : insert p S ∪ T = S ∪ insert p T := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      rw [this]; exact hB s hs hsX
    have h1 := ih hT' (insert p S) hST' B hB'
    have h2 := mCol_moment_avoid_one c n Φ b hb hΦ hn Y U S I L a p hpS hp.1 (κ p) hp.2.1
      hp.2.2.1 hp.2.2.2 X _ h1
    intro s hs hsX
    rw [Finset.prod_insert hpT]
    calc _ ≤ ((1-κ p)⁻¹)^2 * ((∏ q ∈ T, ((1-κ q)⁻¹)^2) * B) := h2 s hs hsX
      _ = _ := by ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.gCol_moment_le
#print axioms Qrh.MarkedAnchor.Inverse.Restore.mCol_moment_avoid
