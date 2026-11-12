/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Bound

/-!
# Inverse.Restore.Tuple — restoring primes forbidden to the tuples; the combined bound

* `mCol_tuple_split`: splitting the exact image `T` of the tuple into `B = T ∩ V` and
  `T \ V` (`Split.primeMarkInj_split`):
  `mCol U S I X = ∑_{F ⊆ I} ∑_{B ⊆ U ∩ V, |B| = |F|} mark_F(B) (∏_B c) mCol (U \ V) S (I \ F) (X/∏_B n)`.
* **`mCol_avoid_tuple_le`**: the moment of `mCol (U \ V) S I` is `≤ lamA #V |I|` times the
  moments of `mCol U S I'` (`I' ⊆ I`), for `κ ≤ 1`, `‖a‖ ≤ 1`.
* **`gCol_full_moment_le`**: the physical exact-image column `gCol S S I X` on a sub-pool
  `S ⊆ S0` is bounded by the main columns `mCol S0 S0 I' X'` on the full pool `S0`, with the
  constant `lamA A |I| · 12^(v+|I|) · lamA (v+|I|) |I|`, `v = #(S0 \ S)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators

variable {σ ι ρ : Type*} [DecidableEq ι]

theorem card_sdiff_add_card_inter' (T V : Finset ι) : (T \ V).card + (T ∩ V).card = T.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]; tauto
  · rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2

/-- Tuple split along a set `V`. -/
theorem mCol_tuple_split (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U V S : Finset ι)
    (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    mCol c n Φ U S I L a X =
      ∑ F ∈ I.powerset, ∑ B ∈ (U ∩ V).powerset.filter (fun B => B.card = F.card),
        primeMarkInj F L a B * ((∏ i ∈ B, c i) *
          mCol c n Φ (U \ V) S (I \ F) L a (X / ∏ i ∈ B, n i)) := by
  unfold mCol
  have h1 : ∀ T ∈ U.powerset.filter (fun T => T.card = I.card),
      primeMarkInj I L a T * ((∏ i ∈ T, c i) * col c n Φ S (X / ∏ i ∈ T, n i)) =
      ∑ F ∈ I.powerset.filter (fun F => F.card = (T ∩ V).card),
        primeMarkInj F L a (T ∩ V) * primeMarkInj (I \ F) L a (T \ (T ∩ V)) *
          ((∏ i ∈ T, c i) * col c n Φ S (X / ∏ i ∈ T, n i)) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    rw [primeMarkInj_split I L a T (T ∩ V) Finset.inter_subset_left hT.2, Finset.sum_mul]
  rw [Finset.sum_congr rfl h1]
  have hsw : ∀ T F, T ∈ U.powerset.filter (fun T => T.card = I.card) ∧
      F ∈ I.powerset.filter (fun F => F.card = (T ∩ V).card) ↔
      T ∈ (U.powerset.filter (fun T => T.card = I.card)).filter
        (fun T => (T ∩ V).card = F.card) ∧ F ∈ I.powerset := by
    intro T F
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h4.symm⟩, h3⟩
    · rintro ⟨⟨⟨h1, h2⟩, h4⟩, h3⟩; exact ⟨⟨h1, h2⟩, h3, h4.symm⟩
  rw [Finset.sum_comm' hsw]
  apply Finset.sum_congr rfl
  intro F hF
  have hFI : F ⊆ I := Finset.mem_powerset.mp hF
  have hIF : (I \ F).card + F.card = I.card := Finset.card_sdiff_add_card_eq_card hFI
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product']
  apply Finset.sum_nbij' (fun T => (T ∩ V, T \ V)) (fun x => x.1 ∪ x.2)
  · intro T hT
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hT ⊢
    have hc := card_sdiff_add_card_inter' T V
    refine ⟨⟨Finset.inter_subset_inter_right hT.1.1, hT.2⟩,
      Finset.sdiff_subset_sdiff hT.1.1 le_rfl, ?_⟩
    omega
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hx ⊢
    obtain ⟨⟨hB1, hB2⟩, hT1, hT2⟩ := hx
    have hd : Disjoint x.1 x.2 := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      exact (Finset.mem_sdiff.mp (hT1 hy2)).2 (Finset.mem_inter.mp (hB1 hy1)).2
    have hBV : (x.1 ∪ x.2) ∩ V = x.1 := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hv⟩
        · exact h
        · exact absurd hv (Finset.mem_sdiff.mp (hT1 h)).2
      · intro h; exact ⟨Or.inl h, (Finset.mem_inter.mp (hB1 h)).2⟩
    refine ⟨⟨Finset.union_subset (hB1.trans Finset.inter_subset_left)
      (hT1.trans Finset.sdiff_subset), ?_⟩, ?_⟩
    · rw [Finset.card_union_of_disjoint hd]; omega
    · rw [hBV]; exact hB2
  · intro T _
    ext y; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset, Finset.mem_product] at hx
    obtain ⟨⟨hB1, _⟩, hT1, _⟩ := hx
    ext y
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hv⟩
        · exact h
        · exact absurd hv (Finset.mem_sdiff.mp (hT1 h)).2
      · intro h; exact ⟨Or.inl h, (Finset.mem_inter.mp (hB1 h)).2⟩
    · simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hv⟩
        · exact absurd (Finset.mem_inter.mp (hB1 h)).2 hv
        · exact h
      · intro h; exact ⟨Or.inr h, (Finset.mem_sdiff.mp (hT1 h)).2⟩
  · intro T _
    have e1 : T \ (T ∩ V) = T \ V := by
      ext y; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    have e2 : ∏ i ∈ T, c i = (∏ i ∈ T ∩ V, c i) * ∏ i ∈ T \ V, c i :=
      (Finset.prod_inter_mul_prod_diff T V c).symm
    have e3 : ∏ i ∈ T, n i = (∏ i ∈ T ∩ V, n i) * ∏ i ∈ T \ V, n i :=
      (Finset.prod_inter_mul_prod_diff T V n).symm
    simp only
    rw [e1, e2, e3, ← div_div]
    ring

/-- The `F = ∅` term of the split is the avoided main column. -/
theorem mCol_tuple_split' (c : ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (U V S : Finset ι)
    (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (X : ℝ) :
    mCol c n Φ (U \ V) S I L a X = mCol c n Φ U S I L a X -
      ∑ F ∈ I.powerset \ {∅}, ∑ B ∈ (U ∩ V).powerset.filter (fun B => B.card = F.card),
        primeMarkInj F L a B * ((∏ i ∈ B, c i) *
          mCol c n Φ (U \ V) S (I \ F) L a (X / ∏ i ∈ B, n i)) := by
  rw [mCol_tuple_split c n Φ U V S I L a X,
    ← Finset.sum_sdiff (s₁ := ({∅} : Finset (Finset σ)))
      (Finset.singleton_subset_iff.mpr (Finset.empty_mem_powerset I)), Finset.sum_singleton]
  have h0 : ∑ B ∈ (U ∩ V).powerset.filter (fun B => B.card = (∅ : Finset σ).card),
      primeMarkInj (∅ : Finset σ) L a B * ((∏ i ∈ B, c i) *
        mCol c n Φ (U \ V) S (I \ ∅) L a (X / ∏ i ∈ B, n i)) = mCol c n Φ (U \ V) S I L a X := by
    rw [sum_card_empty (U ∩ V) (fun B => primeMarkInj (∅ : Finset σ) L a B * ((∏ i ∈ B, c i) *
        mCol c n Φ (U \ V) S (I \ ∅) L a (X / ∏ i ∈ B, n i)))]
    simp [primeMarkInj_empty_slots]
  rw [h0]; ring

/-- **Restoring primes forbidden to the tuples.** The main columns are needed only at the scales
reduced by the removed slots (`X' · ∏_{I \ I'} h ≤ X`, slot floors `h i ≤ n p` on `L i`). -/
theorem mCol_avoid_tuple_le (Y : Finset ρ) (c : ρ → ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ)
    (L : σ → Finset ι) (a : σ → ι → ℂ) (κ : ι → ℝ) (hn : ∀ i, 1 ≤ n i)
    (hκ0 : ∀ p, 0 ≤ κ p) (hκ1 : ∀ p, κ p ≤ 1) (hc : ∀ y ∈ Y, ∀ p, ‖c y p‖ ≤ κ p)
    (U V S : Finset ι) (Mb : ℝ) (h : σ → ℝ) :
    ∀ (k : ℕ) (I : Finset σ), I.card ≤ k → (∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) →
    (∀ i ∈ I, 0 ≤ h i) → (∀ i ∈ I, ∀ p ∈ L i, h i ≤ n p) →
    ∀ X : ℝ, 0 < X →
    (∀ I' ⊆ I, ∀ X' : ℝ, 0 < X' → X' * ∏ i ∈ I \ I', h i ≤ X →
      ∑ y ∈ Y, ‖mCol (c y) n Φ U S I' L a X'‖^2 ≤ Mb) →
    ∑ y ∈ Y, ‖mCol (c y) n Φ (U \ V) S I L a X‖^2 ≤ lamA V.card I.card * Mb := by
  have hA0 : (0 : ℝ) ≤ V.card := Nat.cast_nonneg _
  have hempty : ∀ X : ℝ, 0 < X →
      (∀ I' ⊆ (∅ : Finset σ), ∀ X' : ℝ, 0 < X' → X' * ∏ i ∈ (∅ : Finset σ) \ I', h i ≤ X →
        ∑ y ∈ Y, ‖mCol (c y) n Φ U S I' L a X'‖^2 ≤ Mb) →
      ∑ y ∈ Y, ‖mCol (c y) n Φ (U \ V) S (∅ : Finset σ) L a X‖^2 ≤
        lamA V.card (∅ : Finset σ).card * Mb := by
    intro X hX hM
    have h := hM ∅ (Finset.empty_subset _) X hX (by simp)
    simp only [mCol_empty] at h ⊢
    simpa [lamA] using h
  intro k
  induction k with
  | zero =>
    intro I hI _ _ _ X hX hM
    have hI0 : I = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hI)
    subst hI0
    exact hempty X hX hM
  | succ k ih =>
    intro I hI ha hh0 hhn X hX hM
    by_cases hIe : I = ∅
    · subst hIe
      exact hempty X hX hM
    have hIpos : 1 ≤ I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hIe)
    have hMtop := hM I (subset_refl I) X hX (by rw [prod_sdiff_self_one, mul_one])
    have hMb0 : 0 ≤ Mb := le_trans (Finset.sum_nonneg (fun y _ => sq_nonneg _)) hMtop
    set s0 := (I.powerset \ {∅}).sigma
      (fun F => (U ∩ V).powerset.filter (fun B => B.card = F.card)) with hs0
    set s := s0.filter (fun j => primeMarkInj j.1 L a j.2 ≠ 0) with hs
    have hmem : ∀ j ∈ s, j.1 ⊆ I ∧ j.1 ≠ ∅ ∧ j.2 ⊆ U ∩ V ∧ j.2.card = j.1.card ∧
        primeMarkInj j.1 L a j.2 ≠ 0 := by
      intro j hj
      rw [hs, Finset.mem_filter] at hj
      have hj1 := hj.1
      simp only [hs0, Finset.mem_sigma, Finset.mem_sdiff, Finset.mem_powerset,
        Finset.mem_singleton, Finset.mem_filter] at hj1
      exact ⟨hj1.1.1, hj1.1.2, hj1.2.1, hj1.2.2, hj.2⟩
    have hG : ∀ y ∈ Y, mCol (c y) n Φ (U \ V) S I L a X = mCol (c y) n Φ U S I L a X -
        ∑ j ∈ s, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i) *
          mCol (c y) n Φ (U \ V) S (I \ j.1) L a (X / ∏ i ∈ j.2, n i) := by
      intro y _
      have h := mCol_tuple_split' (c y) n Φ U V S I L a X
      rw [Finset.sum_sigma'] at h
      have e : ∑ j ∈ s0, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i) *
          mCol (c y) n Φ (U \ V) S (I \ j.1) L a (X / ∏ i ∈ j.2, n i) =
          ∑ j ∈ s0, primeMarkInj j.1 L a j.2 * ((∏ i ∈ j.2, c y i) *
          mCol (c y) n Φ (U \ V) S (I \ j.1) L a (X / ∏ i ∈ j.2, n i)) :=
        Finset.sum_congr rfl (fun _ _ => mul_assoc _ _ _)
      have ef : ∑ j ∈ s, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i) *
          mCol (c y) n Φ (U \ V) S (I \ j.1) L a (X / ∏ i ∈ j.2, n i) =
          ∑ j ∈ s0, (primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i) *
          mCol (c y) n Φ (U \ V) S (I \ j.1) L a (X / ∏ i ∈ j.2, n i) := by
        rw [hs]
        apply Finset.sum_filter_of_ne
        intro j _ hne hm
        apply hne
        rw [hm, zero_mul, zero_mul]
      rw [ef, e, hs0, h]
    have hrec := rec_step Y (fun y => mCol (c y) n Φ (U \ V) S I L a X)
      (fun y => mCol (c y) n Φ U S I L a X) s
      (fun j y => primeMarkInj j.1 L a j.2 * ∏ i ∈ j.2, c y i)
      (fun j y => mCol (c y) n Φ (U \ V) S (I \ j.1) L a (X / ∏ i ∈ j.2, n i))
      (fun j => ‖primeMarkInj j.1 L a j.2‖ * ∏ i ∈ j.2, κ i)
      (fun j _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => hκ0 i))
      (by
        intro j _ y hy
        rw [norm_mul, norm_prod]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hc y hy i))
      hG Mb (lamA V.card (I.card - 1) * Mb) ((1 + (V.card : ℝ))^I.card)
      (mul_nonneg (le_trans zero_le_one (one_le_lamA _ hA0 _)) hMb0)
      hMtop
      (by
        intro j hj
        obtain ⟨hFI, hFne, _, _, hmark⟩ := hmem j hj
        have hFpos : 1 ≤ j.1.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hFne)
        have hIF : (I \ j.1).card + j.1.card = I.card := Finset.card_sdiff_add_card_eq_card hFI
        have hP : 1 ≤ ∏ i ∈ j.2, n i := one_le_prod_n n hn j.2
        have hX2 : 0 < X / ∏ i ∈ j.2, n i := div_pos hX (lt_of_lt_of_le one_pos hP)
        have hFP : ∏ i ∈ j.1, h i ≤ ∏ i ∈ j.2, n i :=
          prod_le_of_mark_ne_zero L a n h hn j.1 j.2 (fun i hi => hh0 i (hFI hi))
            (fun i hi => hhn i (hFI hi)) hmark
        have hcall := ih (I \ j.1) (by omega)
          (fun i hi => ha i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hh0 i (Finset.mem_sdiff.mp hi).1)
          (fun i hi => hhn i (Finset.mem_sdiff.mp hi).1) _ hX2 (by
            intro I'' hI'' X'' hX'' hX''le
            exact hM I'' (hI''.trans Finset.sdiff_subset) X'' hX''
              (scale_step h I j.1 I'' hFI hI'' hh0 X X'' _ (lt_of_lt_of_le one_pos hP) hFP
                hX''le hX.le))
        refine hcall.trans (mul_le_mul_of_nonneg_right ?_ hMb0)
        apply lamA_mono _ hA0
        omega)
      (by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => hκ0 i))) ?_
        rw [hs0, ← Finset.sum_sigma' (I.powerset \ {∅})
          (fun F => (U ∩ V).powerset.filter (fun B => B.card = F.card))
          (fun F B => ‖primeMarkInj F L a B‖ * ∏ i ∈ B, κ i)]
        apply mass_powerset_le I _ _ hA0
        · intro F hF
          refine (frozen_mass_le L a κ hκ0 F (U ∩ V)).trans ?_
          rw [← Finset.prod_const]
          apply Finset.prod_le_prod₀
          · intro i _
            exact Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (hκ0 p)
          · intro i hi
            calc ∑ p ∈ (L i).filter (· ∈ U ∩ V), ‖a i p‖ * κ p
                ≤ ∑ p ∈ (L i).filter (· ∈ U ∩ V), (1 : ℝ) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  have h1 := ha i (hF hi) p (Finset.mem_filter.mp hp).1
                  have h2 := hκ1 p
                  have h3 := hκ0 p
                  nlinarith [norm_nonneg (a i p)]
              _ = (((L i).filter (· ∈ U ∩ V)).card : ℝ) := by simp
              _ ≤ V.card := by
                  apply Nat.cast_le.mpr
                  apply Finset.card_le_card
                  intro p hp
                  exact (Finset.mem_inter.mp (Finset.mem_filter.mp hp).2).2
        · intro F _
          exact Finset.sum_nonneg fun B _ =>
            mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => hκ0 i))
    exact hrec.trans (lamA_step _ hA0 I.card hIpos Mb hMb0)

/-- **The physical exact-image column on a sub-pool is bounded by the full main columns** at the
scales reduced by the removed slots. -/
theorem gCol_full_moment_le (Y : Finset ρ) (c : ρ → ι → ℂ) (n : ι → ℝ) (Φ : ℝ → ℂ) (b : ℝ)
    (hb : 0 ≤ b) (hΦ : ∀ x, b < x → Φ x = 0) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (κ : ι → ℝ) (hn1 : ∀ i, 1 < n i) (hκ0 : ∀ p, 0 ≤ κ p) (hκ1 : ∀ p, κ p ^ 2 ≤ 1/2)
    (hc : ∀ y ∈ Y, ∀ p, ‖c y p‖ ≤ κ p) (A : ℝ) (hA0 : 0 ≤ A)
    (I : Finset σ) (hA : ∀ i ∈ I, ∑ p ∈ L i, ‖a i p‖ * κ p ^ 2 ≤ A)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) (h : σ → ℝ) (hh0 : ∀ i ∈ I, 0 ≤ h i)
    (hhn : ∀ i ∈ I, ∀ p ∈ L i, h i ≤ n p)
    (S0 S : Finset ι) (hS : S ⊆ S0) (X : ℝ) (hX : 0 < X) (Mb : ℝ)
    (hM : ∀ I' ⊆ I, ∀ X' : ℝ, 0 < X' → X' * ∏ i ∈ I \ I', h i ≤ X →
      ∑ y ∈ Y, ‖mCol (c y) n Φ S0 S0 I' L a X'‖^2 ≤ Mb) :
    ∑ y ∈ Y, ‖gCol (c y) n Φ S S I L a X‖^2 ≤
      lamA A I.card * (12^((S0 \ S).card + I.card) *
        (lamA ((S0 \ S).card + I.card : ℕ) I.card * Mb)) := by
  have hn : ∀ i, 1 ≤ n i := fun i => (hn1 i).le
  have hk7 : ∀ p, κ p ≤ 7072/10000 := fun p => by nlinarith [hκ1 p, hκ0 p]
  have hMb0 : 0 ≤ Mb := le_trans (Finset.sum_nonneg (fun y _ => sq_nonneg _))
    (hM I (subset_refl I) X hX (by rw [prod_sdiff_self_one, mul_one]))
  set v := (S0 \ S).card + I.card with hv
  apply gCol_moment_le Y c n Φ L a κ hn hκ0 hc A hA0 _ h I.card I le_rfl hA hh0 hhn S S
    (subset_refl S) X hX
  intro I' hI' S' hS' hcard X' hX' hX'le
  rw [Finset.inter_eq_right.mpr hS']
  have hS'0 : S' ⊆ S0 := hS'.trans hS
  have hc1 := Finset.card_sdiff_add_card_eq_card hS'0
  have hc2 := Finset.card_sdiff_add_card_eq_card hS
  have hc3 := Finset.card_sdiff_add_card_eq_card hS'
  have hT : (S0 \ S').card ≤ v := by
    have : I'.card ≤ I.card := Finset.card_le_card hI'
    rw [hv]; omega
  have hI'c : I'.card ≤ I.card := Finset.card_le_card hI'
  have hR0 : 0 ≤ ∏ i ∈ I \ I', h i :=
    Finset.prod_nonneg fun i hi => hh0 i (Finset.mem_sdiff.mp hi).1
  -- tuple side, then column side
  have hB := mCol_avoid_tuple_le Y c n Φ L a κ hn hκ0 (fun p => (hk7 p).trans (by norm_num)) hc
    S0 (S0 \ S') S0 Mb h I'.card I' le_rfl (fun i hi => ha i (hI' hi))
    (fun i hi => hh0 i (hI' hi)) (fun i hi => hhn i (hI' hi))
  rw [Finset.sdiff_sdiff_eq_self hS'0] at hB
  have hC := mCol_moment_avoid c n Φ b hb hΦ hn Y S' I' L a κ (S0 \ S')
    (fun p _ => ⟨hn1 p, hκ0 p, (hk7 p).trans_lt (by norm_num), fun y hy => hc y hy p⟩)
    S' Finset.disjoint_sdiff X' (lamA (S0 \ S').card I'.card * Mb) (by
      intro s hs hsX
      rw [Finset.union_sdiff_of_subset hS'0]
      exact hB s hs (fun I'' hI'' X'' hX'' hX''le => hM I'' (hI''.trans hI') X'' hX'' (by
        have hsplit : ∏ i ∈ I \ I'', h i = (∏ i ∈ I' \ I'', h i) * ∏ i ∈ I \ I', h i := by
          have hsub : I' \ I'' ⊆ I \ I'' := Finset.sdiff_subset_sdiff hI' le_rfl
          have hdiff : (I \ I'') \ (I' \ I'') = I \ I' := by
            ext x; simp only [Finset.mem_sdiff]; have := @hI'' x; tauto
          rw [← Finset.prod_sdiff hsub, hdiff, mul_comm]
        rw [hsplit, ← mul_assoc]
        calc (X'' * ∏ i ∈ I' \ I'', h i) * ∏ i ∈ I \ I', h i ≤ s * ∏ i ∈ I \ I', h i :=
              mul_le_mul_of_nonneg_right hX''le hR0
          _ ≤ X' * ∏ i ∈ I \ I', h i := mul_le_mul_of_nonneg_right hsX hR0
          _ ≤ X := hX'le)))
    X' hX' le_rfl
  refine hC.trans ?_
  have h12 : ∀ p ∈ S0 \ S', ((1 - κ p)⁻¹)^2 ≤ 12 := by
    intro p _
    have h1 : 2928/10000 ≤ 1 - κ p := by linarith [hk7 p]
    have h2 : (1 - κ p)⁻¹ ≤ 10000/2928 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h3 : 0 ≤ (1 - κ p)⁻¹ := inv_nonneg.mpr (by linarith)
    nlinarith
  have hprod : ∏ p ∈ S0 \ S', ((1 - κ p)⁻¹)^2 ≤ 12^v := by
    calc ∏ p ∈ S0 \ S', ((1 - κ p)⁻¹)^2 ≤ ∏ _p ∈ S0 \ S', (12 : ℝ) :=
          Finset.prod_le_prod₀ (fun p _ => sq_nonneg _) h12
      _ = 12^(S0 \ S').card := Finset.prod_const _
      _ ≤ 12^v := pow_le_pow_right₀ (by norm_num) hT
  have hlam : lamA (S0 \ S').card I'.card ≤ lamA (v : ℕ) I.card := by
    refine (lamA_mono_left (Nat.cast_nonneg _) (Nat.cast_le.mpr hT) _).trans ?_
    exact lamA_mono _ (Nat.cast_nonneg _) hI'c
  have hl0 : 0 ≤ lamA (S0 \ S').card I'.card :=
    le_trans zero_le_one (one_le_lamA _ (Nat.cast_nonneg _) _)
  calc (∏ p ∈ S0 \ S', ((1 - κ p)⁻¹)^2) * (lamA (S0 \ S').card I'.card * Mb)
      ≤ 12^v * (lamA (S0 \ S').card I'.card * Mb) :=
        mul_le_mul_of_nonneg_right hprod (mul_nonneg hl0 hMb0)
    _ ≤ 12^v * (lamA (v : ℕ) I.card * Mb) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hlam hMb0

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mCol_avoid_tuple_le
#print axioms Qrh.MarkedAnchor.Inverse.Restore.gCol_full_moment_le
