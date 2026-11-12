/- Copyright (c) 2026 Sil. Apache-2.0.
`energy_le_support` is adapted from sil-density-split `Density/LeafRows.lean` (`energy_le_classes`,
Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafContract

/-!
# High.BranchAux

Bookkeeping for `high_branch_mesh`:
* `energy_le_support`: the packed energy is at most `diag Φ · ∑_{z ∈ G} ‖row z‖²` over a finite set
  `G` of kept rows of nonzero weight;
* `posSlots`, `liftPos`, `prod_split_pos`: the positive-width slots of a slot set as a `Finset α`,
  and the splitting of a product over all slots;
* `prod_rpow_slots`: `∏ₖ (A·Z^(ν wₖ)) = A^card · Z^(ν ∑ w)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy ConcreteTraceCRT
open QRH.SilDensitySplit.Density
local notation "O" => HeckeFamily.O

section Energy
variable {ι : Type*} [Fintype ι]

/-- The packed energy over a finite support. -/
theorem energy_le_support (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K b : ℝ)
    (hΦ : ∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/K)).re) (hK : 0 < K)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic b) :
    ∃ G : Finset O, (∀ z ∈ G, keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0) ∧
      energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≤
        QuadraticInitialBound.diagonalControl Φ *
          ∑ z ∈ G, ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (b*K)
  set B := ShortDraftLatticeCount.rowNormBall N₀
  let f : O → ℝ := fun z => if keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0
  have hout : ∀ z, Φ (‖eisEmbedding z‖^2/K) ≠ 0 → z ∈ B := by
    intro z hn
    have hh : ‖eisEmbedding z‖^2 ≤ (N₀:ℝ) := ((div_le_iff₀ hK).mp (hs hn)).trans hN₀
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    exact_mod_cast (show ((Ideal.span {z}).absNorm:ℝ) ≤ N₀ by
      rwa [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span])
  let G : Finset O := B.filter (fun z => keep z ∧ Φ (‖eisEmbedding z‖^2/K) ≠ 0)
  have hzero : ∀ z ∉ G, f z = 0 := by
    intro z hz
    dsimp only [f]
    by_cases hk : keep z
    · by_cases hp : Φ (‖eisEmbedding z‖^2/K) = 0
      · simp [hk, hp]
      · exact absurd (Finset.mem_filter.mpr ⟨hout z hp, hk, hp⟩) hz
    · simp [hk]
  have he : energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K = ∑ z ∈ G, f z := by
    unfold energy
    exact tsum_eq_sum (fun z hz => hzero z hz)
  refine ⟨G, fun z hz => (Finset.mem_filter.mp hz).2, ?_⟩
  rw [he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  obtain ⟨_, hk, _⟩ := Finset.mem_filter.mp hz
  dsimp only [f]
  rw [if_pos hk, mul_comm]
  exact mul_le_mul_of_nonneg_right (profile_re_le_diag Φ _) (sq_nonneg _)

end Energy

section Slots
variable {α : Type*} [DecidableEq α]

/-- The positive-width slots of `T` as a `Finset α`. -/
def posSlots (T : Finset α) (w : T → ℝ) : Finset α :=
  T.filter (fun x => ∃ hx : x ∈ T, 0 < w ⟨x, hx⟩)

/-- A positive-width slot as a slot of `T`. -/
def liftPos {T : Finset α} {w : T → ℝ} (k : posSlots T w) : T :=
  ⟨k.1, (Finset.mem_filter.mp k.2).1⟩

theorem liftPos_pos {T : Finset α} {w : T → ℝ} (k : posSlots T w) : 0 < w (liftPos k) := by
  obtain ⟨hx, h⟩ := (Finset.mem_filter.mp k.2).2
  exact h

/-- Splitting a product over the slots into positive and zero widths. -/
theorem prod_split_pos {β : Type*} [CommMonoid β] (T : Finset α) (w : T → ℝ) (g : T → β) :
    ∏ k : T, g k = (∏ k : posSlots T w, g (liftPos k)) *
      ∏ k ∈ (Finset.univ : Finset T).filter (fun k => ¬ 0 < w k), g k := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : T => 0 < w k)]
  congr 1
  symm
  refine Finset.prod_bij' (fun k _ => liftPos k)
    (fun k hk => ⟨k.1, Finset.mem_filter.mpr ⟨k.2, ⟨k.2, (Finset.mem_filter.mp hk).2⟩⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, liftPos_pos k⟩
  · intro k _; exact Finset.mem_univ _
  · intro k _; rfl
  · intro k _; rfl
  · intro k _; rfl

theorem sum_split_pos (T : Finset α) (w : T → ℝ) (hw : ∀ k, 0 ≤ w k) :
    ∑ k : T, w k = ∑ k : posSlots T w, w (liftPos k) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k : T => 0 < w k)]
  have h2 : ∑ k ∈ (Finset.univ : Finset T).filter (fun k => ¬ 0 < w k), w k = 0 :=
    Finset.sum_eq_zero (fun k hk => le_antisymm (not_lt.mp (Finset.mem_filter.mp hk).2) (hw k))
  rw [h2, add_zero]
  symm
  refine Finset.sum_bij' (fun k _ => liftPos k)
    (fun k hk => ⟨k.1, Finset.mem_filter.mpr ⟨k.2, ⟨k.2, (Finset.mem_filter.mp hk).2⟩⟩⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, liftPos_pos k⟩
  · intro k _; exact Finset.mem_univ _
  · intro k _; rfl
  · intro k _; rfl
  · intro k _; rfl

end Slots

/-- `∏ₖ (A Z^(ν wₖ)) = A^card Z^(ν ∑ w)`. -/
theorem prod_rpow_slots {ι : Type*} [Fintype ι] (A Z ν : ℝ) (hZ : 0 < Z) (w : ι → ℝ) :
    ∏ k, (A * Z^(ν * w k)) = A^(Fintype.card ι) * Z^(ν * ∑ k, w k) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.rpow_sum_of_pos hZ, Finset.mul_sum]

end
end Qrh.MarkedAnchor.High
