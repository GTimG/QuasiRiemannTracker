import LocalMoment.UnmarkedDensity

/-! Unmarked detector partition, adapted from OpenAI's DetectorBatch and
DetectorFiberPartition. Unlike the marked batch, this has no positive
prime-slot-supply hypothesis. Its moments remain explicit source inputs. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount HeckeDetectorRawFiber

structure UnmarkedBatch (Label : Type*) (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow → Label → Character
  witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U
  data : Label → RowData
  reverse : Label → Bool
  row_coeff : ∀ u ∈ rows, ∀ j, ∀ I : Ideal O, idealCoeff (family u j) I =
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val, u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val, u.property.1⟩) I

variable {Label : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- Extend witnesses only to satisfy the ambient `FreeRow` interface.
Outside the finite source set, reuse one source row; no principal or
out-of-bin ambient row is required to possess a detector witness. -/
def supportedRowRetraction (rows : Finset FreeRow) (u₀ : rows) (u : FreeRow) : rows :=
  if hu : u ∈ rows then ⟨u, hu⟩ else u₀

@[simp] theorem supportedRowRetraction_mem (rows : Finset FreeRow) (u₀ u : rows) :
    supportedRowRetraction rows u₀ u.val = u := by
  simp [supportedRowRetraction, u.property]

def UnmarkedBatch.ofSupportedRows (rows : Finset FreeRow) (u₀ : rows)
    (family : rows → Label → Character)
    (witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i)
    (hrow : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U)
    (data : Label → RowData) (reverse : Label → Bool)
    (hcoeff : ∀ u : rows, ∀ j, ∀ I : Ideal O, idealCoeff (family u j) I =
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character
        ⟨u.val.val, u.val.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val.val, u.val.property.1⟩) I) :
    UnmarkedBatch Label U a ε tstar T allowance i where
  rows := rows
  family := fun u => family (supportedRowRetraction rows u₀ u)
  witness := fun u => witness (supportedRowRetraction rows u₀ u)
  row_norm := hrow
  data := data
  reverse := reverse
  row_coeff := by
    intro u hu j I
    have h := hcoeff ⟨u, hu⟩ j I
    simpa only [supportedRowRetraction, dite_eq_left hu] using h

def UnmarkedBatch.fiberRows (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  B.rows.filter (fun u => (B.witness u).label = j ∧
    (B.witness u).left = J ∧ (B.witness u).right = K)

def UnmarkedBatch.fiber (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows j J K).Nonempty) : UnmarkedFiber U a ε tstar T allowance i Label where
  rows := B.fiberRows j J K
  nonempty := hne
  family := B.family
  witness := B.witness
  label := j
  left := J
  right := K
  fixed_label := fun _ hu => (Finset.mem_filter.mp hu).2.1
  fixed_left := fun _ hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_right := fun _ hu => (Finset.mem_filter.mp hu).2.2.2
  row_norm := fun u hu => B.row_norm u (Finset.mem_filter.mp hu).1
  rowData := B.data j
  reverse := B.reverse j
  row_coeff := fun u hu => B.row_coeff u (Finset.mem_filter.mp hu).1 j

theorem UnmarkedBatch.card_eq_sum_fibers [Fintype Label]
    (B : UnmarkedBatch Label U a ε tstar T allowance i) :
    B.rows.card = ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows j J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s := B.rows) (t := Finset.univ)
    (f := fun u => ((B.witness u).label, (B.witness u).left, (B.witness u).right))
    (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type, Prod.mk.injEq, UnmarkedBatch.fiberRows] using hh

theorem UnmarkedBatch.card_bound [Fintype Label]
    (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (C exponent : ℝ) (hC : 0 ≤ C) (hU : 0 < U)
    (hfiber : ∀ j J K, ∀ hne : (B.fiberRows j J K).Nonempty,
      ((B.fiber j J K hne).rows.card : ℝ) ≤ C * U ^ exponent) :
    (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 *
      C * U ^ exponent := by
  have he : (B.rows.card : ℝ) = ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C * U ^ exponent := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows j J K).Nonempty
      · exact hfiber j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Sum the actual supported-witness partition at the balanced unmarked
cutoff. This incurs only the displayed label and two dyadic-length counts. -/
theorem batch_count_from_unmarked_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
        ∀ (a ε T allowance C height : ℝ) (i : ℕ),
        1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
        0 ≤ C → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
        ∀ {Label : Type*} [Fintype Label]
          (B : UnmarkedBatch Label U a ε (unmarkedCutoff (2 * a - 1)) T allowance i),
        (∀ j J K, ∀ hne : (B.fiberRows j J K).Nonempty,
          UnmarkedMoments (B.fiber j J K hne) c κ C height εm) →
        (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 *
          fiberConstant C height K₀ * U ^ (unmarkedDensity (2 * a - 1) + 156 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ := count_from_unmarked_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance C height i hU ha hδ hε hεsmall hC hh hf Label _ B moments
  apply B.card_bound (fiberConstant C height K₀) _
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU)
  intro j J K hne
  exact hcount a ε T allowance C height i hU ha hδ hε hεsmall hC hh hf
    (B.fiber j J K hne) (moments j J K hne)

end SevenEighths.LocalMoment
end
end OAI
