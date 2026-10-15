import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.PerturbedCentral

open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
open SevenEighths.ProbeHighRowFamily
local notation "O" => HeckeFamily.O

/-! Total-slot-mass versions of the 1/6 identities used by the central source batch. -/

lemma source_slot_length_sum_total {Slot : Type*} (slots : Finset Slot) (ell : Slot → ℝ)
    (d E : ℝ) (hell : ∑ j ∈ slots, ell j = E) :
    (∑ j ∈ slots, ell j / d) = E / d := by
  rw [← Finset.sum_div, hell]

lemma source_slot_weightedMean_total {Slot : Type*} (slots : Finset Slot)
    (ell g : Slot → ℝ) (d E : ℝ) (hd : d ≠ 0) (hE : E ≠ 0)
    (hell : ∑ j ∈ slots, ell j = E) :
    HeckeDetectorPhysicalSelection.weightedMean slots (fun j => ell j / d) g =
      (∑ j ∈ slots, ell j * g j) / E := by
  unfold HeckeDetectorPhysicalSelection.weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div, hell]
  field_simp [hd, hE]

lemma source_slot_product_total {Slot : Type*} (slots : Finset Slot)
    (ell g : Slot → ℝ) (Z d E mesh : ℝ) (hZ : 0 < Z) (hd : d ≠ 0)
    (hE : E ≠ 0) (hell : ∑ j ∈ slots, ell j = E) :
    (∏ j ∈ slots, (Z ^ (ell j)) ^ (-(4 / 25 : ℝ) + g j + mesh)) =
      Z ^ (E * (-(4 / 25 : ℝ) +
        HeckeDetectorPhysicalSelection.weightedMean slots (fun j => ell j / d) g + mesh)) := by
  simp_rw [← Real.rpow_mul hZ.le]
  rw [← Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean_total slots ell g d E hd hE hell]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul, hell]
  field_simp [hE]

lemma physical_slot_widths_injective {N : ℕ} (ell : Fin N → ℝ) (d : ℝ)
    (hell : Function.Injective ell) (hd : d ≠ 0) :
    Function.Injective (fun j => ell j / d) := by
  intro i j hij
  apply hell
  field_simp [hd] at hij
  exact hij

lemma physical_slot_widths_total {N : ℕ} (ell : Fin N → ℝ)
    (d dmin mesh E : ℝ) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (hdtop : d ≤ 37 / 42) (hElo : 1 / 6 ≤ E)
    (hell : ∀ j, 0 < ell j) (hsmall : ∀ j, ell j ≤ dmin * mesh)
    (hsum : ∑ j, ell j = E) :
    (∀ j, 0 < ell j / d) ∧
      (∀ j, ell j / d ≤ mesh) ∧
      7 / 37 ≤ ∑ j, ell j / d := by
  have hd0 : 0 < d := hdmin.trans_le hd
  have hEpos : 0 < E := (by norm_num : (0 : ℝ) < 1 / 6).trans_le hElo
  have hm : 0 ≤ mesh := by
    by_contra hn
    have hmneg : mesh < 0 := lt_of_not_ge hn
    have hs : (∑ j, ell j) ≤ 0 :=
      Finset.sum_nonpos fun j _ =>
        (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hmneg.le)
    rw [hsum] at hs
    linarith
  refine ⟨fun j => div_pos (hell j) hd0, fun j => ?_, ?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [← Finset.sum_div, hsum]
    apply (le_div_iff₀ hd0).mpr
    have htop : (7 / 37 : ℝ) * d ≤ 1 / 6 := by
      nlinarith
    exact htop.trans hElo

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Additive replacement for `actual_source_batch` with arbitrary total slot mass `E ≥ 1/6`. -/
theorem actual_source_batch_totalE (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀ P ∈ S, P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth E : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hdtop : dmax ≤ 37 / 42)
    (hτ : 0 < τ) (hτzero : τ < dmin / 2)
    (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hheightCost : 0 ≤ heightCost)
    (hmargin : 0 < margin) (hm : 0 ≤ mesh) (hb : 0 < binWidth)
    (hElo : 1 / 6 ≤ E)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    ∀ (U : ℝ) (rows : Finset FreeRow), rows.Nonempty →
      rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) U →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
    ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
      (∀ u ∈ rows,
        detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows,
        a ≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ)) →
    ∀ tstar : ℝ, 1 ≤ tstar → tstar ≤ 3 / 2 →
    ∀ (N : ℕ) (ell : Fin N → ℝ), (∀ j, 0 < ell j) →
      (∀ j, ell j ≤ dmin * mesh) → (∑ j, ell j) = E →
    ∀ (W : Fin N → ℝ → ℂ) (upper : Fin N → ℝ) (z : Fin N → ℂ),
    ∃ B : HeckeDetectorBatch.Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z ^ d) a ε tstar (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
      B.rows = rows ∧
      B.data = sourceMomentData M H hH S hS.prime η ∧
      B.reverse = sourceMomentReverse M H ∧
      B.slots = Finset.univ ∧
      B.widths = (fun j => ell j / d) ∧
      B.profile = W ∧ B.upper = upper ∧ B.external = z ∧
      B.mesh = mesh ∧ B.binWidth = binWidth ∧
      (∀ u ∈ rows, ∀ j,
        B.family u j =
          sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw, eventually_ge_atTop (1 : ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent
    tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u => hnext u.val u.property) (fun u => hcurrent u.val u.property)
    tstar ht ht'
  obtain ⟨u0, h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u ∈ rows) : rowNorm u ≤ Z ^ d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp, hwm, hsp⟩ := physical_slot_widths_total ell d dmin mesh E
    hdmin hd (hd'.trans hdtop) hElo hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z ^ d) a ε tstar (Z ^ τ)
    ((Z ^ d) ^ (τ / (2 * dmax))) i (fun u hu => w ⟨u, hu⟩) hnorm
    Finset.univ W upper (fun j => ell j / d) z mesh binWidth hm hb
    (fun j _ => hwp j) (fun j _ => hwm j) hsp
  refine ⟨B, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro u hu j
  dsimp [B, retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]

/-- Additive replacement for `actual_source_amplitude_batches` at total slot mass `E`. -/
theorem actual_source_amplitude_batches_totalE (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth E : ℝ) (I : ℕ)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hdtop : dmax ≤ 37 / 42)
    (hτ : 0 < τ) (hτzero : τ < dmin / 2)
    (hτheight : 4 * τ < dmin * heightCost)
    (hε : 0 < ε) (he : 0 < e) (he' : e < 1 / 1000)
    (hκ : 0 < κ) (hκ' : κ ≤ 1) (hheightCost : 0 ≤ heightCost)
    (hmargin : 0 < margin) (hm : 0 ≤ mesh) (hb : 0 < binWidth)
    (hElo : 1 / 6 ≤ E)
    (hbudget : 12 * e * ((22 : ℝ) + 2) + 8 * κ + 2 * heightCost ≤ ε / 2) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
    ∀ (U : ℝ) (rows : Finset FreeRow), rows.Nonempty →
      rows ⊆ rowBand (Z ^ (1 / 100 : ℝ)) U →
      (∀ u ∈ rows, (calibrationForSet S hmax).residueMonoid u.val ≠ 0) →
      (∀ u ∈ rows, rowNorm u ≤ Z ^ (d - margin)) →
    ∀ (a : ℝ) (i : ℕ), i ≤ I → 51 / 100 < a → a ≤ 1 →
      (∀ u ∈ rows,
        detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3 * (i + 1 : ℕ) * Z ^ τ) < a + 2 * e) →
      (∀ u ∈ rows,
        a ≤ detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          ((3 * i : ℕ) * Z ^ τ)) →
    ∀ (N : ℕ) (ell : Fin N → ℝ), (∀ j, 0 < ell j) →
      (∀ j, ell j ≤ dmin * mesh) → (∑ j, ell j) = E →
    ∀ (W : Fin N → ℝ → ℂ) (upper : Fin N → ℝ) (z : Fin N → ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
      W upper (fun j => ell j / d) z (Z ^ d)
    ∀ bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N))
      ((2 * a - 1) / 2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z ^ d) ((2 * a - 1) / 2) binWidth hb (fun j => ell j / d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2 * a - 1) / 2)
      binWidth (fun j => ell j / d) bin
    ∃ B : HeckeDetectorBatch.Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z ^ d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2 * a - 1) q)
        (Z ^ τ) ((Z ^ d) ^ (τ / (2 * dmax))) i,
      B.rows = rows' ∧
      B.data = sourceMomentData M H hH S hS.prime η ∧
      B.reverse = sourceMomentReverse M H ∧
      B.slots = Finset.univ ∧
      B.widths = (fun j => ell j / d) ∧
      B.profile = W ∧ B.upper = upper ∧ B.external = z ∧
      B.mesh = mesh ∧ B.binWidth = binWidth ∧
      (∀ u ∈ rows', ∀ j,
        B.family u j = sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀ u ∈ B.rows,
        HeckeDetectorAmplitudeFirst.rowMean B.slots (Z ^ d) ((2 * a - 1) / 2)
          B.binWidth B.widths
          (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
            B.profile B.upper B.widths B.external (Z ^ d)) u = q) := by
  have hbatches := actual_source_batch_totalE M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth E I
    hdmin hdmax hdtop hτ hτzero hτheight hε he he' hκ hκ' hheightCost
    hmargin hm hb hElo hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent
    N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow => u.val)
    W upper (fun j => ell j / d) z (Z ^ d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z ^ d) ((2 * a - 1) / 2) binWidth hb (fun j => ell j / d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2 * a - 1) / 2)
    binWidth (fun j => ell j / d) bin
  have hsub : rows' ⊆ rows := Finset.filter_subset _ _
  have hcut := HeckeDetectorAdaptiveCutoff.cutoff_bounds (2 * a - 1) q (by linarith)
  obtain ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW, hUpper, hZ, hMesh, hBin, hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu => hcal u (hsub hu)) (fun u hu => hrow u (hsub hu))
      a i hi ha ha' (fun u hu => hnext u (hsub hu))
      (fun u hu => hcurrent u (hsub hu))
      (HeckeDetectorAdaptiveCutoff.cutoff (2 * a - 1) q) hcut.1 hcut.2
      N ell hell hsmall hsum W upper z
  refine ⟨B, hBr, hBd, hRev, hSlots, hWidths, hW, hUpper, hZ, hMesh, hBin, hFam, ?_⟩
  intro u hu
  have hu' : u ∈ rows' := hBr ▸ hu
  rw [hSlots, hWidths, hW, hUpper, hZ, hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z ^ d)
    ((2 * a - 1) / 2) binWidth hb (fun j => ell j / d) Q bin u hu'

end SevenEighths.PerturbedCentral
end
end OAI
