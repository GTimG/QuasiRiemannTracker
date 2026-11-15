/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Weighted

/-!
# High.Batch

The HIGH energy of one batch at the zero bin `a` against the HIGH price (relative scale: the row
radius `U` is the unit, `P` the relative free width, `S = ∑ widths` the relative slot width).

For every occupied amplitude bin the cutoff is the one of `exists_cutoff` for the class
`(ν, e_bin)`, `ν = 2a-1 ≥ k`, `e_bin = 2·(bin mean) ∈ [0, ν]`; the identity
`fiberTarget + e S = detEx(·, P, S, 1) + 1 - ν P` (`fiberTarget_add_eq`) turns the weighted row sum
of `High.Weighted` into
`(∑ ‖∏ Q‖²) · U^(ν P) ≤ K · U^(1 + highPriceF a0 a1 k P S 1 + ε' + losses)`
(`anchor_batch_price`). The factor `U^(ν P)` is the pointwise payment of the inverse (resp. squared
ordinary) factor by the buffered zeros, `|M|² ≤ U^(ν P)`; together this is the HIGH energy of
the batch. Inputs: supported witnesses at every cutoff `t ∈ [1, 3/2]` (baseline
`actual_supported_witness_family` from the zero guards), the buffered slot bound (HC
`actual_source_slot_envelope`), and the fiber moments `AnchorFiberMoments` for every sub-batch.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition

/-- At radius `1`: `fiberTarget + e S = detEx + 1 - ν P`. -/
theorem fiberTarget_add_eq_with_shift [shift : WitnessShift] (a0 a1 ν e w P S : ℝ) :
    fiberTarget a0 a1 ν e w S WitnessShift.value + e * S = detEx a0 a1 ν e w P S 1 + 1 - ν * P := by
  have h1 : shortCnt a0 a1 ν e w S 1 = 1 - ν * w - e * selW a0 a1 S w := by
    unfold shortCnt selW; rw [one_mul, min_comm]; ring
  have h2 : longCnt ν w 1 = 1 / 6 + (5 / 6 - ν) * (3 * w / 2 + WitnessShift.value) := by
    unfold longCnt; ring
  unfold detEx fiberTarget
  rw [h1, h2]; ring

/-- The original fixed-shift price identity. -/
theorem fiberTarget_add_eq (a0 a1 ν e w P S : ℝ) :
    fiberTarget a0 a1 ν e w S + e*S = detEx a0 a1 ν e w P S 1 + 1 - ν*P := by
  simpa only [WitnessShift.value, fixedWitnessShift] using
    (fiberTarget_add_eq_with_shift a0 a1 ν e w P S)

/-- Bin means of an occupied bin lie in `[0, ν/2]`. -/
theorem occupied_bin_mean {Slot : Type*} (slots : Finset Slot) (widths : Slot → ℝ)
    (hw : ∀ s ∈ slots, 0 < widths s) (U ν binWidth : ℝ) (hν : 0 ≤ ν)
    (bin : BinLabel slots (ν/2) binWidth) (Qs : Slot → ℂ)
    (hocc : ∀ s ∈ slots, HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (ν/2) binWidth (Qs s) =
      binValue slots (ν/2) binWidth bin s) :
    0 ≤ weightedMean slots widths (binValue slots (ν/2) binWidth bin) ∧
      weightedMean slots widths (binValue slots (ν/2) binWidth bin) ≤ ν/2 := by
  have hg (s : Slot) (hs : s ∈ slots) : 0 ≤ binValue slots (ν/2) binWidth bin s ∧
      binValue slots (ν/2) binWidth bin s ≤ ν/2 := by
    rw [← hocc s hs]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)
  rcases lt_or_eq_of_le (Finset.sum_nonneg (fun s hs => (hw s hs).le) :
      0 ≤ ∑ s ∈ slots, widths s) with hpos | hzero
  · exact weightedMean_bounds slots widths _ ν (fun s hs => (hw s hs).le) hpos hg
  · have : weightedMean slots widths (binValue slots (ν/2) binWidth bin) = 0 := by
      unfold weightedMean
      rw [show (∑ s∈slots,widths s) = 0 from hzero.symm, div_zero]
    rw [this]; constructor <;> linarith

/-- **HIGH energy of one batch against the HIGH price.** -/
theorem anchor_batch_price {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth εm C height a0 a1 k P ε' : ℝ) (i : ℕ)
    (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1≤3/4) (hk0 : 0 ≤ k) (hk : k ≤ 2*a-1)
    (hε0 : 0≤ε) (hε : ε≤1/1000000000000) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hC : 0≤C) (hheight : 0≤height) (hε' : 0 < ε')
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2)
    (hwit : ∀ t : ℝ, 1 ≤ t → t ≤ 3/2 →
      Nonempty (∀u,SupportedWitness (χ u) U a ε t T allowance i))
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀ w ∈ cutoffs, ∀ wit : (∀ u, SupportedWitness (χ u) U a ε (3*w/2+1/1000000000000) T allowance i),
      ∀ F : Finset Row, F ⊆ rows → ∀ (j : Label) (J K : Fin (dyadicLength U)),
      (∀ u ∈ F, (wit u).label = j ∧ (wit u).left = J ∧ (wit u).right = K) →
      AnchorFiberMoments F slots χ Q widths U a ε (3*w/2+1/1000000000000) a0 a1 w εm C height j J K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) * U^((2*a-1)*P) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(1 + highPriceF a0 a1 k P (∑s∈slots,widths s) 1 + ε' +
        (154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s))) := by
  have hL : 0 ≤ ∑s∈slots,widths s := Finset.sum_nonneg (fun s hs => (hw s hs).le)
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hν0 : 0 ≤ 2*a-1 := by linarith
  -- cutoffs per bin
  let cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ := fun bin =>
    if h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k then
      Classical.choose (exists_cutoff (a0 := a0) (a1 := a1) hk0 h P (∑s∈slots,widths s) 1 hε')
    else cutLo
  have hcut : ∀ bin, cut bin ∈ cutoffs := by
    intro bin
    by_cases h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k
    · simp only [cut, dif_pos h]
      exact (Classical.choose_spec (exists_cutoff (a0 := a0) (a1 := a1) hk0 h P
        (∑s∈slots,widths s) 1 hε')).1
    · simp only [cut, dif_neg h]; exact cutLo_mem
  have hcutspec : ∀ bin, (2*a-1, 2*weightedMean slots widths
      (binValue slots ((2*a-1)/2) binWidth bin)) ∈ classes k →
      detEx a0 a1 (2*a-1) (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        (cut bin) P (∑s∈slots,widths s) 1 <
        highPriceF a0 a1 k P (∑s∈slots,widths s) 1 + ε' := by
    intro bin h
    simp only [cut, dif_pos h]
    exact (Classical.choose_spec (exists_cutoff (a0 := a0) (a1 := a1) hk0 h P
      (∑s∈slots,widths s) 1 hε')).2
  have ht : ∀ bin, 1 ≤ 3*cut bin/2+1/1000000000000 ∧ 3*cut bin/2+1/1000000000000 ≤ 3/2 := by
    intro bin
    obtain ⟨h1, h2⟩ := hcut bin
    unfold cutLo at h1; unfold cutHi at h2
    constructor <;> linarith
  let witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000000000) T allowance i :=
    fun bin => Classical.choice (hwit _ (ht bin).1 (ht bin).2)
  have hsum := anchor_weighted_row_sum rows slots χ Q widths U a ε T allowance mesh binWidth εm C
    height a0 a1 (1 - (2*a-1)*P + highPriceF a0 a1 k P (∑s∈slots,widths s) 1 + ε') i hU ha hν
    hε0 hε hmesh hbin hC hheight hfreq hw hwm hL ha1 ha1' cut hcut witness hQ
    (fun bin j J K => hmom (cut bin) (hcut bin) (witness bin) _ (Finset.filter_subset _ _) j J K
      (fun u hu => by
        obtain ⟨-, h1, h2, h3, -⟩ := anchorFiber_fields rows slots widths Q χ U a ε T allowance
          binWidth i hbin cut witness bin j J K u hu
        exact ⟨h1, h2, h3⟩))
    (by
      intro bin hex
      obtain ⟨u, -, hocc⟩ := hex
      obtain ⟨hm0, hm1⟩ := occupied_bin_mean slots widths hw U (2*a-1) binWidth hν0 bin
        (Q u) hocc
      have hcl : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
          ∈ classes k := ⟨hk, hν, by linarith, by linarith⟩
      have h1 := hcutspec bin hcl
      have h2 := fiberTarget_add_eq a0 a1 (2*a-1)
        (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)) (cut bin) P
        (∑s∈slots,widths s)
      linarith)
  have hP : 0 ≤ U^((2*a-1)*P) := Real.rpow_nonneg hU0.le _
  refine (mul_le_mul_of_nonneg_right hsum hP).trans (le_of_eq ?_)
  rw [mul_assoc, ← Real.rpow_add hU0]
  congr 2
  ring


/-- **HIGH batch energy from the buffered zero guards.** The supported witnesses at every cutoff are
supplied by the baseline `actual_supported_witness_family` (constants chosen before the scale);
the remaining inputs are the slot envelope and the fiber moments. -/
theorem anchor_batch_price_guards (dmin dmax τ ε e κ η : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*η)
    (hε : 0<ε) (hεs : ε ≤ 1/1000000000000) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1)
    (hη : 0≤η) (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax → 1 < Z^d →
    ∀ {Row Label Slot : Type*} [Fintype Label] (χ : Row→Label→Character)
      (hχ : ∀ u j, (χ u j).residue ≠ 1) (rows : Finset Row) (slots : Finset Slot)
      (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
      (a mesh binWidth εm C height a0 a1 k P ε' : ℝ) (i : ℕ), i ≤ I →
      51/100 < a → 2*a-1 ≤ 3/4 → 0 ≤ k → k ≤ 2*a-1 → 0 ≤ mesh → 0 < binWidth → 0 ≤ C →
      0 ≤ height → 0 < ε' → 0 ≤ a1 → a1 ≤ 1/2 →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i : ℕ)*Z^τ ≤ height →
      (∀ u, HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ) < a+2*e) →
      (∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
      (∀ u j, (χ u j).modulus.absNorm ≤ Z^d) →
      (∀s∈slots,0<widths s) → (∀s∈slots,widths s≤mesh) →
      (∀u∈rows,∀s∈slots,‖Q u s‖≤((Z^d)^(widths s))^((2*a-1)/2+binWidth)) →
      (∀ w ∈ cutoffs, ∀ wit : (∀ u, SupportedWitness (χ u) (Z^d) a ε (3*w/2+1/1000000000000) (Z^τ)
          ((Z^d)^(τ/(2*dmax))) i),
        ∀ F : Finset Row, F ⊆ rows → ∀ (j : Label) (J K : Fin (dyadicLength (Z^d))),
        (∀ u ∈ F, (wit u).label = j ∧ (wit u).left = J ∧ (wit u).right = K) →
        AnchorFiberMoments F slots χ Q widths (Z^d) a ε (3*w/2+1/1000000000000) a0 a1 w εm C height
          j J K) →
      (∑u∈rows,‖∏s∈slots,Q u s‖^2) * (Z^d)^((2*a-1)*P) ≤
        ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
          Fintype.card Label*(dyadicLength (Z^d) : ℝ)^2*(192*(1+height)*C))*
        (Z^d)^(1 + highPriceF a0 a1 k P (∑s∈slots,widths s) 1 + ε' +
          (154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s))) := by
  obtain ⟨Z₀, hZ₀⟩ := actual_supported_witness_family dmin dmax τ ε e κ η I hdmin hdmax hτ
    hτzero hτheight hε he he' hκ hκ' hη hbudget
  refine ⟨Z₀, ?_⟩
  intro Z hZ d hd hd' hU Row Label Slot _ χ hχ rows slots Q widths a mesh binWidth εm C height
    a0 a1 k P ε' i hi ha hν hk0 hk hmesh hbin hC hheight hε' ha1 ha1' hfreq hnext hcur hmod hw hwm
    hQ hmom
  have hwit := hZ₀ Z hZ d hd hd' χ hχ a i hi ha (by linarith) hnext hcur hmod
  exact anchor_batch_price rows slots χ Q widths (Z^d) a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) mesh
    binWidth εm C height a0 a1 k P ε' i hU (by linarith) hν hk0 hk hε.le hεs hmesh hbin hC hheight
    hε' hfreq hw hwm ha1 ha1' (fun t h1 h2 => hwit t h1 h2) hQ hmom

end
end Qrh.TwoSlot.AnchorZeroLoss.High
