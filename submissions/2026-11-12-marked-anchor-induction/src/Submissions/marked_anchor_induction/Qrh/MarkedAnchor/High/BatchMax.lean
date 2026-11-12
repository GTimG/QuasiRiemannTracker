/- Copyright (c) 2026 Sil. Apache-2.0.
The `max 1` slot weights follow Hailey Collet's `Record12518109Gain` max-weighted row sums
(`raw_max_fiber_comparison`, Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.PriceFloor
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Batch
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Cofactor.Restore
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Witness

/-!
# High.BatchMax

The HIGH batch bound in the form the leaf consumes after the raw/core slot comparison of HC
(`eventually_whole_original_raw_max_comparison` bounds `∑ ∏ max 1 ‖rawQ‖²` by `4^#slots ∑ ∏ max 1 ‖coreQ‖²`),
with the cutoff floor of `High.PriceFloor`:

* `weighted_of_card_max`: rows with common amplitude bins pay `∏ max 1 ‖Q‖² ≤ U^(2 q S + 2 bw S)`;
* `anchor_weighted_max_sum`: the weighted row sum of `High.Weighted` with `∏ max 1 ‖Q‖²`;
* `anchor_batch_maxW`: `(∑ ∏ max 1 ‖Q‖²) · U^(ν P) ≤ K · U^(1 + max 0 (detPriceW a0 a1 k wlo P S 1) + ε' + losses)`,
  the fiber moments needed only for cutoffs `w ≥ wlo` (`HighCoreFiberInputs`);
* `scaled_detPriceW`, `restored_price_leW`, `core_restored_le_detW`: the restoration of
  `Cofactor.Restore` for the floored price:
  `(M-d)/6 + d (1 + max 0 (detPriceW(P/d,S/d,1))) ≤ M + highPriceFW(P,S,M)` (`0 < d ≤ M`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorSupportedWitness HeckeDetectorFiberPartition

variable {Row Label Slot : Type*}

/-- Slot payment with `max 1` weights. -/
theorem weighted_of_card_max (rows : Finset Row) (slots : Finset Slot) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U ν binWidth A X : ℝ) (hU : 1<U) (hbin : 0<binWidth)
    (hw : ∀s∈slots,0<widths s) (hL : 0≤∑s∈slots,widths s)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (ν/2) binWidth (Q u s)=g s)
    (hν : 0 ≤ ν)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^(ν/2+binWidth))
    (hcard : (rows.card : ℝ)≤A*U^X) :
    (∑u∈rows,∏s∈slots,max 1 (‖Q u s‖^2)) ≤ A*U^(X+2*weightedMean slots widths g*(∑s∈slots,widths s)+
      2*binWidth*(∑s∈slots,widths s)) := by
  set S := ∑s∈slots,widths s with hSdef
  set q := weightedMean slots widths g with hqdef
  have hU0 : 0<U := zero_lt_one.trans hU
  have hmeanS : q*S=∑s∈slots,widths s*g s := by
    rcases lt_or_eq_of_le hL with hLp | hzero
    · rw [hqdef, hSdef]; unfold weightedMean; exact div_mul_cancel₀ _ hLp.ne'
    · have hempty : slots=∅ := by
        by_contra hne
        have hpos := Finset.sum_pos hw (Finset.nonempty_iff_ne_empty.mpr hne)
        linarith
      subst hempty
      simp [hSdef]
  have hslot (u : Row) (hu : u∈rows) (s : Slot) (hs : s ∈ slots) :
      max 1 (‖Q u s‖^2) ≤ U^(2*(widths s*g s) + 2*(binWidth*widths s)) := by
    have hP : 1 < U^(widths s) := Real.one_lt_rpow hU (hw s hs)
    have hup := HeckePrimeAmplitudeBins.amplitude_upper (U^(widths s)) (ν/2) binWidth (Q u s) hP
      hbin (hQ u hu s hs)
    rw [hbins u hu s hs] at hup
    have hg0 : 0 ≤ g s := by
      rw [← hbins u hu s hs]
      exact (HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)).1
    have he : (U^(widths s))^(g s + binWidth) = U^(widths s*g s + binWidth*widths s) := by
      rw [← Real.rpow_mul hU0.le]; congr 1; ring
    rw [he] at hup
    have h1 : 1 ≤ U^(widths s*g s + binWidth*widths s) :=
      Real.one_le_rpow hU.le (by have := (hw s hs).le; positivity)
    have hsq : (U^(widths s*g s + binWidth*widths s))^2 =
        U^(2*(widths s*g s) + 2*(binWidth*widths s)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]; congr 1; push_cast; ring
    rw [← hsq]
    refine max_le (by nlinarith) ?_
    exact pow_le_pow_left₀ (norm_nonneg _) hup 2
  have hprod (u : Row) (hu : u∈rows) : ∏s∈slots,max 1 (‖Q u s‖^2) ≤ U^(2*q*S+2*binWidth*S) := by
    calc ∏s∈slots,max 1 (‖Q u s‖^2)
        ≤ ∏s∈slots,U^(2*(widths s*g s) + 2*(binWidth*widths s)) :=
          Finset.prod_le_prod₀ (fun s _ => le_trans zero_le_one (le_max_left _ _))
            (fun s hs => hslot u hu s hs)
      _ = U^(∑s∈slots,(2*(widths s*g s) + 2*(binWidth*widths s))) :=
          (Real.rpow_sum_of_pos hU0 _ _).symm
      _ = U^(2*q*S+2*binWidth*S) := by
          congr 1
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hmeanS,
            hSdef]
          ring
  have hA : 0 ≤ A*U^X := (Nat.cast_nonneg _).trans hcard
  calc
    _ ≤ ∑u∈rows,U^(2*q*S+2*binWidth*S) := Finset.sum_le_sum hprod
    _ = (rows.card : ℝ)*U^(2*q*S+2*binWidth*S) := by simp
    _ ≤ (A*U^X)*U^(2*q*S+2*binWidth*S) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hU0.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hU0]; congr 1; congr 1; ring

/-- The weighted HIGH row sum with `max 1` slot weights. -/
theorem anchor_weighted_max_sum [Fintype Label]
    (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth εm C height a0 a1 E : ℝ) (i : ℕ)
    (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1≤3/4) (hε0 : 0≤ε) (hε : ε≤1/1000000) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hC : 0≤C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh) (hL : 0≤∑s∈slots,widths s)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2)
    (cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ) (hcut : ∀ bin, cut bin ∈ cutoffs)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000) T allowance i)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀ bin j J K, AnchorFiberMoments
      (anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K)
      slots χ Q widths U a ε (3*cut bin/2+1/1000000) a0 a1 (cut bin) εm C height j J K)
    (hE : ∀ bin, (∃ u ∈ rows, ∀ s ∈ slots,
        HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s) =
          binValue slots ((2*a-1)/2) binWidth bin s) → fiberTarget a0 a1 (2*a-1)
        (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)) (cut bin)
        (∑s∈slots,widths s) +
      2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)*(∑s∈slots,widths s)
        ≤ E) :
    (∑u∈rows,∏s∈slots,max 1 (‖Q u s‖^2)) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(E + 154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s)) := by
  set A := 192*(1+height)*C with hAdef
  set X := E + 154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s) with hXdef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hU0 : 0<U := zero_lt_one.trans hU
  have hf (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
      (J K : Fin (dyadicLength U)) :
      (∑u∈anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K,
        ∏s∈slots,max 1 (‖Q u s‖^2)) ≤ A*U^X := by
    set F := anchorFiber rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness bin j J K
    by_cases hne : F.Nonempty
    · have hfields (u : Row) (hu : u∈F) := anchorFiber_fields rows slots widths Q χ U a ε
        T allowance binWidth i hbin cut witness bin j J K u hu
      have hc := anchor_fiber_count F hne slots χ Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U a ε T allowance mesh binWidth εm C height
        a0 a1 (cut bin) i hU ha hν hε0 hε hmesh hbin hC hheight hfreq hw hwm hL ha1 ha1'
        (hcut bin) (witness bin) j J K (fun u hu=>(hfields u hu).2.1)
        (fun u hu=>(hfields u hu).2.2.1) (fun u hu=>(hfields u hu).2.2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.2) (hmom bin j J K)
      have hh := weighted_of_card_max F slots Q widths (binValue slots ((2*a-1)/2) binWidth bin)
        U (2*a-1) binWidth A _ hU hbin hw hL (fun u hu=>(hfields u hu).2.2.2.2) (by linarith)
        (fun u hu=>hQ u (hfields u hu).1) hc
      refine hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hU.le ?_) hA)
      obtain ⟨u0, hu0⟩ := hne
      have := hE bin ⟨u0, (hfields u0 hu0).1, (hfields u0 hu0).2.2.2.2⟩
      rw [hXdef]; linarith
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he,Finset.sum_empty]
      exact mul_nonneg hA (Real.rpow_nonneg hU0.le _)
  rw [anchor_fiber_sum rows slots widths Q χ U a ε T allowance binWidth i hbin cut witness]
  calc
    _ ≤ ∑bin : BinLabel slots ((2*a-1)/2) binWidth,∑j : Label,
        ∑J : Fin (dyadicLength U),∑K : Fin (dyadicLength U),A*U^X := by
      exact Finset.sum_le_sum (fun bin _=>Finset.sum_le_sum (fun j _=>
        Finset.sum_le_sum (fun J _=>Finset.sum_le_sum (fun K _=>hf bin j J K))))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- **HIGH batch with `max 1` weights against the floored detector price.** -/
theorem anchor_batch_maxW [Fintype Label]
    (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth εm C height a0 a1 k wlo P ε' : ℝ) (i : ℕ)
    (hU : 1<U) (ha : 1/2≤a) (hν : 2*a-1≤3/4) (hk0 : 0 ≤ k) (hk : k ≤ 2*a-1) (hlo : wlo ≤ cutHi)
    (hε0 : 0≤ε) (hε : ε≤1/1000000) (hmesh : 0≤mesh)
    (hbin : 0<binWidth) (hC : 0≤C) (hheight : 0≤height) (hε' : 0 < ε')
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh)
    (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2)
    (hwit : ∀ t : ℝ, 1 ≤ t → t ≤ 3/2 →
      Nonempty (∀u,SupportedWitness (χ u) U a ε t T allowance i))
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀ w ∈ cutoffs, wlo ≤ w →
      ∀ wit : (∀ u, SupportedWitness (χ u) U a ε (3*w/2+1/1000000) T allowance i),
      ∀ F : Finset Row, F ⊆ rows → ∀ (j : Label) (J K : Fin (dyadicLength U)),
      (∀ u ∈ F, (wit u).label = j ∧ (wit u).left = J ∧ (wit u).right = K) →
      AnchorFiberMoments F slots χ Q widths U a ε (3*w/2+1/1000000) a0 a1 w εm C height j J K) :
    (∑u∈rows,∏s∈slots,max 1 (‖Q u s‖^2)) * U^((2*a-1)*P) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(1 + max 0 (detPriceW a0 a1 k wlo P (∑s∈slots,widths s) 1) + ε' +
        (154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s))) := by
  have hL : 0 ≤ ∑s∈slots,widths s := Finset.sum_nonneg (fun s hs => (hw s hs).le)
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hν0 : 0 ≤ 2*a-1 := by linarith
  let cut : BinLabel slots ((2*a-1)/2) binWidth → ℝ := fun bin =>
    if h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k then
      Classical.choose (exists_cutoffW_det (a0 := a0) (a1 := a1) hk0 hlo h P (∑s∈slots,widths s) 1 hε')
    else max (clampLo wlo) cutLo
  have hcut : ∀ bin, cut bin ∈ cutoffs ∧ wlo ≤ cut bin := by
    intro bin
    by_cases h : (2*a-1, 2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        ∈ classes k
    · simp only [cut, dif_pos h]
      obtain ⟨h1, h2, -⟩ := Classical.choose_spec (exists_cutoffW_det (a0 := a0) (a1 := a1) hk0 hlo h P
        (∑s∈slots,widths s) 1 hε')
      exact ⟨h1, h2⟩
    · simp only [cut, dif_neg h]
      have hc := clampLo_mem wlo
      refine ⟨⟨le_max_right _ _, max_le hc.2 (by norm_num [cutLo, cutHi])⟩, ?_⟩
      refine le_trans ?_ (le_max_left _ _)
      unfold clampLo; exact le_min (le_max_left _ _) hlo
  have hcutspec : ∀ bin, (2*a-1, 2*weightedMean slots widths
      (binValue slots ((2*a-1)/2) binWidth bin)) ∈ classes k →
      detEx a0 a1 (2*a-1) (2*weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin))
        (cut bin) P (∑s∈slots,widths s) 1 <
        max 0 (detPriceW a0 a1 k wlo P (∑s∈slots,widths s) 1) + ε' := by
    intro bin h
    simp only [cut, dif_pos h]
    exact (Classical.choose_spec (exists_cutoffW_det (a0 := a0) (a1 := a1) hk0 hlo h P
      (∑s∈slots,widths s) 1 hε')).2.2
  have ht : ∀ bin, 1 ≤ 3*cut bin/2+1/1000000 ∧ 3*cut bin/2+1/1000000 ≤ 3/2 := by
    intro bin
    obtain ⟨⟨h1, h2⟩, -⟩ := hcut bin
    unfold cutLo at h1; unfold cutHi at h2
    constructor <;> linarith
  let witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (3*cut bin/2+1/1000000) T allowance i :=
    fun bin => Classical.choice (hwit _ (ht bin).1 (ht bin).2)
  have hsum := anchor_weighted_max_sum rows slots χ Q widths U a ε T allowance mesh binWidth εm C
    height a0 a1 (1 - (2*a-1)*P + max 0 (detPriceW a0 a1 k wlo P (∑s∈slots,widths s) 1) + ε') i
    hU ha hν hε0 hε hmesh hbin hC hheight hfreq hw hwm hL ha1 ha1' cut (fun bin => (hcut bin).1)
    witness hQ
    (fun bin j J K => hmom (cut bin) (hcut bin).1 (hcut bin).2 (witness bin) _
      (Finset.filter_subset _ _) j J K
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

/-- **Core batch from the buffered zero guards at an unbounded height index** (witnesses from
`budget_supported_witness_family`; constants before the scale `Z`, core scale `U = Z^d`). -/
theorem core_batch_guards (dmin dmax τ ε e κ η : ℝ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hε : 0<ε) (hεs : ε ≤ 1/1000000) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1)
    (hη : 0≤η) (hη2 : η ≤ 2) (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*η≤ε/2) :
    ∃ Z₀ : ℝ, ∀ Z : ℝ, Z₀ ≤ Z → ∀ d : ℝ, dmin ≤ d → d ≤ dmax → 1 < Z^d →
    ∀ {Row Label Slot : Type*} [Fintype Label] (χ : Row→Label→Character)
      (hχ : ∀ u j, (χ u j).residue ≠ 1) (rows : Finset Row) (slots : Finset Slot)
      (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
      (a mesh binWidth εm C height a0 a1 k wlo P ε' : ℝ) (i : ℕ),
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^η →
      51/100 < a → 2*a-1 ≤ 3/4 → 0 ≤ k → k ≤ 2*a-1 → wlo ≤ cutHi → 0 ≤ mesh → 0 < binWidth →
      0 ≤ C → 0 ≤ height → 0 < ε' → 0 ≤ a1 → a1 ≤ 1/2 →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i : ℕ)*Z^τ ≤ height →
      (∀ u, HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ) < a+2*e) →
      (∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ)) →
      (∀ u j, (χ u j).modulus.absNorm ≤ Z^d) →
      (∀s∈slots,0<widths s) → (∀s∈slots,widths s≤mesh) →
      (∀u∈rows,∀s∈slots,‖Q u s‖≤((Z^d)^(widths s))^((2*a-1)/2+binWidth)) →
      (∀ w ∈ cutoffs, wlo ≤ w → ∀ wit : (∀ u, SupportedWitness (χ u) (Z^d) a ε (3*w/2+1/1000000)
          (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
        ∀ F : Finset Row, F ⊆ rows → ∀ (j : Label) (J K : Fin (dyadicLength (Z^d))),
        (∀ u ∈ F, (wit u).label = j ∧ (wit u).left = J ∧ (wit u).right = K) →
        AnchorFiberMoments F slots χ Q widths (Z^d) a ε (3*w/2+1/1000000) a0 a1 w εm C height
          j J K) →
      (∑u∈rows,∏s∈slots,max 1 (‖Q u s‖^2)) * (Z^d)^((2*a-1)*P) ≤
        ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
          Fintype.card Label*(dyadicLength (Z^d) : ℝ)^2*(192*(1+height)*C))*
        (Z^d)^(1 + max 0 (detPriceW a0 a1 k wlo P (∑s∈slots,widths s) 1) + ε' +
          (154*ε + (2*a-1)*mesh + εm + 2*binWidth*(∑s∈slots,widths s))) := by
  obtain ⟨Z₀, hZ₀⟩ := budget_supported_witness_family dmin dmax τ ε e κ η hdmin hdmax hτ hε he
    he' hκ hκ' hη hη2 hbudget
  refine ⟨Z₀, ?_⟩
  intro Z hZ d hd hd' hU Row Label Slot _ χ hχ rows slots Q widths a mesh binWidth εm C height
    a0 a1 k wlo P ε' i hbud ha hν hk0 hk hlo hmesh hbin hC hheight hε' ha1 ha1' hfreq hnext hcur
    hmod hw hwm hQ hmom
  have hwit := hZ₀ Z hZ d hd hd' χ hχ a i hbud ha (by linarith) hnext hcur hmod
  exact anchor_batch_maxW rows slots χ Q widths (Z^d) a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) mesh
    binWidth εm C height a0 a1 k wlo P ε' i hU (by linarith) hν hk0 hk hlo hε.le hεs hmesh hbin hC
    hheight hε' hfreq hw hwm ha1 ha1' (fun t h1 h2 => hwit t h1 h2) hQ hmom

/-! ### Restoration for the floored price -/

section Restore
variable {a0 a1 k wlo : ℝ}

theorem scaled_detPriceW (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d : ℝ} (hd : 0 < d) :
    d * detPriceW a0 a1 k wlo (P / d) (S / d) 1 ≤ detPriceW a0 a1 k wlo P S d := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have key : detPriceW a0 a1 k wlo (P / d) (S / d) 1 ≤ (detPriceW a0 a1 k wlo P S d + ε) / d := by
    refine supC_le hk1 fun p hp => ?_
    have h1 := infW_le_detPriceW (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hp P S d
    obtain ⟨w, hw, hlt⟩ := exists_lt_infW
      (show infW (fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P S d) <
        infW (fun w => detEx a0 a1 p.1 p.2 (fl wlo w) P S d) + ε by linarith)
    refine (infW_le (fun w hw => (detEx_bounds hk0 hp (fl_mem hw) (P / d) (S / d) 1).1) hw).trans ?_
    rw [le_div_iff₀ hd, mul_comm, Cofactor.detEx_scale p.1 p.2 (fl wlo w) P S hd]
    linarith
  rw [le_div_iff₀ hd] at key
  linarith

theorem restored_price_leW (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d M : ℝ} (hd : 0 < d)
    (hdM : d ≤ M) (hS : 0 ≤ S) :
    (M - d) / 6 + d + highPriceFW a0 a1 k wlo P S d ≤ M + highPriceFW a0 a1 k wlo P S M := by
  have h := highPriceFW_le_add (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) (s := S) (M := M)
    (P' := P) (s' := S) (M' := d) (c := 5 * (M - d) / 6) hk0 hk1 (by linarith)
    (by unfold tinyEx; linarith) (fun p hp w hw => by
      obtain ⟨h1, h2, h3, h4⟩ := hp
      exact Cofactor.detEx_restored hd hdM h2 h3 hS hw)
  linarith

theorem scaled_maxDetW_le (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d : ℝ} (hd : 0 < d) :
    d * max 0 (detPriceW a0 a1 k wlo (P / d) (S / d) 1) ≤ highPriceFW a0 a1 k wlo P S d := by
  rw [mul_max_of_nonneg _ _ hd.le, mul_zero]
  exact max_le (highPriceFW_nonneg a0 a1 k wlo P S d)
    ((scaled_detPriceW hk0 hk1 hd).trans (detPriceW_le_highPriceFW a0 a1 k wlo P S d))

/-- **Core batch exponent restored to the raw radius**, floored price, every `d ∈ (0, M]`. -/
theorem core_restored_le_detW (hk0 : 0 ≤ k) (hk1 : k ≤ 3 / 4) {P S d M : ℝ} (hd : 0 < d)
    (hdM : d ≤ M) (hS : 0 ≤ S) :
    (M - d) / 6 + d * (1 + max 0 (detPriceW a0 a1 k wlo (P / d) (S / d) 1)) ≤
      M + highPriceFW a0 a1 k wlo P S M := by
  have h1 := scaled_maxDetW_le (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) (S := S) hk0 hk1 hd
  have h2 := restored_price_leW (a0 := a0) (a1 := a1) (wlo := wlo) (P := P) hk0 hk1 hd hdM hS
  nlinarith

/-- Tiny cores against the floored price. -/
theorem tiny_restored_leW {P S d M : ℝ} (hd : d ≤ 2 / 25) :
    (M - d) / 6 + (d + 3 / 4 * P + S) ≤ M + highPriceFW a0 a1 k wlo P S M := by
  have := tinyEx_le_highPriceFW a0 a1 k wlo P S M
  unfold tinyEx at this
  linarith

end Restore

end
end Qrh.MarkedAnchor.High
