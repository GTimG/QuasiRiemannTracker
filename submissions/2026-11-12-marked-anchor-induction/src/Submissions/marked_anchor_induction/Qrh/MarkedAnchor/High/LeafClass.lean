/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's whole-family raw/core comparison and core conductors
(`Record12518109Gain/WholeRawTransport.lean`, `WholeConductor.lean`, `WholeRegularSetup.lean`,
Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafCoreBatch
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafAlgebra
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeRawTransport
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeConductor
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeRegularSetup

/-!
# High.LeafClass

The per-class core-batch lemma of the HIGH leaf: one batch `F` of
regular sixth-free cores `u` of one cofactor class `B` (raw rows `z = u·B⁶`), all in one buffered
zero bin, at the core scale `q = dB + margin`.

Inputs (per raw row, supplied by the leaf from `High.RowSplit.high_row_split` and HC's
`actual_high_slots`): the pointwise row bound `rowsq u ≤ K1 Z^((2a-1)P) ∏_{x∈T} ns u x`, the small
slots `ns ≤ Csm`, and the large slots `ns = ‖rawQ‖²` (`High.LeafSlots.state_slot_norm_eq`).

Steps: HC `eventually_whole_original_raw_max_comparison` (`Bmask = 0`, `R u = 1`, `hkeep` by
`whole_regular_retained`, `hlarge` from `w ≥ wmin`) replaces the raw slots by the core slots
(`4^#big`); `High.LeafCoreSlot.core_slot_bound` (conductors from HC `eventually_whole_core_conductor`)
gives the envelope `‖coreSlot‖ ≤ Cc Z^(ε₁ d) (Z^w)^((2a-1)/2)`; `High.LeafCoreBatch.core_batch_class`
gives the detector bound at `Z^q`; `High.LeafAlgebra.raw_batch_le` assembles.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDyadic Cycle61Moment CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local instance leafClassQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **One regular core batch of one cofactor class, raw rows.** -/
theorem core_class_batch (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) {a0 a1 wlo : ℝ}
    (hM : HighMarkedCoreInputsH a0 a1 wlo) (εm : ℝ) (hεm : 0 < εm) :
    ∃ meshm : ℝ, 0 < meshm ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
      (hH : RayOrthogonality.globalUnits rayM ≤ H)
      (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
      ∀ (η η₀ : Character) {α : Type} [Fintype α] [DecidableEq α] (wmin dmin dmax : ℝ),
      0 < wmin → 0 < dmin → dmin ≤ dmax →
      ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (τ ε e ηw bw ηd margin Broot d ε₁ kap v : ℝ), 0 < τ → 0 < ε → ε ≤ 1/1000000 →
        0 < e → e < 1/1000 → 0 ≤ ηw → ηw ≤ 2 → 12*e*((22:ℝ)+2)+8*e+2*ηw ≤ ε/2 → 0 < bw →
        0 < ηd → 0 < margin → 0 ≤ Broot → dmax ≤ d → 0 < ε₁ → 0 < kap → 0 ≤ v →
        8*e*(1/d)+kap ≤ ε₁ →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Cc : ℝ, 1 ≤ Cc ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 2 < Z^τ ∧
      ∀ (dB : ℝ), dmin ≤ dB + margin → dB + margin ≤ dmax →
      ∀ (B : NZIdeal) (F : Finset FreeRow) (T big : Finset α)
        (θ : α → RayQuotient.Characters rayM H) (w σ vv : α → ℝ)
        (t height mesh a k P ε' K1 Csm : ℝ) (i : ℕ)
        (rowsq : FreeRow → ℝ) (ns : FreeRow → α → ℝ),
      (B.val.absNorm : ℝ) ≤ Z^Broot →
      (∀ u ∈ F, ProbeHighRowFamily.rowNorm u ≤ Z^dB) →
      (∀ u ∈ F, RegularCore rayM H hH η η₀ u) →
      big ⊆ T → (∀ x ∈ big, wmin ≤ w x) → (∀ x ∈ big, w x ≤ 1) → 0 ≤ mesh →
      (∀ x ∈ big, w x ≤ mesh) → mesh/(dB+margin) ≤ meshm →
      (∀ x ∈ big, σ x = 33/50) → (∀ x ∈ big, |vv x| ≤ height) → 0 ≤ height → |t| ≤ height →
      (∀ x ∈ big, |t + vv x| + Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^(dB+margin))^ηw →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^v →
      51/100 < a → a ≤ 1 → 2*a-1 ≤ 3/4 → 0 ≤ k → k ≤ 2*a-1 → wlo ≤ cutHi → 0 ≤ a1 →
      a1 ≤ 1/2 → 0 < ε' → 0 ≤ K1 → 1 ≤ Csm →
      (∀ u ∈ F, ∀ hn : (∀ j, (coreFamily rayM H hH η η₀ u j).residue ≠ 1),
        HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ u) hn (3*(i+1 : ℕ)*Z^τ) <
          a+2*e ∧
        a ≤ HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ u) hn ((3*i : ℕ)*Z^τ)) →
      (∀ u ∈ F, ∀ x ∈ T, 0 ≤ ns u x) →
      (∀ u ∈ F, rowsq u ≤ K1 * Z^((2*a-1)*P) * ∏ x ∈ T, ns u x) →
      (∀ u ∈ F, ∀ x ∈ T, x ∉ big → ns u x ≤ Csm) →
      (∀ u ∈ F, ∀ x ∈ big, ns u x = ‖naturalSlot
        (excluded (naturalRow η (ProbePhysical.sixthFrequencyEquiv (u, B)).val
          (ProbePhysical.sixthFrequencyEquiv (u, B)).property).character 1)
        (primePool rayM H 2 (Z^(w x)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ x)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w x)) (σ x) (t + vv x) I) (Z^(w x))‖^2) →
      ∑ u ∈ F, rowsq u ≤ K1 * Csm^(T \ big).card * 4^big.card *
        (((Cc * Z^(ε₁*d))^2)^big.card *
          (Kc * (1 + (2*Real.pi*((Z^(dB+margin))^(τ/(2*dmax))) + ((3*i : ℕ) : ℝ)*Z^τ +
            (|t| + height)))^(J+1)) *
          (Z^(dB+margin))^(1 + max 0 (detPriceW a0 a1 k wlo (P/(dB+margin))
              (∑ x ∈ big, w x / (dB+margin)) 1) + ε' +
            (154*ε + (2*a-1)*(mesh/(dB+margin)) + εm + 2*bw*(∑ x ∈ big, w x / (dB+margin))) +
            ηd)) := by
  obtain ⟨meshm, hmeshm, hcls⟩ := core_batch_class hβ hM εm hεm
  refine ⟨meshm, hmeshm, ?_⟩
  intro rayM _ H hH W hWs hW η η₀ α _ _ wmin dmin dmax hwmin hdmin hdd
  obtain ⟨J, C, hC, hcls'⟩ := hcls rayM H hH W hWs hW η η₀ (Slot := α) wmin dmin dmax hwmin
    hdmin hdd
  refine ⟨J, C, hC, ?_⟩
  intro τ ε e ηw bw ηd margin Broot d ε₁ kap v hτ hε hε1 he he' hηw hηw2 hbud hbw hηd hmargin
    hBroot hdmaxd hε₁ hkap hv hslot
  have hd : 0 < d := (hdmin.trans_le hdd).trans_le hdmaxd
  obtain ⟨Kc, hKc, hev3⟩ := hcls' τ ε e ηw bw ηd hτ hε hε1 he he' hηw hηw2 hbud hbw hηd
  obtain ⟨Cc, hCc, hcs⟩ := core_slot_bound rayM H hH W hWs hW (1/d) d τ ε₁ e kap v
    (by positivity) hd.le hτ hε₁ he he' hkap hv hslot
  refine ⟨Kc, hKc, Cc, hCc, ?_⟩
  have hlargeEv : ∀ᶠ Z : ℝ in atTop, ∀ j : WholeSourceIndex rayM H,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase
        (ProbeHighRowFamily.momentData (Record12518109Natural.cleanWholeBase rayM H hH η η₀ j))).modulus.absNorm
          : ℝ) < Z^wmin :=
    Filter.eventually_all.mpr fun j =>
      (tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop _)
  filter_upwards [hev3,
    Record12518109GainWholeGeometry.eventually_whole_core_conductor rayM H hH η η₀ margin hmargin,
    Record12518109GainWholeRaw.eventually_whole_original_raw_max_comparison (Slot := α) rayM H hH
      η η₀ (Record12518109GainWholeGeometry.wholeRegularBad rayM H hH η η₀) W (33/50) (33/50) 0
      Broot wmin hWs hW le_rfl hBroot hwmin,
    hlargeEv, (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2),
    (tendsto_rpow_atTop hd).eventually (eventually_ge_atTop 2)] with Z hZ3 hZc hZr hZl hZτ hZd
  refine ⟨hZ3.1, hZτ, ?_⟩
  intro dB hq1 hq2 B F T big θ w σ vv t height mesh a k P ε' K1 Csm i rowsq ns hBN hnorm hreg
    hbigT hwmin' hw1 hmesh hwm hmm hσ hv hh0 ht hwin hgate4 hgate2 ha ha1 hν hk0 hk hlo ha1'
    ha1'' hε' hK1 hCsm hguard hns hrow hsmall hbig
  have hZ1 : 1 < Z := hZ3.1
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hq0 : 0 < dB + margin := hdmin.trans_le hq1
  have hdBq : dB ≤ dB + margin := by linarith
  -- the core slot envelope
  have hQ : ∀ u ∈ F, ∀ x ∈ big,
      ‖coreSlot rayM H hH η η₀ W (Z^(dB+margin)) θ (fun s => w s / (dB+margin)) σ vv
        (fun _ => t) u x‖ ≤ (Cc * Z^(ε₁*d)) * (Z^(w x))^((2*a-1)/2) := by
    intro u hu x hx
    have hn := core_nonprincipal rayM H hH η η₀ u (hreg u hu)
    have hb := hcs Z d hZ1.le hd.le le_rfl hZd hZτ
      (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀)) η₀ u.val u.property.1
      hn (θ x) a i ha.le ha1 (hguard u hu hn).1 (w x / d) (σ x) (t + vv x)
      (div_nonneg (hwmin.le.trans (hwmin' x hx)) hd.le)
      (div_le_div_of_nonneg_right (hw1 x hx) hd.le) (hσ x hx).ge (hσ x hx).le
      (fun θ' => ((hZc.2 dB u (hnorm u hu)).2 (θ x) θ').trans
        (Real.rpow_le_rpow_of_exponent_le hZ1.le (hq2.trans hdmaxd))) (hwin x hx) hgate2
    have e1 : (Z^d)^(w x / d) = Z^(w x) := scale_rescale hZ0 hd
    have e2 : (Z^(dB+margin))^(w x / (dB+margin)) = Z^(w x) := scale_rescale hZ0 hq0
    have e3 : (Z^d)^((a-1/2)*(w x/d)+ε₁) = Z^(ε₁*d) * (Z^(w x))^((2*a-1)/2) := by
      rw [← Real.rpow_mul hZ0.le, ← Real.rpow_mul hZ0.le, ← Real.rpow_add hZ0]
      congr 1
      field_simp
      ring
    rw [e1, e3] at hb
    have hcs_eq : coreSlot rayM H hH η η₀ W (Z^(dB+margin)) θ (fun s => w s / (dB+margin)) σ vv
        (fun _ => t) u x =
        naturalSlot (naturalRow (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀))
          u.val u.property.1).character (primePool rayM H 2 (Z^(w x)))
          (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ x)) I *
            HeckePrimeAnnular.annularWeight W (Z^(w x)) (σ x) (t + vv x) I) (Z^(w x)) := by
      unfold coreSlot
      rw [e2]
    rw [hcs_eq, mul_assoc]
    exact hb
  -- the raw/core comparison
  have hrowq : ∀ u ∈ F, ((Ideal.span {u.val}).absNorm : ℝ) ≤ Z^(dB+margin) := fun u hu =>
    (hnorm u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ1.le hdBq)
  have hnormq : ∀ u ∈ F, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z^(dB+margin) := fun u hu => by
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact hrowq u hu
  have hkeep : ∀ u ∈ F, ∀ j, CenteredMomentDetectorEnergyInitialState.initialKeep
      (Record12518109Natural.cleanWholeBase rayM H hH η η₀ j)
      (CenteredMomentNaturalFixedRaySource.internalQ (Record12518109GainWholeGeometry.wholeRegularBad rayM H hH η η₀ j)
        (Record12518109Natural.wholeSourceAnchor rayM H hH η₀ j)) u.val := fun u hu j =>
    Record12518109GainWholeGeometry.whole_regular_retained rayM H hH η η₀ F u
      (Finset.mem_filter.mpr ⟨hu, hreg u hu⟩) j
  have hlarge : ∀ x ∈ big, ∀ j,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase
        (ProbeHighRowFamily.momentData (Record12518109Natural.cleanWholeBase rayM H hH η η₀ j))).modulus.absNorm
          : ℝ) < (Z^(dB+margin))^(w x / (dB+margin)) := fun x hx j => by
    rw [scale_rescale hZ0 hq0]
    exact (hZl j).trans_le (Real.rpow_le_rpow_of_exponent_le hZ1.le (hwmin' x hx))
  have hcmp : ∑ u ∈ F, ∏ x ∈ big, max 1 (‖naturalSlot
        (excluded (naturalRow η (ProbePhysical.sixthFrequencyEquiv (u, B)).val
          (ProbePhysical.sixthFrequencyEquiv (u, B)).property).character 1)
        (primePool rayM H 2 (Z^(w x)))
        (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ x)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w x)) (σ x) (t + vv x) I) (Z^(w x))‖^2) ≤
      4^big.card * ∑ u ∈ F, ∏ x ∈ big, max 1 (‖coreSlot rayM H hH η η₀ W (Z^(dB+margin)) θ
        (fun s => w s / (dB+margin)) σ vv (fun _ => t) u x‖^2) :=
    hZr.2 (dB+margin) hq0 F big w σ vv (fun _ => t) θ hwmin' (fun x hx => (hσ x hx).ge)
      (fun x hx => (hσ x hx).le) hrowq hnormq hkeep hlarge B (fun _ => (1 : Ideal O)) hBN
      (fun _ _ => one_ne_zero) (fun _ _ => by simp)
  -- the core detector bound
  have hA : 1 ≤ Cc * Z^(ε₁*d) :=
    one_le_mul_of_one_le_of_one_le hCc (Real.one_le_rpow hZ1.le (by positivity))
  have hpi : 0 ≤ 2*Real.pi*((Z^(dB+margin))^(τ/(2*dmax))) := by
    have := Real.pi_pos
    have := Real.rpow_nonneg (Real.rpow_nonneg hZ0.le (dB+margin)) (τ/(2*dmax))
    positivity
  have hiZ : 0 ≤ ((3*i : ℕ) : ℝ)*Z^τ := by
    have := Real.rpow_nonneg hZ0.le τ; positivity
  have hcore := hZ3.2 (dB+margin) hq1 hq2 F big θ w σ vv (fun _ => t) a
    (2*Real.pi*((Z^(dB+margin))^(τ/(2*dmax))) + ((3*i : ℕ) : ℝ)*Z^τ + (|t| + height)) mesh
    (Cc * Z^(ε₁*d)) k P ε' i hrowq hreg (fun u hu j => (hZc.2 dB u (hnorm u hu)).1 j)
    (fun u _ => by have := abs_nonneg t; linarith) hwmin' hmesh hwm hmm hσ
    (fun x hx => by have := hv x hx; have := abs_nonneg t; linarith) hgate4 ha hν hk0 hk hlo
    ha1' ha1'' hε' hA (by have := abs_nonneg t; linarith) hguard hQ
  exact raw_batch_le F T big rowsq ns _ _ K1 (Z^((2*a-1)*P)) Csm _ hK1
    (Real.rpow_nonneg hZ0.le _) hCsm hbigT hns hrow hsmall
    (fun u hu x hx => by rw [hbig u hu x hx]; exact le_max_right _ _) hcmp hcore

end
end Qrh.MarkedAnchor.High
