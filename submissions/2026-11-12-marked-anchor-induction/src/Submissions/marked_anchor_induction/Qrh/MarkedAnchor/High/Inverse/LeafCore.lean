/- Copyright (c) 2026 Sil. Apache-2.0.
The bin bookkeeping follows `High/LeafBranch.lean` (`class_bound`). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Inverse.LeafAux

/-!
# High.Inverse.LeafCore — one cofactor class of the inverse HIGH leaf

Fixed scale `Z`, common twist `tw`, slots `x ∈ T ⊆ Fin K` (widths `ell'`, heights `v'`), cofactor
`B` with core width `dB > 2/25`:

* `row_bin_select` — every regular SlotHigh core `c` (raw row `c·B⁶`) lies in a zero bin
  `(j, a) = (⌈7|θ|+hv⌉ + m, (1+k)/2 + q·2e)` with `m ≤ Ne`, `q ≤ Pmax` (`exists_zero_bin`; `q ≥ 0`
  from `canonical_envelope` + the LOW slot supplier `slotHighT_lt`);
* `regular_class_bound` — the regular cores, grouped by `(m, q)`, each group by
  `High.core_class_batch` (`CoreBatchAt`), `bin_exponent_le`, `bin_constant_le`;
* `class_bound` — plus the exceptional cores (at most `E`, whole-row bound).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local notation "sfe" => ProbePhysical.sixthFrequencyEquiv
local instance leafCoreQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The squared canonical slot `x` of the raw row `w`. -/
def invNs (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (data : RowData)
    (tw : RayQuotient.Characters rayM G.twist) (Z : ℝ) {α : Type} (ell v : α → ℝ) (w : O)
    (x : α) : ℝ :=
  ‖directSlot w (canonicalPool rayM G.pool (Z^(ell x)))
    (rayCoeff rayM G hH W (33/50) data tw (Z^(ell x)) (v x)) (Z^(ell x))‖^2

/-- Both buffered guards of the core family of `c` at bin value `a`, height index `j`. -/
def CoreGuard (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (η η₀ : Character) (c : FreeRow)
    (Z τ e a : ℝ) (j : ℕ) : Prop :=
  ∀ hn : (∀ i, (coreFamily rayM H hH η η₀ c i).residue ≠ 1),
    HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ c) hn (3*(j+1 : ℕ)*Z^τ) <
      a + 2*e ∧
    a ≤ HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ c) hn ((3*j : ℕ)*Z^τ)

theorem window_ok {Z τ x : ℝ} {j : ℕ} (hZτ : 1 ≤ Z^τ) (h : |x| ≤ (j:ℝ)) :
    |x| + Z^τ/2 ≤ ((3*j+2 : ℕ) : ℝ)*Z^τ := by
  push_cast
  have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hZτ) hj0]

/-- **Zero bin of a regular HIGH core.** -/
theorem row_bin_select (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (Φ : ℝ → ℂ) (data : RowData)
    (tw : RayQuotient.Characters rayM G.twist) {K : ℕ} (T : Finset (Fin K))
    (ell' v' : Fin K → ℝ) {Z τ ε₁ e ηw Cr Cs k lam lam' wmin hv θ : ℝ} {Ne Pmax : ℕ}
    (hri : RowInputsAt rayM G hH W Φ data τ ε₁ ε₁ e ηw Cr Cs tw Z)
    (hZ1 : 1 < Z) (hZτ : 1 ≤ Z^τ) (he : 0 < e) (he' : e < 1/1000) (hk0 : 1/6 ≤ k)
    (hηw : 0 ≤ ηw)
    (hgate : ∀ j : ℕ, j ≤ ⌈7*|θ|+hv⌉₊ + Ne → (3+((3*j+2 : ℕ) : ℝ)*Z^τ)^4 ≤ Z^((2/25)*ηw))
    (hNe : (49/100:ℝ) ≤ Ne*(2*e)) (hPmax : 1/(4*e) ≤ (Pmax:ℝ))
    (h4 : 4*ε₁ ≤ lam') (hwl : wmin ≤ lam') (hlam : lam' < lam)
    (hdel : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) <
      Z^wmin)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < Z^wmin)
    (hell0 : ∀ x ∈ T, 0 ≤ ell' x) (hell1 : ∀ x ∈ T, ell' x ≤ 1)
    (hvb : ∀ x ∈ T, |v' x| ≤ hv)
    (hβT : ∀ x ∈ T, ∀ P ∈ canonicalPool rayM G.pool (Z^(ell' x)),
      ‖rayCoeff rayM G hH W (33/50) data tw (Z^(ell' x)) (v' x) P‖ ≤ 1)
    (c : FreeRow) (B : NZIdeal)
    (hreg : RegularCore rayM G.pool (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw) c)
    (hN : ((Ideal.span {(sfe (c, B)).val}).absNorm : ℝ) ≤ Z)
    (hhigh : ∃ x ∈ T, (65536 + Cs^2) * Z^(k * ell' x + lam) <
      invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x) :
    ∃ mq : ℕ × ℕ, mq ∈ Finset.range (Ne+1) ×ˢ Finset.range (Pmax+1) ∧
      CoreGuard rayM G.pool (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw) c Z τ e
        ((1+k)/2 + (mq.2:ℝ)*(2*e)) (⌈7*|θ|+hv⌉₊ + mq.1) := by
  have hZ0 : 0 < Z := by linarith
  have hnc := core_nonprincipal rayM G.pool (hHpool G hH) (dataBase data)
    (twistEta rayM G hH data tw) c hreg
  obtain ⟨j, hj1, hj2, p, hlo, hup⟩ := exists_zero_bin (coreFamily rayM G.pool (hHpool G hH)
    (dataBase data) (twistEta rayM G hH data tw) c) hnc (Z^τ) k e he (⌈7*|θ|+hv⌉₊) Ne hNe
  have hzb := HeckeDetectorZeros.zeroMaximum_bounds _ hnc ((3*j : ℕ)*Z^τ)
  have ha1 : (1+k)/2 + p*(2*e) ≤ 1 := hlo.trans hzb.2
  have hup' : HeckeDetectorZeros.zeroMaximum (coreFamily rayM G.pool (hHpool G hH)
      (dataBase data) (twistEta rayM G hH data tw) c) hnc (3*(j+1 : ℕ)*Z^τ) <
      max ((1+k)/2 + p*(2*e)) (51/100) + 2*e :=
    hup.trans_le (by linarith [le_max_left ((1+k)/2 + p*(2*e)) (51/100)])
  have hconv : Z^((2/25)*ηw) ≤ (Z^(2:ℝ))^ηw := by
    rw [← Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by nlinarith)
  obtain ⟨-, hii⟩ := hri c B hnc hN (max ((1+k)/2 + p*(2*e)) (51/100)) j (le_max_right _ _)
    (max_le ha1 (by norm_num)) hup' ((hgate j hj2).trans hconv)
  have hi0j : ((⌈7*|θ|+hv⌉₊ : ℕ) : ℝ) ≤ j := by exact_mod_cast hj1
  have hvi0 : hv ≤ ((⌈7*|θ|+hv⌉₊ : ℕ) : ℝ) :=
    le_trans (by linarith [abs_nonneg θ]) (Nat.le_ceil _)
  have henv := canonical_envelope rayM G hH W hWs data tw hZ1
    (le_max_right ((1+k)/2 + p*(2*e)) (51/100)) he h4 hwl hdel hfbm (ι := T)
    (fun x => ell' x.1) (fun x => v' x.1) (fun x => hell0 x.1 x.2) (fun x => hβT x.1 x.2)
    (sfe (c, B)).val (sfe (c, B)).property
    (fun x _ => hii (ell' x.1) (v' x.1) (hell0 x.1 x.2) (hell1 x.1 x.2)
      (window_ok hZτ ((hvb x.1 x.2).trans (hvi0.trans hi0j))))
  have hk := slotHighT_lt (T := T) (ns := invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val)
    (ell := ell') hZ1 (by positivity : (0:ℝ) < 65536 + Cs^2) le_rfl hlam hell0
    (fun x hx => henv ⟨x, hx⟩) hhigh
  have ha51 : 51/100 ≤ (1+k)/2 + p*(2*e) := by
    by_contra hlt
    push Not at hlt
    rw [max_eq_right hlt.le] at hk
    linarith
  rw [max_eq_left ha51] at hk
  obtain ⟨-, hp0⟩ := grid_ge (by positivity : (0:ℝ) < 2*e) p hk
  have hq : ((p.toNat : ℕ) : ℝ) = (p : ℝ) := by
    have := Int.toNat_of_nonneg hp0
    exact_mod_cast this
  have hqP : p.toNat ≤ Pmax := by
    have h1 : (p:ℝ)*(2*e) ≤ 5/12 := by linarith
    have h2 : ((p.toNat : ℕ):ℝ) ≤ 1/(4*e) := by
      rw [hq, le_div_iff₀ (by positivity)]
      have : (p:ℝ)*(4*e) = 2*((p:ℝ)*(2*e)) := by ring
      linarith
    exact_mod_cast h2.trans hPmax
  refine ⟨(j - ⌈7*|θ|+hv⌉₊, p.toNat), ?_, ?_⟩
  · simp only [Finset.mem_product, Finset.mem_range]
    omega
  · show CoreGuard rayM G.pool (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw) c Z τ e
      ((1+k)/2 + ((p.toNat : ℕ):ℝ)*(2*e)) (⌈7*|θ|+hv⌉₊ + (j - ⌈7*|θ|+hv⌉₊))
    rw [hq, Nat.add_sub_cancel' hj1]
    exact fun _ => ⟨hup, hlo⟩

/-- **The regular cores of one cofactor class.** -/
theorem regular_class_bound (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ)
    (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (Φ : ℝ → ℂ) (data : RowData)
    (tw : RayQuotient.Characters rayM G.twist)
    {a0 a1 k wlo : ℝ} (hk0 : 1/6 ≤ k) (hk1 : k ≤ 3/4) (hlo : wlo ≤ cutHi) (ha1 : 0 ≤ a1)
    (ha1' : a1 ≤ 1/2)
    {K J Jo Ne Pmax : ℕ}
    {εm meshm wmin τ εd ηw bw δs margin ε₁ e Kc Cc Cr Cs Z lam lam' mesh hv θ r dB : ℝ}
    (hcb : CoreBatchAt rayM G.pool (hHpool G hH) W (dataBase data) (twistEta rayM G hH data tw)
      (Fin K) a0 a1 wlo εm meshm wmin (2/25) 2 J τ εd ηw bw δs margin 1 2 ε₁ ηw e Kc Cc Z)
    (hri : RowInputsAt rayM G hH W Φ data τ ε₁ ε₁ e ηw Cr Cs tw Z)
    (hZ1 : 1 < Z) (hZτ : 1 ≤ Z^τ) (hτ : 0 < τ)
    (he : 0 < e) (he' : e < 1/1000) (hNe : (49/100:ℝ) ≤ Ne*(2*e)) (hPmax : 1/(4*e) ≤ (Pmax:ℝ))
    (h4 : 4*ε₁ ≤ lam') (hwl : wmin ≤ lam') (hlam : lam' < lam) (hwmin : 0 < wmin)
    (hε₁ : 0 < ε₁) (hηw : 0 ≤ ηw) (hδs : 0 < δs) (hεd : 0 ≤ εd) (hεm : 0 ≤ εm) (hbw : 0 ≤ bw)
    (hmargin : 0 < margin) (hmargin2 : margin ≤ 1/2) (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmeshm : mesh ≤ meshm * (2/25)) (hmeshm0 : 0 < meshm)
    (hJ : J + 1 ≤ Jo) (hCr : 0 < Cr) (hCc : 1 ≤ Cc) (hKc : 0 ≤ Kc)
    (hdel : ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ) <
      Z^wmin)
    (hfbm : ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ) < Z^wmin)
    (hv0 : 0 ≤ hv) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hgate : ∀ j : ℕ, j ≤ ⌈7*|θ|+hv⌉₊ + Ne → (3+((3*j+2 : ℕ) : ℝ)*Z^τ)^4 ≤ Z^((2/25)*ηw))
    (T : Finset (Fin K)) (ell' v' : Fin K → ℝ)
    (hell0 : ∀ x ∈ T, 0 ≤ ell' x) (hellm : ∀ x ∈ T, ell' x ≤ mesh)
    (hvb : ∀ x ∈ T, |v' x| ≤ hv)
    (hβT : ∀ x ∈ T, ∀ P ∈ canonicalPool rayM G.pool (Z^(ell' x)),
      ‖rayCoeff rayM G hH W (33/50) data tw (Z^(ell' x)) (v' x) P‖ ≤ 1)
    (B : NZIdeal) (hdB : 2/25 < dB) (hdB1 : dB ≤ 1) (hBN : (B.val.absNorm : ℝ) ≤ Z^(1:ℝ))
    (Fr : Finset FreeRow) (g : FreeRow → ℝ)
    (hFr : ∀ c ∈ Fr, RegularCore rayM G.pool (hHpool G hH) (dataBase data)
        (twistEta rayM G hH data tw) c ∧
      ((Ideal.span {(sfe (c, B)).val}).absNorm : ℝ) ≤ Z ∧ ProbeHighRowFamily.rowNorm c ≤ Z^dB)
    (hg : ∀ c ∈ Fr, g c ≤ ‖polynomial (data.character ⟨(sfe (c, B)).val, (sfe (c, B)).property⟩)
        true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0‖^2 *
      ∏ x ∈ T, invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x)
    (hhigh : ∀ c ∈ Fr, ∃ x ∈ T, (65536 + Cs^2) * Z^(k * ell' x + lam) <
      invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x) :
    ∑ c ∈ Fr, g c ≤ (((Ne+1)*(Pmax+1) : ℕ) : ℝ) *
      ((Cr * (4*65536*Cc^2)^K * Kc * (7*(8+6*((Ne:ℝ)+1)))^Jo) * 1 * ((1+‖θ‖+hv)*Z^τ)^Jo *
        Z^(2*ε₁*2*((K:ℝ)+1) + (K:ℝ)*wmin + (dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB +
          (margin + 2*(δs + 154*εd + εm + δs) + mesh + 2*bw*(K:ℝ))))) := by
  have hZ0 : 0 < Z := by linarith
  have hconv : ∀ y : ℝ, 2/25 ≤ y → Z^((2/25)*ηw) ≤ (Z^y)^ηw := fun y hy => by
    rw [← Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (mul_le_mul_of_nonneg_right hy hηw)
  have hsel : ∀ c ∈ Fr, ∃ mq : ℕ × ℕ, mq ∈ Finset.range (Ne+1) ×ˢ Finset.range (Pmax+1) ∧
      CoreGuard rayM G.pool (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw) c Z τ e
        ((1+k)/2 + (mq.2:ℝ)*(2*e)) (⌈7*|θ|+hv⌉₊ + mq.1) := fun c hc =>
    row_bin_select rayM G hH W hWs Φ data tw T ell' v' hri hZ1 hZτ he he' hk0 hηw hgate hNe
      hPmax h4 hwl hlam hdel hfbm hell0 (fun x hx => (hellm x hx).trans hmesh1) hvb hβT c B
      (hFr c hc).1 (hFr c hc).2.1 (hhigh c hc)
  choose! sel hselm hselg using hsel
  set i0 : ℕ := ⌈7*|θ|+hv⌉₊ with hi0
  set Kg : ℝ := (Cr * (4*65536*Cc^2)^K * Kc * (7*(8+6*((Ne:ℝ)+1)))^Jo) * 1 *
      ((1+‖θ‖+hv)*Z^τ)^Jo *
        Z^(2*ε₁*2*((K:ℝ)+1) + (K:ℝ)*wmin + (dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB +
          (margin + 2*(δs + 154*εd + εm + δs) + mesh + 2*bw*(K:ℝ)))) with hKg
  have hθn : ‖θ‖ = |θ| := Real.norm_eq_abs θ
  have hZτ0 : 0 ≤ Z^τ := by linarith
  have hY0 : 0 ≤ (1+‖θ‖+hv)*Z^τ := by
    have := norm_nonneg θ
    positivity
  have hKg0 : 0 ≤ Kg := by positivity
  have hi0r : (i0 : ℝ) < 7*|θ| + hv + 1 := Nat.ceil_lt_add_one (by positivity)
  have hi0l : 7*|θ| + hv ≤ (i0:ℝ) := Nat.le_ceil _
  have hgrp : ∀ mq ∈ Finset.range (Ne+1) ×ˢ Finset.range (Pmax+1),
      ∑ c ∈ Fr.filter (fun c => sel c = mq), g c ≤ Kg := by
    intro mq hmq
    obtain ⟨m, q⟩ := mq
    simp only [Finset.mem_product, Finset.mem_range] at hmq
    obtain ⟨hm, -⟩ := hmq
    set F := Fr.filter (fun c => sel c = (m, q)) with hF
    have hFm : ∀ c ∈ F, c ∈ Fr ∧ sel c = (m, q) := fun c hc => Finset.mem_filter.mp hc
    have hguardF : ∀ c ∈ F, CoreGuard rayM G.pool (hHpool G hH) (dataBase data)
        (twistEta rayM G hH data tw) c Z τ e ((1+k)/2 + (q:ℝ)*(2*e)) (i0 + m) := by
      intro c hc
      have h := hselg c (hFm c hc).1
      rw [(hFm c hc).2] at h
      exact h
    rcases F.eq_empty_or_nonempty with hFe | ⟨c₁, hc₁⟩
    · rw [hFe, Finset.sum_empty]; exact hKg0
    set a : ℝ := (1+k)/2 + (q:ℝ)*(2*e) with ha_def
    have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
    have ha_lo : (1+k)/2 ≤ a := by
      rw [ha_def]; have : 0 ≤ (q:ℝ)*(2*e) := by positivity
      linarith
    have hn₁ := core_nonprincipal rayM G.pool (hHpool G hH) (dataBase data)
      (twistEta rayM G hH data tw) c₁ (hFr c₁ (hFm c₁ hc₁).1).1
    have ha78 : a ≤ 7/8 :=
      (((hguardF c₁ hc₁ hn₁).2.trans (CenteredMomentPrimeGlobal.zeroMaximum_le_beta _ hn₁ _
        hβ)).trans Candidate.FourthPower.IncumbentInput.baseline_beta)
    have haone : a ≤ 1 := by linarith
    set j : ℕ := i0 + m with hj_def
    have hjN : j ≤ i0 + Ne := by omega
    have hg4 := hgate j hjN
    have hdBq1 : (2/25:ℝ) ≤ dB + margin := by linarith
    have hdBq2 : dB + margin ≤ 2 := by linarith
    have hq0' : 0 < dB + margin := by linarith
    have hjr : (i0:ℝ) ≤ (j:ℝ) := by exact_mod_cast (Nat.le_add_right i0 m)
    have hwin : ∀ y : ℝ, |y| ≤ 7*|θ| + hv → |y| + Z^τ/2 ≤ ((3*j+2 : ℕ):ℝ)*Z^τ :=
      fun y hy => window_ok hZτ (by linarith)
    have hθ7 : |2*Real.pi*θ| ≤ 7*|θ| + hv := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
      have hpi : 2*Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
      nlinarith [abs_nonneg θ]
    have h3 : (1:ℝ) ≤ 3+((3*j+2 : ℕ) : ℝ)*Z^τ := by
      have : (0:ℝ) ≤ ((3*j+2 : ℕ) : ℝ)*Z^τ := by positivity
      linarith
    set big : Finset (Fin K) := T.filter (fun x => wmin ≤ ell' x) with hbig
    have hZ4 : 1 ≤ Z^(2*ε₁*2) := Real.one_le_rpow hZ1.le (by positivity)
    have hCsm1 : (1:ℝ) ≤ 65536 * Z^(2*ε₁*2) * Z^wmin := by
      have := Real.one_le_rpow hZ1.le hwmin.le
      have : (1:ℝ) ≤ Z^(2*ε₁*2) * Z^wmin := one_le_mul_of_one_le_of_one_le hZ4 this
      nlinarith
    -- the row bound
    have hrow : ∀ c ∈ F, g c ≤ (Cr * 1 * Z^(2*ε₁*2)) * Z^((2*a-1)*r) *
        ∏ x ∈ T, invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x := by
      intro c hc
      have hcF := hFr c (hFm c hc).1
      have hnc := core_nonprincipal rayM G.pool (hHpool G hH) (dataBase data)
        (twistEta rayM G hH data tw) c hcF.1
      have hM := (hri c B hnc hcF.2.1 a j (by linarith) haone (hguardF c hc hnc).1
        (hg4.trans (hconv 2 (by norm_num)))).1 r θ hr0 hr1 (hwin _ hθ7)
      refine (hg c (hFm c hc).1).trans ?_
      have hP0 : 0 ≤ ∏ x ∈ T, invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x :=
        Finset.prod_nonneg fun x _ => sq_nonneg _
      have hK : Cr * Z^((2*a-1)*r + 2*ε₁) ≤ (Cr * 1 * Z^(2*ε₁*2)) * Z^((2*a-1)*r) := by
        rw [Real.rpow_add hZ0]
        have h1 : Z^(2*ε₁) ≤ Z^(2*ε₁*2) := Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
        have h0 : 0 ≤ Z^((2*a-1)*r) := Real.rpow_nonneg hZ0.le _
        have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCr.le h0)
        nlinarith
      calc _ ≤ Cr * Z^((2*a-1)*r + 2*ε₁) *
            ∏ x ∈ T, invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x :=
            mul_le_mul_of_nonneg_right hM hP0
        _ ≤ _ := mul_le_mul_of_nonneg_right hK hP0
    -- small slots
    have hsmall : ∀ c ∈ F, ∀ x ∈ T, x ∉ big →
        invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x ≤
          65536 * Z^(2*ε₁*2) * Z^wmin := by
      intro c _ x hx hxb
      have hlt : ell' x < wmin := by
        by_contra h
        exact hxb (Finset.mem_filter.mpr ⟨hx, not_lt.mp h⟩)
      have hD : 1 ≤ Z^(ell' x) := Real.one_le_rpow hZ1.le (hell0 x hx)
      have hD0 : 0 < Z^(ell' x) := zero_lt_one.trans_le hD
      have ht := trivial_slot (sfe (c, B)).val (canonicalPool rayM G.pool (Z^(ell' x)))
        (rayCoeff rayM G hH W (33/50) data tw (Z^(ell' x)) (v' x)) (Z^(ell' x)) hD
        (fun P hP => by
          simp only [canonicalPool, primePool, Finset.mem_filter] at hP
          refine ⟨hP.1.2.1.ne_zero, ?_⟩
          have := (div_le_iff₀ hD0).mp hP.2.2
          linarith) (hβT x hx)
      have hzw : Z^(ell' x) ≤ Z^wmin := Real.rpow_le_rpow_of_exponent_le hZ1.le hlt.le
      have hzw0 : 0 ≤ Z^wmin := Real.rpow_nonneg hZ0.le _
      calc invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x ≤ 65536 * Z^(ell' x) := ht
        _ ≤ 65536 * Z^wmin := by linarith
        _ ≤ 65536 * Z^(2*ε₁*2) * Z^wmin := by nlinarith
    -- big slots
    have hbigS : ∀ c ∈ F, ∀ x ∈ big,
        invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x = ‖naturalSlot
          (excluded (naturalRow (dataBase data) (sfe (c, B)).val (sfe (c, B)).property).character 1)
          (primePool rayM G.pool 2 (Z^(ell' x)))
          (fun I => idealCoeff (relativeCharacter rayM G.pool (hHpool G hH)
              (twistEta rayM G hH data tw) ((fun _ => (1 : RayQuotient.Characters rayM G.pool)) x)) I *
            HeckePrimeAnnular.annularWeight W (Z^(ell' x)) ((fun _ => (33/50 : ℝ)) x)
              (0 + v' x) I) (Z^(ell' x))‖^2 := by
      intro c _ x hx
      have hwx := (Finset.mem_filter.mp hx).2
      have hD0 : 0 < Z^(ell' x) := Real.rpow_pos_of_pos hZ0 _
      have hle := Real.rpow_le_rpow_of_exponent_le hZ1.le hwx
      unfold invNs
      rw [directSlot_eq_natural rayM G hH W hWs (33/50) data tw hD0 (v' x) (hdel.trans_le hle)
        (hfbm.trans_le hle), naturalSlot_excluded_one, zero_add]
    have hcbF := hcb dB hdBq1 hdBq2 B F T big (fun _ => 1) ell' (fun _ => 33/50) v' 0
      (hv + 7*|θ|) mesh a k r δs (Cr * 1 * Z^(2*ε₁*2)) (65536 * Z^(2*ε₁*2) * Z^wmin) j g
      (fun c x => invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x) hBN
      (fun c hc => (hFr c (hFm c hc).1).2.2)
      (fun c hc => (hFr c (hFm c hc).1).1)
      (Finset.filter_subset _ _)
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => (hellm x (Finset.mem_filter.mp hx).1).trans hmesh1)
      hmesh0
      (fun x hx => hellm x (Finset.mem_filter.mp hx).1)
      (by rw [div_le_iff₀ hq0']; nlinarith)
      (fun _ _ => rfl)
      (fun x hx => by
        have := hvb x (Finset.mem_filter.mp hx).1
        have := abs_nonneg θ
        linarith)
      (by have := abs_nonneg θ; positivity)
      (by rw [abs_zero]; have := abs_nonneg θ; positivity)
      (fun x hx => by
        rw [zero_add]
        exact hwin _ (by
          have := hvb x (Finset.mem_filter.mp hx).1
          have := abs_nonneg θ
          linarith))
      (hg4.trans (hconv _ hdBq1))
      (le_trans (pow_le_pow_right₀ h3 (by norm_num)) (hg4.trans (hconv 2 (by norm_num))))
      (by linarith) haone (by linarith) (by linarith) (by linarith) hlo ha1 ha1' hδs
      (by positivity) hCsm1 hguardF (fun _ _ _ _ => sq_nonneg _) hrow hsmall hbigS
    rw [← Finset.sum_div] at hcbF
    have hSbS : ∑ x ∈ big, ell' x ≤ ∑ x ∈ T, ell' x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x hx _ => hell0 x hx)
    have hSb0 : 0 ≤ ∑ x ∈ big, ell' x :=
      Finset.sum_nonneg fun x hx => hell0 x (Finset.mem_filter.mp hx).1
    have hTK : T.card ≤ K := (Finset.card_le_univ T).trans (by simp)
    have hSbN : ∑ x ∈ big, ell' x ≤ (K:ℝ) := by
      calc ∑ x ∈ big, ell' x ≤ ∑ _x ∈ big, (1:ℝ) := Finset.sum_le_sum fun x hx =>
            (hellm x (Finset.mem_filter.mp hx).1).trans hmesh1
        _ = (big.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ (K:ℝ) := by
            exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans hTK
    have hX := bin_exponent_le (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hk1
      (q := dB + margin) (dB := dB) (margin := margin) (Mc := 2) (P := r)
      (S := ∑ x ∈ T, ell' x) (Sb := ∑ x ∈ big, ell' x) (ε' := δs) (ε := εd) (εm := εm)
      (ηd := δs) (bw := bw) (mesh := mesh) (a := a) (N := (K:ℝ)) rfl (by linarith)
      hmargin.le hdBq2 hSb0 hSbS hSbN hδs.le hεd hεm hδs.le hbw hmesh0 (by linarith)
      (by linarith)
    have hYq : (Z^(dB+margin))^(τ/(2*2)) ≤ Z^τ := by
      rw [← Real.rpow_mul hZ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hZ1.le
      have : (dB+margin)*(τ/(2*2)) = τ*((dB+margin)/4) := by ring
      rw [this]
      nlinarith
    have hi : (j:ℝ) ≤ ((Ne:ℝ)+1)*((i0:ℝ)+1) := by
      have h1 : (j:ℝ) ≤ (i0:ℝ) + Ne := by exact_mod_cast hjN
      have : (0:ℝ) ≤ Ne := Nat.cast_nonneg _
      have : (0:ℝ) ≤ i0 := Nat.cast_nonneg _
      nlinarith
    have hfac := height_factor_le (Y := (Z^(dB+margin))^(τ/(2*2))) (y := Z^τ)
      (x := |(0:ℝ)| + (hv + 7*|θ|)) (i := j) (h := i0) (B := Ne) hYq hZτ
      (by have := abs_nonneg θ; positivity) hi (by rw [abs_zero]; linarith)
    have hHD1 : 1 ≤ 1 + (2*Real.pi*((Z^(dB+margin))^(τ/(2*2))) + ((3*j : ℕ) : ℝ)*Z^τ +
        (|(0:ℝ)| + (hv + 7*|θ|))) := by
      have : 0 ≤ 2*Real.pi*((Z^(dB+margin))^(τ/(2*2))) := by
        have := Real.pi_pos
        have := Real.rpow_nonneg (Real.rpow_nonneg hZ0.le (dB+margin)) (τ/(2*2))
        positivity
      have : 0 ≤ ((3*j : ℕ) : ℝ)*Z^τ := by positivity
      have := abs_nonneg θ
      rw [abs_zero]
      linarith
    have hHDY : 1 + (2*Real.pi*((Z^(dB+margin))^(τ/(2*2))) + ((3*j : ℕ) : ℝ)*Z^τ +
        (|(0:ℝ)| + (hv + 7*|θ|))) ≤ (7*(8+6*((Ne:ℝ)+1))) * ((1+‖θ‖+hv)*Z^τ) := by
      refine hfac.trans ?_
      rw [abs_zero, hθn]
      have hB0 : (0:ℝ) ≤ 8 + 6*((Ne:ℝ)+1) := by positivity
      have h1 : 1 + (0 + (hv + 7*|θ|)) ≤ 7*(1+|θ|+hv) := by linarith
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hB0) hZτ0
      calc (8 + 6*((Ne:ℝ)+1)) * (1 + (0 + (hv + 7*|θ|))) * Z^τ ≤
          (8 + 6*((Ne:ℝ)+1)) * (7*(1+|θ|+hv)) * Z^τ := this
        _ = _ := by ring
    have hn : (T \ big).card + big.card ≤ K := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)]
      exact hTK
    have hfin := bin_constant_le (Ch := 7*(8+6*((Ne:ℝ)+1))) (Y := (1+‖θ‖+hv)*Z^τ) (Jo := Jo)
      (N := K) (d := (2:ℝ)) hZ1 hCr.le zero_le_one (by norm_num : (1:ℝ) ≤ 65536) hCc hKc hHD1 hHDY hJ hn
      hε₁.le (by norm_num) hwmin.le hX
    exact hcbF.trans hfin
  calc ∑ c ∈ Fr, g c
      = ∑ mq ∈ Finset.range (Ne+1) ×ˢ Finset.range (Pmax+1),
          ∑ c ∈ Fr.filter (fun c => sel c = mq), g c :=
        (Finset.sum_fiberwise_of_maps_to (fun c hc => hselm c hc) g).symm
    _ ≤ ∑ _mq ∈ Finset.range (Ne+1) ×ˢ Finset.range (Pmax+1), Kg := Finset.sum_le_sum hgrp
    _ = _ := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range,
          nsmul_eq_mul]

end
end Qrh.MarkedAnchor.High.Inverse

#print axioms Qrh.MarkedAnchor.High.Inverse.regular_class_bound
