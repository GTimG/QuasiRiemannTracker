/- Modified by Joseph Bebel (2026-11-12): smaller-tolerance inverse
HIGH leaf; original coefficient, mask and principal-row proofs are retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The assembly follows `High/LeafBranch.lean` (`high_branch_mesh`); the sixth-power cofactor sum and
the exceptional cores are Hailey Collet's (`Record12518109Gain`, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.LeafCore
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.PrincipalSpike

/-!
# High.Inverse.Leaf — **the inverse HIGH leaf**

`inverseHighLeaf : InverseHighLeaf`.

For the fixed-ray canonical family (`canonicalSlotsRay W (33/50) rayM G hH`, common twist `tw`):
* large heights `Z^A ≤ ‖θ‖ + hv`: the trivial energy (`trivial_energy`), paid by the height
  degree `Jo + ⌈(1+K)/A⌉`;
* small heights: the SlotHigh rows of the ball, as nonzero frequencies, by sixth-power cofactor
  class (`high_cofactor_energyW` at `M = 1`):
  - tiny classes (`coreWidth ≤ 2/25`): `Cofactor.tiny_core_count` × the whole-row bound
    (`whole_row_spike`; principal row members by the principal inverse spike);
  - large classes: `class_bound` (exceptional cores pointwise, regular cores binned and batched by
    `High.core_class_batch`, `High.Inverse.LeafCore.regular_class_bound`).
* the slots `ι` are re-indexed into `Fin K` (`Fintype.equivFin`, `Fin.castLEEmb`,
  `Function.extend`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section
variable [shift : WitnessShift]
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local notation "sfe" => ProbePhysical.sixthFrequencyEquiv
local instance leafQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **One large cofactor class**: exceptional cores pointwise, regular cores batched. -/
theorem class_bound (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
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
    (fib : Finset FreeRow) (g : FreeRow → ℝ) (E : ℕ) (Kw εw lamv : ℝ) (hKw : 0 ≤ Kw)
    (hfib : ∀ c ∈ fib, ((Ideal.span {(sfe (c, B)).val}).absNorm : ℝ) ≤ Z ∧
      ProbeHighRowFamily.rowNorm c ≤ Z^dB)
    (hg : ∀ c ∈ fib, g c ≤ ‖polynomial (data.character ⟨(sfe (c, B)).val, (sfe (c, B)).property⟩)
        true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0‖^2 *
      ∏ x ∈ T, invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x)
    (hhigh : ∀ c ∈ fib, ∃ x ∈ T, (65536 + Cs^2) * Z^(k * ell' x + lam) <
      invNs rayM G hH W data tw Z ell' v' (sfe (c, B)).val x)
    (hwhole : ∀ c ∈ fib, g c ≤ Kw * Z^(3/4*r + (∑ x ∈ T, ell' x) + εw))
    (hE : ((fib.filter (fun c => ¬ RegularCore rayM G.pool (hHpool G hH) (dataBase data)
      (twistEta rayM G hH data tw) c)).card : ℝ) ≤ E)
    (hlamv : 2*ε₁*2*((K:ℝ)+1) + (K:ℝ)*wmin +
      (margin + 2*(δs + 154*εd + εm + δs) + mesh + 2*bw*(K:ℝ)) ≤ lamv)
    (hεw : εw ≤ lamv) :
    ∑ c ∈ fib, g c ≤ ((E:ℝ) * Kw + (((Ne+1)*(Pmax+1) : ℕ) : ℝ) *
      (Cr * (4*65536*Cc^2)^K * Kc * (7*(8+6*((Ne:ℝ)+1)))^Jo)) * ((1+‖θ‖+hv)*Z^τ)^Jo *
        Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv) := by
  have hZ0 : 0 < Z := by linarith
  have hY1 : 1 ≤ (1+‖θ‖+hv)*Z^τ :=
    one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg θ]) hZτ
  have hYJ : 1 ≤ ((1+‖θ‖+hv)*Z^τ)^Jo := one_le_pow₀ hY1
  have hEc0 : 0 ≤ Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv) :=
    Real.rpow_nonneg hZ0.le _
  rw [← Finset.sum_filter_not_add_sum_filter fib (fun c => RegularCore rayM G.pool (hHpool G hH)
    (dataBase data) (twistEta rayM G hH data tw) c) g]
  -- the exceptional cores
  have hexc : ∑ c ∈ fib.filter (fun c => ¬ RegularCore rayM G.pool (hHpool G hH) (dataBase data)
      (twistEta rayM G hH data tw) c), g c ≤ (E:ℝ) * (Kw * ((1+‖θ‖+hv)*Z^τ)^Jo *
        Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv)) := by
    have hexp : 3/4*r + (∑ x ∈ T, ell' x) + εw ≤
        dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv := by
      have ht := tinyEx_le_highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB
      unfold tinyEx at ht
      linarith
    have hpt : ∀ c ∈ fib.filter (fun c => ¬ RegularCore rayM G.pool (hHpool G hH)
        (dataBase data) (twistEta rayM G hH data tw) c), g c ≤
        Kw * ((1+‖θ‖+hv)*Z^τ)^Jo *
          Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv) := by
      intro c hc
      refine (hwhole c (Finset.mem_filter.mp hc).1).trans ?_
      have hz := Real.rpow_le_rpow_of_exponent_le hZ1.le hexp
      calc Kw * Z^(3/4*r + (∑ x ∈ T, ell' x) + εw)
          ≤ Kw * Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv) :=
            mul_le_mul_of_nonneg_left hz hKw
        _ = Kw * 1 * Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv) := by ring
        _ ≤ _ := by gcongr
    calc _ ≤ ∑ _c ∈ fib.filter (fun c => ¬ RegularCore rayM G.pool (hHpool G hH)
          (dataBase data) (twistEta rayM G hH data tw) c), Kw * ((1+‖θ‖+hv)*Z^τ)^Jo *
            Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv) :=
          Finset.sum_le_sum hpt
      _ = ((fib.filter (fun c => ¬ RegularCore rayM G.pool (hHpool G hH) (dataBase data)
            (twistEta rayM G hH data tw) c)).card : ℝ) * (Kw * ((1+‖θ‖+hv)*Z^τ)^Jo *
              Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hE (by positivity)
  -- the regular cores
  have hreg := regular_class_bound hβ rayM G hH W hWs Φ data tw hk0 hk1 hlo ha1 ha1' hcb hri hZ1
    hZτ hτ he he' hNe hPmax h4 hwl hlam hwmin hε₁ hηw hδs hεd hεm hbw hmargin hmargin2 hmesh0
    hmesh1 hmeshm hmeshm0 hJ hCr hCc hKc hdel hfbm hv0 hr0 hr1 hgate T ell' v' hell0 hellm hvb
    hβT B hdB hdB1 hBN (fib.filter (fun c => RegularCore rayM G.pool (hHpool G hH)
      (dataBase data) (twistEta rayM G hH data tw) c)) g
    (fun c hc => ⟨(Finset.mem_filter.mp hc).2, (hfib c (Finset.mem_filter.mp hc).1).1,
      (hfib c (Finset.mem_filter.mp hc).1).2⟩)
    (fun c hc => hg c (Finset.mem_filter.mp hc).1)
    (fun c hc => hhigh c (Finset.mem_filter.mp hc).1)
  have hzr : Z^(2*ε₁*2*((K:ℝ)+1) + (K:ℝ)*wmin + (dB + highPriceFW a0 a1 k wlo r
      (∑ x ∈ T, ell' x) dB + (margin + 2*(δs + 154*εd + εm + δs) + mesh + 2*bw*(K:ℝ)))) ≤
      Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv) :=
    Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have hKg0 : 0 ≤ Cr * (4*65536*Cc^2)^K * Kc * (7*(8+6*((Ne:ℝ)+1)))^Jo := by positivity
  have hYJ0 : 0 ≤ ((1+‖θ‖+hv)*Z^τ)^Jo := by linarith
  have hreg' : ∑ c ∈ fib.filter (fun c => RegularCore rayM G.pool (hHpool G hH)
      (dataBase data) (twistEta rayM G hH data tw) c), g c ≤
      (((Ne+1)*(Pmax+1) : ℕ) : ℝ) * ((Cr * (4*65536*Cc^2)^K * Kc * (7*(8+6*((Ne:ℝ)+1)))^Jo) *
        ((1+‖θ‖+hv)*Z^τ)^Jo * Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv)) := by
    refine hreg.trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left hzr (mul_nonneg hKg0 hYJ0)
  calc _ ≤ (E:ℝ) * (Kw * ((1+‖θ‖+hv)*Z^τ)^Jo *
        Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv)) +
      (((Ne+1)*(Pmax+1) : ℕ) : ℝ) * ((Cr * (4*65536*Cc^2)^K * Kc * (7*(8+6*((Ne:ℝ)+1)))^Jo) *
        ((1+‖θ‖+hv)*Z^τ)^Jo * Z^(dB + highPriceFW a0 a1 k wlo r (∑ x ∈ T, ell' x) dB + lamv)) :=
      add_le_add hexc hreg'
    _ = _ := by ring

/-- **The inverse HIGH leaf, from the principal inverse spike.** -/
theorem inverseHighLeaf_of_spike (hP : PrincipalSpikeHyp) : InverseHighLeaf := by
  have hshift1 := WitnessShift.le_fixed
  intro a0 a1 k wlo hβ hk0 hk1 ha1 ha1' hlo hm
  have hM := highMarkedCoreInputsH_of_inverse hm
  intro ε hε
  obtain ⟨εd, hεd_def⟩ : ∃ x : ℝ, x = min (WitnessShift.value) (ε/10000) := ⟨_, rfl⟩
  have hεd : 0 < εd := by rw [hεd_def]; exact lt_min WitnessShift.pos (by positivity)
  have hεd1 : εd ≤ WitnessShift.value := by rw [hεd_def]; exact min_le_left _ _
  have hεd2 : εd ≤ ε/10000 := by rw [hεd_def]; exact min_le_right _ _
  obtain ⟨εm, hεm_def⟩ : ∃ x : ℝ, x = ε/1000 := ⟨_, rfl⟩
  have hεm : 0 < εm := by rw [hεm_def]; positivity
  obtain ⟨meshm, hmeshm, hcls⟩ := core_class_batch_at hβ hM εm hεm
  obtain ⟨mesh, hmesh_def⟩ : ∃ x : ℝ, x = min (min (meshm*(2/25)/2) (ε/100)) 1 := ⟨_, rfl⟩
  have hmesh : 0 < mesh := by
    rw [hmesh_def]; exact lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hmeshA : mesh ≤ meshm*(2/25) := by
    rw [hmesh_def]
    have := min_le_left (min (meshm*(2/25)/2) (ε/100)) 1
    have := min_le_left (meshm*(2/25)/2) (ε/100)
    have : meshm*(2/25)/2 ≤ meshm*(2/25) := by linarith [mul_pos hmeshm (by norm_num : (0:ℝ) < 2/25)]
    linarith
  have hmeshB : mesh ≤ ε/100 := by
    rw [hmesh_def]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hmesh1 : mesh ≤ 1 := by rw [hmesh_def]; exact min_le_right _ _
  refine ⟨mesh, hmesh, ?_⟩
  intro K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data
  obtain ⟨W, hW, hWs, rayM, hne, G, hH, rfl⟩ := hcls
  -- parameters
  have hK1 : (0:ℝ) < (K:ℝ) + 1 := by positivity
  obtain ⟨margin, hmargin_def⟩ : ∃ x : ℝ, x = min (ε/100) (1/2) := ⟨_, rfl⟩
  have hmargin : 0 < margin := by rw [hmargin_def]; exact lt_min (by positivity) (by norm_num)
  have hmargin1 : margin ≤ ε/100 := by rw [hmargin_def]; exact min_le_left _ _
  have hmargin2 : margin ≤ 1/2 := by rw [hmargin_def]; exact min_le_right _ _
  obtain ⟨wmin, hwmin_def⟩ : ∃ x : ℝ, x = min (ε/(100*((K:ℝ)+1))) (lam/4) := ⟨_, rfl⟩
  have hwmin : 0 < wmin := by rw [hwmin_def]; exact lt_min (by positivity) (by positivity)
  have hwminA : wmin ≤ ε/(100*((K:ℝ)+1)) := by rw [hwmin_def]; exact min_le_left _ _
  have hwminB : wmin ≤ lam/4 := by rw [hwmin_def]; exact min_le_right _ _
  obtain ⟨ε₁, hε₁_def⟩ : ∃ x : ℝ, x = min (ε/(400*((K:ℝ)+1))) (lam/16) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁_def]; exact lt_min (by positivity) (by positivity)
  have hε₁A : ε₁ ≤ ε/(400*((K:ℝ)+1)) := by rw [hε₁_def]; exact min_le_left _ _
  have hε₁B : ε₁ ≤ lam/16 := by rw [hε₁_def]; exact min_le_right _ _
  obtain ⟨e, he_def⟩ : ∃ x : ℝ, x = min (εd/2000) (ε₁/100) := ⟨_, rfl⟩
  have he : 0 < e := by rw [he_def]; exact lt_min (by positivity) (by positivity)
  have heA : e ≤ εd/2000 := by rw [he_def]; exact min_le_left _ _
  have heB : e ≤ ε₁/100 := by rw [he_def]; exact min_le_right _ _
  obtain ⟨ηw, hηw_def⟩ : ∃ x : ℝ, x = min (εd/100) (ε₁/100) := ⟨_, rfl⟩
  have hηw : 0 < ηw := by rw [hηw_def]; exact lt_min (by positivity) (by positivity)
  have hηwA : ηw ≤ εd/100 := by rw [hηw_def]; exact min_le_left _ _
  have hηwB : ηw ≤ ε₁/100 := by rw [hηw_def]; exact min_le_right _ _
  obtain ⟨bw, hbw_def⟩ : ∃ x : ℝ, x = ε/(200*((K:ℝ)+1)) := ⟨_, rfl⟩
  have hbw : 0 < bw := by rw [hbw_def]; positivity
  obtain ⟨δs, hδs_def⟩ : ∃ x : ℝ, x = ε/400 := ⟨_, rfl⟩
  have hδs : 0 < δs := by rw [hδs_def]; positivity
  obtain ⟨A, hA_def⟩ : ∃ x : ℝ, x = ηw/400 := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hA_def]; positivity
  have he' : e < 1/1000 := by linarith
  have hbpw : 12*e*(1+2) + 8*e + 2*ηw ≤ ε₁ := by linarith
  have hbsl : 8*e*(1/2) + e ≤ ε₁ := by linarith
  have hbud : 12*e*((22:ℝ)+2)+8*e+2*ηw ≤ εd/2 := by linarith
  have hηw2 : ηw ≤ 2 := by linarith
  have hgA : 8*A < (2/25)*ηw := by rw [hA_def]; linarith
  obtain ⟨Ne, hNe_def⟩ : ∃ n : ℕ, n = ⌈(49/100:ℝ)/(2*e)⌉₊ := ⟨_, rfl⟩
  have hNe : (49/100:ℝ) ≤ Ne*(2*e) := by
    have h := Nat.le_ceil ((49/100:ℝ)/(2*e))
    rw [← hNe_def, div_le_iff₀ (by positivity)] at h
    exact h
  obtain ⟨Pmax, hPmax_def⟩ : ∃ n : ℕ, n = ⌈1/(4*e)⌉₊ := ⟨_, rfl⟩
  have hPmax : 1/(4*e) ≤ (Pmax:ℝ) := by rw [hPmax_def]; exact Nat.le_ceil _
  -- the core batches, one per twist
  choose Jf Cf hCf hclsj using fun tw : RayQuotient.Characters rayM G.twist =>
    hcls rayM G.pool (hHpool G hH) W hWs hW (dataBase data) (twistEta rayM G hH data tw)
      (α := Fin K) wmin (2/25) 2 hwmin (by norm_num) (by norm_num)
  obtain ⟨Jo, hJo_def⟩ : ∃ n : ℕ, n = (∑ tw, Jf tw) + 1 := ⟨_, rfl⟩
  have hJ : ∀ tw, Jf tw + 1 ≤ Jo := fun tw => by
    rw [hJo_def]
    have := Finset.single_le_sum (f := Jf) (fun _ _ => Nat.zero_le _) (Finset.mem_univ tw)
    omega
  obtain ⟨τ, hτ_def⟩ : ∃ x : ℝ, x = min A (ε/(100*((Jo:ℝ)+1))) := ⟨_, rfl⟩
  have hτ : 0 < τ := by rw [hτ_def]; exact lt_min hA (by positivity)
  have hτA : τ ≤ A := by rw [hτ_def]; exact min_le_left _ _
  have hτB : τ ≤ ε/(100*((Jo:ℝ)+1)) := by rw [hτ_def]; exact min_le_right _ _
  choose Kcf hKcf Ccf hCcf hevj using fun tw : RayQuotient.Characters rayM G.twist =>
    hclsj tw τ εd e ηw bw δs margin 1 2 ε₁ e ηw hτ hεd hεd1 he he' hηw.le hηw2 hbud hbw hδs
      hmargin (by norm_num) le_rfl hε₁ he hηw.le hbsl
  obtain ⟨Cr, hCr, Cs, hCs, hriev⟩ := inverse_row_inputs_at rayM G hH W hWs hW Φ ao bo hao hΦs
    hΦ data τ ε₁ ε₁ e ηw hτ hε₁ hε₁ he he' hηw.le hbpw hbsl
  obtain ⟨C0, hC0, htriv⟩ := trivial_energy Φ ao bo hΦs hΦ.continuous
  obtain ⟨Cw, hCw, hwev⟩ := whole_row_spike hβ hP Φ ao bo hao hΦs hΦ data τ ε₁ e ηw A hτ hε₁
    he he' hηw.le hA.le hbpw
  obtain ⟨Ct, hCt, htiny⟩ := Cofactor.tiny_core_count (2/25) δs (by norm_num) hδs
  obtain ⟨D, hD, hcof⟩ := high_cofactor_energyW δs hδs
  -- constants
  obtain ⟨E, hE_def⟩ : ∃ n : ℕ, n = ∑ tw : RayQuotient.Characters rayM G.twist,
      ((Record12518109GainWholeGeometry.wholeRegularDictionary rayM G.pool (hHpool G hH)
        (dataBase data) (twistEta rayM G hH data tw)).exceptional_cores_finite.toFinset).card :=
    ⟨_, rfl⟩
  obtain ⟨Kw, hKw_def⟩ : ∃ x : ℝ, x = Cw * 65536^K := ⟨_, rfl⟩
  have hKw : 0 < Kw := by rw [hKw_def]; positivity
  have hKgj : ∀ tw, 0 ≤ Cr * (4*65536*Ccf tw^2)^K * Kcf tw * (7*(8+6*((Ne:ℝ)+1)))^Jo :=
    fun tw => by have := hKcf tw; positivity
  obtain ⟨Kbin, hKbin_def⟩ : ∃ x : ℝ, x = ∑ tw : RayQuotient.Characters rayM G.twist,
      Cr * (4*65536*Ccf tw^2)^K * Kcf tw * (7*(8+6*((Ne:ℝ)+1)))^Jo := ⟨_, rfl⟩
  have hKbin : 0 ≤ Kbin := by rw [hKbin_def]; exact Finset.sum_nonneg fun tw _ => hKgj tw
  obtain ⟨Kcls, hKcls_def⟩ : ∃ x : ℝ, x = (E:ℝ) * Kw + (((Ne+1)*(Pmax+1) : ℕ) : ℝ) * Kbin :=
    ⟨_, rfl⟩
  have hKcls : 0 ≤ Kcls := by rw [hKcls_def]; positivity
  obtain ⟨degree, hdeg_def⟩ : ∃ n : ℕ, n = Jo + ⌈(1+(K:ℝ))/A⌉₊ := ⟨_, rfl⟩
  obtain ⟨lamv, hlamv_def⟩ : ∃ x : ℝ, x = 2*ε₁*2*((K:ℝ)+1) + (K:ℝ)*wmin +
      (margin + 2*(δs + 154*εd + εm + δs) + mesh + 2*bw*(K:ℝ)) + 2*ε₁ := ⟨_, rfl⟩
  obtain ⟨Cfin, hCfin_def⟩ : ∃ x : ℝ, x = C0 * 65536^K + Ct * Kw + Kcls * D := ⟨_, rfl⟩
  have hCfin : 0 < Cfin := by rw [hCfin_def]; positivity
  -- the eventual scale
  obtain ⟨Z₁, hZ₁⟩ := eventually_atTop.mp ((((((eventually_all.mpr hevj).and
    (eventually_all.mpr hriev)).and hwev).and (gate_eventually Ne A ηw hgA)).and
    ((tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop
      ((DetectorDictionaryInverseRawInitialGates.deletedBase data).modulus.absNorm : ℝ)))).and
    ((tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop
      ((Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm : ℝ))))
  refine ⟨degree, 65536 + Cs^2, Cfin, max Z₁ 2, by positivity, hCfin,
    lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro Z hZ ι _ _ hKι L ell β hv hv0 hclsZ hell0 hellm hpr hrat hβ1 _ r hr0 hr1 rows hrows θ
  obtain ⟨⟨⟨⟨⟨hZc, hZr⟩, hZw⟩, hZg⟩, hZd⟩, hZf⟩ := hZ₁ Z (le_of_max_le_left hZ)
  have hZ1 : 1 < Z := lt_of_lt_of_le (by norm_num) (le_of_max_le_right hZ)
  have hZ0 : 0 < Z := by linarith
  obtain ⟨tw, v, hvb, hLβ⟩ := hclsZ
  obtain ⟨-, hZτ2, hcbZ⟩ := hZc tw
  obtain ⟨-, -, hriZ⟩ := hZr tw
  have hZτ : 1 ≤ Z^τ := by linarith
  set S : ℝ := ∑ i, ell i with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hell0 i
  have hSK : S ≤ (K:ℝ) := by
    calc S ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum fun i _ => (hellm i).trans hmesh1
      _ = (Fintype.card ι : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ ≤ (K:ℝ) := by exact_mod_cast hKι
  have hprice0 : 0 ≤ highPriceFW a0 a1 k wlo r S 1 := by
    unfold highPriceFW; exact le_max_left _ _
  have hdegA : 1 + S ≤ A * degree := by
    have h1 := Nat.le_ceil ((1+(K:ℝ))/A)
    rw [div_le_iff₀ hA] at h1
    have h2 : (⌈(1+(K:ℝ))/A⌉₊ : ℝ) ≤ degree := by
      rw [hdeg_def]; push_cast; have := Nat.cast_nonneg (α := ℝ) Jo; linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hA.le
    rw [mul_comm A]
    linarith
  have hHd1 : 1 ≤ ((1+‖θ‖+hv)^degree)^2 := by
    have : 1 ≤ (1+‖θ‖+hv)^degree := one_le_pow₀ (by linarith [norm_nonneg θ])
    exact one_le_pow₀ this
  have hZp0 : 0 ≤ Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) := Real.rpow_nonneg hZ0.le _
  by_cases hlarge : Z^A ≤ ‖θ‖ + hv
  · -- large heights: the trivial bound
    have h1 := htriv data L ell β Z hZ1.le hell0 hpr hrat hβ1 r hr0 hr1
      (rows.filter (fun u => SlotHigh (65536 + Cs^2) lam k Z L ell β u))
      (fun u hu => hrows u (Finset.mem_filter.mp hu).1) θ
    have hcard : (65536:ℝ)^(Fintype.card ι) ≤ 65536^K := pow_le_pow_right₀ (by norm_num) hKι
    have h2 := large_height_bound (C0 := C0*65536^K) (P := highPriceFW a0 a1 k wlo r S 1) (ε := ε)
      hZ1.le hlarge hv0 hdegA hprice0 hε.le (by positivity)
    have hCC : C0 * 65536^K ≤ Cfin := by
      rw [hCfin_def]; have : 0 ≤ Ct * Kw := by positivity
      have : 0 ≤ Kcls * D := by positivity
      linarith
    calc _ ≤ C0 * (65536:ℝ)^(Fintype.card ι) * Z^(2 + S) := h1
      _ ≤ C0 * 65536^K * Z^(2 + S) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hC0.le)
            (Real.rpow_nonneg hZ0.le _)
      _ ≤ C0 * 65536^K * Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) *
          ((1+‖θ‖+hv)^degree)^2 := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hZp0) (by positivity)
  push Not at hlarge
  have hθn : ‖θ‖ = |θ| := Real.norm_eq_abs θ
  rw [hθn] at hlarge
  have hgateAll : ∀ j : ℕ, j ≤ ⌈7*|θ|+hv⌉₊ + Ne →
      (3+((3*j+2 : ℕ) : ℝ)*Z^τ)^4 ≤ Z^((2/25)*ηw) := fun j hj =>
    gate_bound hZ1.le hτ.le hτA hv0 hlarge hj hZg
  have hconv2 : Z^((2/25)*ηw) ≤ (Z^(2:ℝ))^ηw := by
    rw [← Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  -- re-indexing the slots into `Fin K`
  set em : ι ↪ Fin K := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hKι) with hem
  set T : Finset (Fin K) := Finset.univ.map em with hT
  set ell' : Fin K → ℝ := Function.extend em ell 0 with hell'_def
  set v' : Fin K → ℝ := Function.extend em v 0 with hv'_def
  have hell' : ∀ i, ell' (em i) = ell i := fun i => em.injective.extend_apply ell 0 i
  have hv' : ∀ i, v' (em i) = v i := fun i => em.injective.extend_apply v 0 i
  have hTmem : ∀ x ∈ T, ∃ i, em i = x := fun x hx => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
    exact ⟨i, rfl⟩
  have hSeq : ∑ x ∈ T, ell' x = S := by
    rw [hT, Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => hell' i
  have hell0T : ∀ x ∈ T, 0 ≤ ell' x := fun x hx => by
    obtain ⟨i, rfl⟩ := hTmem x hx; rw [hell']; exact hell0 i
  have hellmT : ∀ x ∈ T, ell' x ≤ mesh := fun x hx => by
    obtain ⟨i, rfl⟩ := hTmem x hx; rw [hell']; exact hellm i
  have hvbT : ∀ x ∈ T, |v' x| ≤ hv := fun x hx => by
    obtain ⟨i, rfl⟩ := hTmem x hx; rw [hv']; exact hvb i
  have hβT : ∀ x ∈ T, ∀ P ∈ canonicalPool rayM G.pool (Z^(ell' x)),
      ‖rayCoeff rayM G hH W (33/50) data tw (Z^(ell' x)) (v' x) P‖ ≤ 1 := fun x hx => by
    obtain ⟨i, rfl⟩ := hTmem x hx
    rw [hell', hv']
    intro P hP
    have h := hβ1 i P (by rw [(hLβ i).1]; exact hP)
    rwa [(hLβ i).2] at h
  have hslotT : ∀ (w : O) (i : ι), invNs rayM G hH W data tw Z ell' v' w (em i) =
      ‖directSlot w (L i) (β i) (Z^(ell i))‖^2 := fun w i => by
    unfold invNs
    rw [hell', hv', (hLβ i).1, (hLβ i).2]
  -- rows as nonzero frequencies
  set toNF : NonzeroElement ↪ ProbePhysical.NonzeroFrequency :=
    ⟨fun u => ⟨u.val, u.property⟩, fun u u' h => Subtype.ext (congrArg Subtype.val h)⟩ with htoNF
  set R : Finset ProbePhysical.NonzeroFrequency :=
    (rows.filter (fun u => SlotHigh (65536 + Cs^2) lam k Z L ell β u)).map toNF with hR_def
  set f : ProbePhysical.NonzeroFrequency → ℝ := fun h =>
    ‖polynomial (data.character ⟨h.val, h.property⟩) true (InverseMoment.childLogTest Φ θ)
      (Z^r) 0 0 * (∏ i, directSlot h.val (L i) (β i) (Z^(ell i)))‖^2 with hf_def
  have hsumR : inverseMarkedSum data Φ L ell β
      (rows.filter (fun u => SlotHigh (65536 + Cs^2) lam k Z L ell β u)) Z r θ =
      ∑ h ∈ R, f h := by
    unfold inverseMarkedSum
    rw [hR_def, Finset.sum_map]
    try rfl
  have hRmem : ∀ h ∈ R, (⟨h.val, h.property⟩ : NonzeroElement) ∈
      rows.filter (fun u => SlotHigh (65536 + Cs^2) lam k Z L ell β u) := by
    intro h hh
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hh
    exact hu
  have hRn : ∀ h ∈ R, ((Ideal.span {h.val}).absNorm : ℝ) ≤ Z := by
    intro h hh
    have := hrows _ (Finset.mem_filter.mp (hRmem h hh)).1
    rwa [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at this
  have hRprod : ∀ h : ProbePhysical.NonzeroFrequency, f h =
      ‖polynomial (data.character ⟨h.val, h.property⟩) true (InverseMoment.childLogTest Φ θ)
        (Z^r) 0 0‖^2 * ∏ x ∈ T, invNs rayM G hH W data tw Z ell' v' h.val x := by
    intro h
    simp only [hf_def]
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow, hT, Finset.prod_map]
    congr 1
    exact Finset.prod_congr rfl fun i _ => (hslotT h.val i).symm
  have hRhigh : ∀ h ∈ R, ∃ x ∈ T, (65536 + Cs^2) * Z^(k * ell' x + lam) <
      invNs rayM G hH W data tw Z ell' v' h.val x := by
    intro h hh
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp (hRmem h hh)).2
    refine ⟨em i, Finset.mem_map_of_mem _ (Finset.mem_univ i), ?_⟩
    rw [hslotT, hell']
    exact hi
  -- the whole-row bound
  have hi0 : 7*|θ| + hv ≤ ((⌈7*|θ|+hv⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hθ7 : |2*Real.pi*θ| ≤ 7*|θ| + hv := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
    have hpi : 2*Real.pi ≤ 7 := by linarith [Real.pi_lt_d2]
    have := mul_le_mul_of_nonneg_right hpi (abs_nonneg θ)
    linarith
  have hθA : |θ| < Z^A := by linarith
  have hRw : ∀ h ∈ R, f h ≤ Kw * Z^(3/4*r + S + 2*ε₁) := by
    intro h hh
    have hM := hZw ⟨h.val, h.property⟩ (hRn h hh) r θ ⌈7*|θ|+hv⌉₊ hr0 hr1 hθA
      (window_ok hZτ (hθ7.trans hi0))
      ((hgateAll _ (Nat.le_add_right _ _)).trans hconv2)
    have hsl : ∀ i, ‖directSlot h.val (L i) (β i) (Z^(ell i))‖^2 ≤ 65536 * Z^(ell i) := by
      intro i
      have hD : 1 ≤ Z^(ell i) := Real.one_le_rpow hZ1.le (hell0 i)
      refine trivial_slot h.val (L i) (β i) (Z^(ell i)) hD (fun P hP => ⟨(hpr i P hP).ne_zero, ?_⟩)
        (hβ1 i)
      have h2 := (hrat i P hP).2
      have hD0 : 0 < Z^(ell i) := zero_lt_one.trans_le hD
      have := (div_le_iff₀ hD0).mp h2
      linarith
    have hprod : ∏ i, ‖directSlot h.val (L i) (β i) (Z^(ell i))‖^2 ≤ 65536^K * Z^S := by
      calc ∏ i, ‖directSlot h.val (L i) (β i) (Z^(ell i))‖^2 ≤ ∏ i, (65536 * Z^(ell i)) :=
            Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) (fun i _ => hsl i)
        _ = (65536 : ℝ)^(Fintype.card ι) * Z^(∑ i, ell i) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
              Real.rpow_sum_of_pos hZ0]
        _ ≤ 65536^K * Z^S :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hKι)
              (Real.rpow_nonneg hZ0.le _)
    have hfe : f h = ‖polynomial (data.character ⟨h.val, h.property⟩) true
        (InverseMoment.childLogTest Φ θ) (Z^r) 0 0‖^2 *
          ∏ i, ‖directSlot h.val (L i) (β i) (Z^(ell i))‖^2 := by
      simp only [hf_def]
      rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
    rw [hfe, hKw_def]
    calc _ ≤ (Cw * Z^(3/4*r + 2*ε₁)) * (65536^K * Z^S) :=
          mul_le_mul hM hprod (Finset.prod_nonneg fun i _ => sq_nonneg _) (by positivity)
      _ = Cw * 65536^K * (Z^(3/4*r + 2*ε₁) * Z^S) := by ring
      _ = Cw * 65536^K * Z^(3/4*r + S + 2*ε₁) := by
          rw [← Real.rpow_add hZ0]; congr 2; ring
  -- tiny and large classes
  have hnormR : ∀ h ∈ R, LocalMoment.rawFrequencyNorm h ≤ Z^(1:ℝ) := by
    intro h hh
    rw [Real.rpow_one]
    exact hRn h hh
  have hpair : ∀ (u : FreeRow) (B : NZIdeal), sfe (u, B) ∈ R →
      ProbeHighRowFamily.rowNorm u ≤ Z^(Cofactor.coreWidth Z 1 B) ∧
        (B.val.absNorm : ℝ) ≤ Z^(1:ℝ) := by
    intro u B hR
    have hn := hnormR _ hR
    rw [LocalMoment.raw_sixth_norm] at hn
    refine ⟨rowNorm_le_coreWidth hZ1 u B hn, ?_⟩
    have h1 := ProbeHighRowFamily.rowNorm_ge_one u
    have hB1 : (1:ℝ) ≤ (B.val.absNorm : ℝ) := by
      have hp : 0 < B.val.absNorm :=
        Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
      exact_mod_cast hp
    have hB6 : (B.val.absNorm : ℝ) ≤ (B.val.absNorm : ℝ)^6 := le_self_pow₀ hB1 (by norm_num)
    have hn' : ProbeHighRowFamily.rowNorm u * (B.val.absNorm : ℝ)^6 ≤ Z^(1:ℝ) := hn
    have h6 : (B.val.absNorm : ℝ)^6 ≤ ProbeHighRowFamily.rowNorm u * (B.val.absNorm : ℝ)^6 :=
      le_mul_of_one_le_left (by positivity) h1
    linarith
  have hsplit : ∑ h ∈ R, f h =
      ∑ h ∈ R.filter (fun h => Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25), f h +
      ∑ h ∈ R, (if Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25 then 0 else f h) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_filter_add_sum_filter_not]
  -- the tiny classes
  have htinyS : ∑ h ∈ R.filter (fun h => Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25), f h ≤
      (Ct * Kw) * Z^(1/6 + δs + (5*(2/25)/6 + δs) + (3/4*r + S + 2*ε₁)) := by
    have hcard := htiny Z hZ1.le Z hZ1.le
      ((R.filter (fun h => Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25)).map
        ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro z hz
      obtain ⟨hh, hhm, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨hhR, hht⟩ := Finset.mem_filter.mp hhm
      refine ⟨hh.property, hRn hh hhR, ?_⟩
      have e1 : sfe (ProbePhysical.sixthFrequencyEquiv.symm hh) = hh := Equiv.apply_symm_apply _ hh
      have hR' : sfe ((ProbePhysical.sixthFrequencyEquiv.symm hh).1, (ProbePhysical.sixthFrequencyEquiv.symm hh).2) ∈ R := by
        rw [Prod.mk.eta, e1]; exact hhR
      obtain ⟨hcw, -⟩ := hpair _ _ hR'
      refine ⟨ConcretePrimeRowBridge.idealGenerator (ProbePhysical.sixthFrequencyEquiv.symm hh).2.val,
        (ProbePhysical.sixthFrequencyEquiv.symm hh).1.val, ?_, ?_⟩
      · show hh.val = _
        have e2 := congrArg Subtype.val e1
        rw [← e2, ProbePhysical.sixthFrequencyEquiv_apply]
        ring
      · exact hcw.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le hht))
    rw [Finset.card_map] at hcard
    have hnn : 0 ≤ Kw * Z^(3/4*r + S + 2*ε₁) := by positivity
    have e : Z^(1/6 + δs) * Z^(5*(2/25)/6 + δs) * Z^(3/4*r + S + 2*ε₁) =
        Z^(1/6 + δs + (5*(2/25)/6 + δs) + (3/4*r + S + 2*ε₁)) := by
      rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
    calc ∑ h ∈ R.filter (fun h => Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25), f h
        ≤ ∑ _h ∈ R.filter (fun h => Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25),
            Kw * Z^(3/4*r + S + 2*ε₁) :=
          Finset.sum_le_sum fun h hh => hRw h (Finset.mem_filter.mp hh).1
      _ = ((R.filter (fun h => Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25)).card : ℝ) *
          (Kw * Z^(3/4*r + S + 2*ε₁)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Ct * Z^(1/6 + δs) * Z^(5*(2/25)/6 + δs)) * (Kw * Z^(3/4*r + S + 2*ε₁)) :=
          mul_le_mul_of_nonneg_right hcard hnn
      _ = (Ct * Kw) * (Z^(1/6 + δs) * Z^(5*(2/25)/6 + δs) * Z^(3/4*r + S + 2*ε₁)) := by ring
      _ = _ := by rw [e]
  -- the large classes
  set Y : ℝ := (1+‖θ‖+hv)*Z^τ with hY_def
  have hY1 : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (by linarith [norm_nonneg θ]) hZτ
  have hYJ0 : 0 ≤ Y^Jo := pow_nonneg (by linarith) _
  have hε₁K : 2*ε₁*2*((K:ℝ)+1) ≤ ε/100 := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ) < 400*((K:ℝ)+1))).mp hε₁A
    have h' := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 100)
    have e : 2*ε₁*2*((K:ℝ)+1) = ε₁*(400*((K:ℝ)+1))/100 := by ring
    rw [e]; exact h'
  have hwK : (K:ℝ)*wmin ≤ ε/100 := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ) < 100*((K:ℝ)+1))).mp hwminA
    have h' := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 100)
    have e : wmin*(100*((K:ℝ)+1))/100 = (K:ℝ)*wmin + wmin := by ring
    rw [e] at h'
    linarith
  have hbwK : 2*bw*(K:ℝ) ≤ ε/100 := by
    have h : 2*bw*((K:ℝ)+1) = ε/100 := by rw [hbw_def]; field_simp; ring
    have e : 2*bw*(K:ℝ) = 2*bw*((K:ℝ)+1) - 2*bw := by ring
    rw [e, h]; linarith
  have hε₁e : ε₁ ≤ ε/400 := by
    have : ε/(400*((K:ℝ)+1)) ≤ ε/400 :=
      div_le_div_of_nonneg_left hε.le (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) K; linarith)
    linarith
  have hτJ : τ*(Jo:ℝ) ≤ ε/100 := by
    have h := (le_div_iff₀ (by positivity : (0:ℝ) < 100*((Jo:ℝ)+1))).mp hτB
    have h' := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 100)
    have e : τ*(100*((Jo:ℝ)+1))/100 = τ*(Jo:ℝ) + τ := by ring
    rw [e] at h'
    linarith
  have hlamv1 : 2*ε₁*2*((K:ℝ)+1) + (K:ℝ)*wmin +
      (margin + 2*(δs + 154*εd + εm + δs) + mesh + 2*bw*(K:ℝ)) ≤ lamv := by
    rw [hlamv_def]; linarith
  have hlamv2 : 2*ε₁ ≤ lamv := by
    rw [hlamv_def]
    have : 0 ≤ (K:ℝ)*wmin := by positivity
    have : 0 ≤ 2*bw*(K:ℝ) := by positivity
    have : 0 ≤ 2*ε₁*2*((K:ℝ)+1) := by positivity
    linarith
  have hmemR : ∀ (B : NZIdeal), ∀ u ∈ LocalMoment.sixthFreeFiber R B, sfe (u, B) ∈ R := by
    intro B u hu
    obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
    obtain ⟨hp, hpB⟩ := Finset.mem_filter.mp hp
    have hpe : p = (u, B) := Prod.ext hpu hpB
    rw [← hpe]
    exact (LocalMoment.mem_sixthPairs R p).mp hp
  have hlarge_cls := hcof a0 a1 k wlo (by linarith) hk1 R
    (fun h => if Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25 then 0 else f h) Z 1 r S
    (Kcls * Y^Jo) lamv hZ1 zero_le_one hS0 (mul_nonneg hKcls hYJ0) hnormR (by
      intro B hne
      obtain ⟨u₀, hu₀⟩ := hne
      have hmemB := hmemR B
      have hfval : ∀ u ∈ LocalMoment.sixthFreeFiber R B,
          (fun h => if Cofactor.coreWidth Z 1 (ProbePhysical.sixthFrequencyEquiv.symm h).2 ≤ 2/25 then 0 else f h)
            (sfe (u, B)) =
          if Cofactor.coreWidth Z 1 B ≤ 2/25 then 0 else f (sfe (u, B)) := by
        intro u _
        simp only [Equiv.symm_apply_apply]
      refine ⟨fun hbig => ?_, fun hsmall => ?_⟩
      · rw [Finset.sum_congr rfl hfval]
        simp only [if_neg (not_le.mpr hbig)]
        have hEc : ((((LocalMoment.sixthFreeFiber R B).filter (fun c => ¬ RegularCore rayM
            G.pool (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw) c)).card : ℕ) : ℝ)
            ≤ E := by
          have hsub : (LocalMoment.sixthFreeFiber R B).filter (fun c => ¬ RegularCore rayM
              G.pool (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw) c) ⊆
              (Record12518109GainWholeGeometry.wholeRegularDictionary rayM G.pool (hHpool G hH)
                (dataBase data) (twistEta rayM G hH data tw)).exceptional_cores_finite.toFinset := by
            intro u hu
            have hnr := (Finset.mem_filter.mp hu).2
            unfold RegularCore at hnr
            rw [not_not] at hnr
            exact (Set.Finite.mem_toFinset _).mpr hnr
          have h1 := Finset.card_le_card hsub
          have h2 : ((Record12518109GainWholeGeometry.wholeRegularDictionary rayM G.pool
              (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw)).exceptional_cores_finite.toFinset).card
              ≤ E := by
            rw [hE_def]
            exact Finset.single_le_sum (f := fun tw => ((Record12518109GainWholeGeometry.wholeRegularDictionary
              rayM G.pool (hHpool G hH) (dataBase data) (twistEta rayM G hH data tw)).exceptional_cores_finite.toFinset).card)
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ tw)
          exact_mod_cast h1.trans h2
        have hcb := class_bound hβ rayM G hH W hWs Φ data tw hk0 hk1 hlo ha1 ha1' (hcbZ)
          hriZ hZ1 hZτ hτ he he' hNe hPmax (lam' := lam/2) (by linarith) (by linarith) (by linarith) hwmin hε₁
          hηw.le hδs hεd.le hεm.le hbw.le hmargin hmargin2 hmesh.le hmesh1 hmeshA hmeshm (hJ tw)
          hCr (hCcf tw) (hKcf tw) hZd hZf hv0 hr0 hr1 hgateAll T ell' v' hell0T hellmT hvbT hβT
          B hbig (Cofactor.coreWidth_le Z 1 hZ1 B)
          (hpair u₀ B (hmemB u₀ hu₀)).2
          (LocalMoment.sixthFreeFiber R B) (fun c => f (sfe (c, B))) E Kw (2*ε₁) lamv hKw.le
          (fun c hc => ⟨hRn _ (hmemB c hc), (hpair c B (hmemB c hc)).1⟩)
          (fun c hc => (hRprod _).le)
          (fun c hc => hRhigh _ (hmemB c hc))
          (fun c hc => by rw [hSeq]; exact hRw _ (hmemB c hc))
          hEc hlamv1 hlamv2
        rw [hSeq] at hcb
        refine hcb.trans ?_
        have hKt : (E:ℝ) * Kw + (((Ne+1)*(Pmax+1) : ℕ) : ℝ) *
            (Cr * (4*65536*Ccf tw^2)^K * Kcf tw * (7*(8+6*((Ne:ℝ)+1)))^Jo) ≤ Kcls := by
          rw [hKcls_def]
          have h1 : Cr * (4*65536*Ccf tw^2)^K * Kcf tw * (7*(8+6*((Ne:ℝ)+1)))^Jo ≤ Kbin := by
            rw [hKbin_def]
            exact Finset.single_le_sum (f := fun tw => Cr * (4*65536*Ccf tw^2)^K * Kcf tw *
              (7*(8+6*((Ne:ℝ)+1)))^Jo) (fun tw _ => hKgj tw) (Finset.mem_univ tw)
          have := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) ((Ne+1)*(Pmax+1)))
          linarith
        have hz0 : 0 ≤ Z^(Cofactor.coreWidth Z 1 B + highPriceFW a0 a1 k wlo r S
            (Cofactor.coreWidth Z 1 B) + lamv) := Real.rpow_nonneg hZ0.le _
        calc _ ≤ Kcls * Y^Jo * Z^(Cofactor.coreWidth Z 1 B + highPriceFW a0 a1 k wlo r S
              (Cofactor.coreWidth Z 1 B) + lamv) := by
              rw [hY_def]
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKt hYJ0) hz0
          _ = _ := by ring
      · rw [Finset.sum_congr rfl hfval]
        simp only [if_pos hsmall, Finset.sum_const_zero]
        positivity)
  -- the budget
  have htinyM := tinyEx_le_highPriceFW a0 a1 k wlo r S 1
  unfold tinyEx at htinyM
  have hE1 : 1/6 + δs + (5*(2/25)/6 + δs) + (3/4*r + S + 2*ε₁) ≤
      1 + highPriceFW a0 a1 k wlo r S 1 + ε := by
    have hδsv : δs = ε/400 := hδs_def
    linarith
  have hE2 : τ*(Jo:ℝ) + (1 + highPriceFW a0 a1 k wlo r S 1 + lamv + δs*1) ≤
      1 + highPriceFW a0 a1 k wlo r S 1 + ε := by
    have hδsv : δs = ε/400 := hδs_def
    have hεmv : εm = ε/1000 := hεm_def
    rw [hlamv_def]
    linarith
  have hHJ : (1+‖θ‖+hv)^Jo ≤ ((1+‖θ‖+hv)^degree)^2 := by
    have hx1 : 1 ≤ 1+‖θ‖+hv := by linarith [norm_nonneg θ]
    have h1 : (1+‖θ‖+hv)^Jo ≤ (1+‖θ‖+hv)^degree :=
      pow_le_pow_right₀ hx1 (by rw [hdeg_def]; omega)
    have h2 : 1 ≤ (1+‖θ‖+hv)^degree := one_le_pow₀ hx1
    exact h1.trans (le_self_pow₀ h2 (by norm_num))
  have hA1 : (Ct * Kw) * Z^(1/6 + δs + (5*(2/25)/6 + δs) + (3/4*r + S + 2*ε₁)) ≤
      (Ct * Kw) * (Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) * ((1+‖θ‖+hv)^degree)^2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc Z^(1/6 + δs + (5*(2/25)/6 + δs) + (3/4*r + S + 2*ε₁)) ≤
        Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) := Real.rpow_le_rpow_of_exponent_le hZ1.le hE1
      _ = Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hHd1 hZp0
  have hZτJ : (Z^τ)^Jo = Z^(τ*(Jo:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
  have hA2 : Kcls * Y^Jo * D * Z^(1 + highPriceFW a0 a1 k wlo r S 1 + lamv + δs*1) ≤
      (Kcls * D) * (Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) * ((1+‖θ‖+hv)^degree)^2) := by
    rw [hY_def, mul_pow, hZτJ]
    have hz : Z^(τ*(Jo:ℝ)) * Z^(1 + highPriceFW a0 a1 k wlo r S 1 + lamv + δs*1) ≤
        Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) := by
      rw [← Real.rpow_add hZ0]
      exact Real.rpow_le_rpow_of_exponent_le hZ1.le hE2
    have hH0 : 0 ≤ (1+‖θ‖+hv)^Jo := pow_nonneg (by linarith [norm_nonneg θ]) _
    calc Kcls * ((1+‖θ‖+hv)^Jo * Z^(τ*(Jo:ℝ))) * D *
          Z^(1 + highPriceFW a0 a1 k wlo r S 1 + lamv + δs*1)
        = (Kcls * D) * ((1+‖θ‖+hv)^Jo * (Z^(τ*(Jo:ℝ)) *
          Z^(1 + highPriceFW a0 a1 k wlo r S 1 + lamv + δs*1))) := by ring
      _ ≤ (Kcls * D) * (((1+‖θ‖+hv)^degree)^2 * Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hHJ hz (by positivity) (by positivity)
      _ = _ := by ring
  have hCC : Ct * Kw + Kcls * D ≤ Cfin := by
    rw [hCfin_def]; have : 0 ≤ C0 * 65536^K := by positivity
    linarith
  rw [hsumR, hsplit]
  calc _ ≤ (Ct * Kw) * Z^(1/6 + δs + (5*(2/25)/6 + δs) + (3/4*r + S + 2*ε₁)) +
        Kcls * Y^Jo * D * Z^(1 + highPriceFW a0 a1 k wlo r S 1 + lamv + δs*1) :=
        add_le_add htinyS hlarge_cls
    _ ≤ (Ct * Kw) * (Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) * ((1+‖θ‖+hv)^degree)^2) +
        (Kcls * D) * (Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) * ((1+‖θ‖+hv)^degree)^2) :=
        add_le_add hA1 hA2
    _ = (Ct * Kw + Kcls * D) * Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) *
        ((1+‖θ‖+hv)^degree)^2 := by ring
    _ ≤ Cfin * Z^(1 + highPriceFW a0 a1 k wlo r S 1 + ε) * ((1+‖θ‖+hv)^degree)^2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hZp0) (by positivity)

/-- **The inverse HIGH leaf** from the principal inverse spike `Principal.PrincipalInverseSpike`. -/
theorem inverseHighLeaf_of_principal (hP : Principal.PrincipalInverseSpike) :
    InverseHighLeaf :=
  inverseHighLeaf_of_spike hP

/-- **The inverse HIGH leaf.** -/
theorem inverseHighLeaf : InverseHighLeaf :=
  inverseHighLeaf_of_principal Principal.principalInverseSpike

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse

#print axioms Qrh.TwoSlot.AnchorZeroLoss.High.Inverse.inverseHighLeaf
