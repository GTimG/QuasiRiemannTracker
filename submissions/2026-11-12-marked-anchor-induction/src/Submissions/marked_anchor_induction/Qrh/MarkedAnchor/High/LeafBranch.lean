/- Copyright (c) 2026 Sil. Apache-2.0.
The bin bookkeeping follows sil-density-split `Density/LeafHighEnergy.lean` (`high_branch`,
Apache-2.0); the sixth-power cofactor sum and the exceptional cores are Hailey Collet's
(`Record12518109Gain`, `Cycle61/Density/NaturalDictionary.lean`, Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafClass
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafPointwise
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafBudget
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.BranchAux
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.CoreGuards
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.CofactorW
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Cofactor.Tiny

/-!
# High.LeafBranch

**The ordinary HIGH leaf**:

`high_branch_mesh : HighMarkedCoreInputsH a0 a1 wlo → HighBranchMesh (highPriceW a0 a1 k wlo _ _) k`

for `1/6 ≤ k ≤ 3/4`, `wlo ≤ cutHi`, `0 ≤ a1 ≤ 1/2` (and `β ≥ 51/100`).

The energy is reduced to a finite support `G` of HIGH rows (`energy_le_support`); every row
`z = u·B⁶` is classified by its sixth-power cofactor `B`:
* tiny classes (`coreWidth ≤ 2/25`): the tiny-core count (`Cofactor.tiny_core_count`) times
  the whole-row bound (all slots paid pointwise, `ν ≤ 3/4`);
* large classes: exceptional cores (finitely many, `exceptional_cores_finite`) pointwise; the
  regular cores split by their `selectBin` bin, each bin a core batch
  (`High.LeafClass.core_class_batch`) at the core scale `coreWidth + margin`;
* the classes are summed by `High.CofactorW.high_cofactor_energyW`.
The parameters: `εm = loss·Mmin/(100(Mmin+1))`, `meshH = meshm·(2/25)/2`,
`wmin = loss·Mmin/(100(N+1))`, `dmin = 2/25`, `dmax = Mcap+1`, `ε_det = 592 e + 4 d v/min Mmin (2/25)`,
`ηw = d v/(2/25)`, `bw = loss·Mmin/(200(N+1))`, `margin = min (loss·Mmin/100) (1/2)` and
`δ = loss·Mmin/(100(Mcap+2))` for the dyadic, cutoff, cofactor and tiny losses.
-/

set_option autoImplicit false
set_option maxHeartbeats 40000000

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open LocalMoment HeckeDyadic HeckeDetectorWitnessRows CenteredMomentWholeSlotDeletion
open HeckeDetectorSupportedWitness HeckeDetectorRowwisePolynomial HeckeInverseAmplification
open CenteredMomentNaturalRowSource ProbePhysical ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal
local instance leafBranchQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

theorem le_rpow_of_pow_six_le {x Z a : ℝ} (hx : 0 ≤ x) (hZ : 0 < Z) (h : x^6 ≤ Z^a) :
    x ≤ Z^(a/6) := by
  by_contra hlt
  push Not at hlt
  have h6 : (Z^(a/6))^6 < x^6 :=
    pow_lt_pow_left₀ hlt (Real.rpow_nonneg hZ.le _) (by norm_num)
  have e : (Z^(a/6))^6 = Z^a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]; norm_num
  linarith

theorem sfe_mem_of_fiber {R : Finset NonzeroFrequency} {B : NZIdeal} {u : FreeRow}
    (hu : u ∈ LocalMoment.sixthFreeFiber R B) : sixthFrequencyEquiv (u, B) ∈ R := by
  obtain ⟨p, hp, hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨hp, hpB⟩ := Finset.mem_filter.mp hp
  have hpe : p = (u, B) := Prod.ext hpu hpB
  rw [← hpe]
  exact (LocalMoment.mem_sixthPairs R p).mp hp

theorem sum_extSlot {α : Type*} (T : Finset α) (w : T → ℝ) :
    ∑ x ∈ T, extSlot w 0 x = ∑ k : T, w k := by
  rw [← Finset.sum_coe_sort T]
  exact Finset.sum_congr rfl fun k _ => extSlot_coe w 0 k

/-- The whole-row bound (all slots paid pointwise). -/
theorem whole_bound_alg {r Kr ctl2 Z ν Pl ε₁ d Cs S : ℝ} {n N : ℕ} (hZ : 1 < Z) (hKr : 0 ≤ Kr)
    (hctl : 0 ≤ ctl2) (hCs : 1 ≤ Cs) (hε : 0 ≤ ε₁*d) (hν0 : 0 ≤ ν) (hν : ν ≤ 3/4) (hPl : 0 ≤ Pl)
    (hS : 0 ≤ S) (hn : n ≤ N)
    (h : r ≤ Kr * ctl2 * Z^(ν*Pl + 2*ε₁*d) * ((Cs * Z^(2*ε₁*d))^n * Z^(ν*S))) :
    r ≤ (Kr * Cs^N) * ctl2 * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have e1 : (Cs * Z^(2*ε₁*d))^n = Cs^n * Z^(2*ε₁*d*n) := by
    rw [mul_pow, ← Real.rpow_natCast (Z^(2*ε₁*d)) n, ← Real.rpow_mul hZ0.le]
  rw [e1] at h
  have hc : Cs^n ≤ Cs^N := pow_le_pow_right₀ hCs hn
  have hz : Z^(ν*Pl + 2*ε₁*d) * Z^(2*ε₁*d*n) * Z^(ν*S) ≤
      Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) := by
    rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    have hnN : (n:ℝ) ≤ N := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hν) hPl, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - ν) hS,
      mul_nonneg hε (sub_nonneg.mpr hnN)]
  have hCs0 : 0 ≤ Cs := zero_le_one.trans hCs
  calc r ≤ Kr * ctl2 * Z^(ν*Pl + 2*ε₁*d) * (Cs^n * Z^(2*ε₁*d*n) * Z^(ν*S)) := h
    _ = (Kr * ctl2) * Cs^n * (Z^(ν*Pl + 2*ε₁*d) * Z^(2*ε₁*d*n) * Z^(ν*S)) := by ring
    _ ≤ (Kr * ctl2) * Cs^N * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) hz (by positivity)
          (by positivity)
    _ = _ := by ring

/-- **The ordinary HIGH leaf.** -/
theorem high_branch_mesh (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) {a0 a1 k wlo : ℝ}
    (hk0 : 1/6 ≤ k) (hk1 : k ≤ 3/4) (hlo : wlo ≤ cutHi) (ha1 : 0 ≤ a1) (ha1' : a1 ≤ 1/2)
    (hM : HighMarkedCoreInputsH a0 a1 wlo) :
    HighBranchMesh (highPriceW a0 a1 k wlo (by linarith) hk1) k := by
  intro loss Mmin hloss hloss1 hMmin
  have hδu : 0 < loss * Mmin := mul_pos hloss hMmin
  obtain ⟨εm, hεm_def⟩ : ∃ x : ℝ, x = loss * Mmin / (100 * (Mmin + 1)) := ⟨_, rfl⟩
  have hεm : 0 < εm := by rw [hεm_def]; positivity
  obtain ⟨meshm, hmeshm, hcls⟩ := core_class_batch hβ hM εm hεm
  refine ⟨meshm * (2/25) / 2, by positivity, ?_⟩
  intro rayM _ H hH α _ _ W hWs hW bΦ hbΦ κ _ anchors η₀ hβlo hβhi Mcap Lplain ε₁ e kap v d mesh
    hL hε₁ he he' hkap hkap' hv hd hdsupply hslot hplain hmesh0 hmeshH hdet hdet2
  by_cases hMM : Mmin ≤ Mcap
  swap
  · refine ⟨0, fun τ hτ => ⟨1, one_pos, ∅, ?_⟩⟩
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2)] with Z hZ1 hZτ
    refine ⟨hZ1, hZτ, ?_⟩
    intro j w₀ st hchar hpunct hwidth hMst
    exfalso
    have h1 := st.character_nonneg
    have h2 : st.width = st.rowWidth + st.characterWidth := rfl
    exact hMM (by linarith)
  -- constants fixed by the data
  have hMcap0 : 0 < Mcap := hMmin.trans_le hMM
  obtain ⟨δu, hδu_def⟩ : ∃ x : ℝ, x = loss * Mmin := ⟨_, rfl⟩
  have hδu0 : 0 < δu := by rw [hδu_def]; exact hδu
  have hδuM : δu ≤ loss * Mcap := by rw [hδu_def]; exact mul_le_mul_of_nonneg_left hMM hloss.le
  set N : ℕ := Fintype.card α with hN_def
  obtain ⟨wmin, hwmin_def⟩ : ∃ x : ℝ, x = δu / (100 * ((N:ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨bw, hbw_def⟩ : ∃ x : ℝ, x = δu / (200 * ((N:ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨δs, hδs_def⟩ : ∃ x : ℝ, x = δu / (100 * (Mcap + 2)) := ⟨_, rfl⟩
  obtain ⟨margin, hmargin_def⟩ : ∃ x : ℝ, x = min (δu / 100) (1/2) := ⟨_, rfl⟩
  obtain ⟨dmax, hdmax_def⟩ : ∃ x : ℝ, x = Mcap + 1 := ⟨_, rfl⟩
  obtain ⟨εd, hεd_def⟩ : ∃ x : ℝ, x = 592*e + 4*d*v/min Mmin (2/25) := ⟨_, rfl⟩
  obtain ⟨ηw, hηw_def⟩ : ∃ x : ℝ, x = d*v/(2/25) := ⟨_, rfl⟩
  obtain ⟨Broot, hBroot_def⟩ : ∃ x : ℝ, x = (Mcap + 1)/6 := ⟨_, rfl⟩
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hwmin : 0 < wmin := by rw [hwmin_def]; positivity
  have hbw : 0 < bw := by rw [hbw_def]; positivity
  have hδs : 0 < δs := by rw [hδs_def]; positivity
  have hmargin : 0 < margin := by rw [hmargin_def]; exact lt_min (by positivity) (by norm_num)
  have hmargin1 : margin ≤ δu / 100 := by rw [hmargin_def]; exact min_le_left _ _
  have hmargin2 : margin ≤ 1/2 := by rw [hmargin_def]; exact min_le_right _ _
  have hdd : (2/25 : ℝ) ≤ dmax := by rw [hdmax_def]; linarith
  have hdmaxd : dmax ≤ d := by rw [hdmax_def]; linarith
  have hdmax0 : 0 < dmax := by rw [hdmax_def]; linarith
  have hmin0 : 0 < min Mmin (2/25) := lt_min hMmin (by norm_num)
  have hdv : 0 ≤ d * v := mul_nonneg hd.le hv
  have hηwle : ηw ≤ d*v / min Mmin (2/25) := by
    rw [hηw_def]; exact div_le_div_of_nonneg_left hdv hmin0 (min_le_right _ _)
  have hdvm : 0 ≤ d*v / min Mmin (2/25) := div_nonneg hdv hmin0.le
  have hεd_eq : εd = 592*e + 4*(d*v / min Mmin (2/25)) := by rw [hεd_def]; ring
  have hεd : 0 < εd := by rw [hεd_eq]; positivity
  have hεd1 : εd ≤ 1/1000000 := by rw [hεd_def]; exact hdet
  have hεd2 : 200*εd*(Mcap+1) ≤ δu := by rw [hεd_def, hδu_def]; exact hdet2
  have hηw0 : 0 ≤ ηw := by rw [hηw_def]; positivity
  have hηw2 : ηw ≤ 2 := by
    have : 4*(d*v / min Mmin (2/25)) ≤ 1/1000000 := by rw [hεd_eq] at hεd1; linarith
    linarith
  have hbud : 12*e*((22:ℝ)+2)+8*e+2*ηw ≤ εd/2 := by rw [hεd_eq]; linarith
  have hBroot : 0 ≤ Broot := by rw [hBroot_def]; positivity
  -- the core batches, one per anchor
  choose Jf Cf hCf hclsj using fun j : κ =>
    hcls rayM H hH W hWs hW (anchors j) η₀ (α := α) wmin (2/25) dmax hwmin (by norm_num) hdd
  refine ⟨(∑ j, Jf j) + 1, ?_⟩
  intro τ hτ
  choose Kcf hKcf Ccf hCcf hevj using fun j : κ =>
    hclsj j τ εd e ηw bw δs margin Broot d ε₁ kap v hτ hεd hεd1 he he' hηw0 hηw2 hbud hbw hδs
      hmargin hBroot hdmaxd hε₁ hkap hv hslot
  obtain ⟨Kr, hKr, Cs, hCs, S₀, hpw⟩ := high_row_pointwise rayM H hH (α := α) W hWs hW bΦ Mcap
    Lplain τ ε₁ e kap v d (by linarith) hL hτ hε₁ he he' hkap hkap' hv hd hdsupply hslot hplain
  obtain ⟨Ct, hCt, htiny⟩ := Cofactor.tiny_core_count (2/25) δs (by norm_num) hδs
  obtain ⟨D, hD, hcof⟩ := high_cofactor_energyW δs hδs
  -- the constant
  obtain ⟨Ch, hCh_def⟩ : ∃ x : ℝ, x = 2 * (8 + 6 * ((bufferCount e : ℝ) + 1)) := ⟨_, rfl⟩
  have hCh0 : 0 ≤ Ch := by rw [hCh_def]; positivity
  set Jo : ℕ := (∑ j, Jf j) + 1 with hJo_def
  have hCs0 : 0 < Cs := zero_lt_one.trans_le hCs
  obtain ⟨Kw, hKw_def⟩ : ∃ x : ℝ, x = Kr * Cs^N := ⟨_, rfl⟩
  have hKw : 0 < Kw := by rw [hKw_def]; positivity
  have hKbinj : ∀ j, 0 ≤ Kr * (4*Cs*Ccf j^2)^N * Kcf j * Ch^Jo := fun j => by
    have := hKcf j; positivity
  obtain ⟨Kbin, hKbin_def⟩ : ∃ x : ℝ, x = ∑ j, Kr * (4*Cs*Ccf j^2)^N * Kcf j * Ch^Jo :=
    ⟨_, rfl⟩
  have hKbin : 0 ≤ Kbin := by rw [hKbin_def]; exact Finset.sum_nonneg fun j _ => hKbinj j
  obtain ⟨E, hE_def⟩ : ∃ n : ℕ, n = ∑ j, ((Record12518109GainWholeGeometry.wholeRegularDictionary
      rayM H hH (anchors j) η₀).exceptional_cores_finite.toFinset).card := ⟨_, rfl⟩
  refine ⟨Ct * Kw + ((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D, by positivity,
    S₀, ?_⟩
  have hbΦev : ∀ᶠ Z : ℝ in atTop, bΦ ≤ Z^margin :=
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop bΦ)
  filter_upwards [hpw η₀, Filter.eventually_all.mpr hevj, hbΦev, eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop 2)] with Z hZpw hZj hZb hZ1 hZτ
  refine ⟨hZ1, hZτ, ?_⟩
  intro j w₀ st hchar hpunct hwidth hMst hQM hQη h T θ w σ v' t height hw0 hwm hw1 hσ hσ' hh0 hv'
    hwin hhle hgate p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hZτ0 : 0 ≤ Z^τ := Real.rpow_nonneg hZ0.le _
  have hZτ1 : 1 ≤ Z^τ := by linarith
  have hM0 : 0 ≤ st.rowWidth := st.row_nonneg
  have hMc : st.rowWidth ≤ Mcap := by
    have h1 := st.character_nonneg
    have h2 : st.width = st.rowWidth + st.characterWidth := rfl
    linarith
  have hPl0 : 0 ≤ length Z X₁ + length Z X₂ :=
    add_nonneg (length_nonneg Z X₁ hZ1) (length_nonneg Z X₂ hZ1)
  have hS0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw0 i
  obtain ⟨M', hM'_def⟩ : ∃ x : ℝ, x = st.rowWidth + margin := ⟨_, rfl⟩
  have hM'0 : 0 ≤ M' := by rw [hM'_def]; linarith
  have hM'M : st.rowWidth ≤ M' := by rw [hM'_def]; linarith
  have hM'c : M' ≤ Mcap + 1/2 := by rw [hM'_def]; linarith
  set ctl2 : ℝ := (p.control S₀)^2 with hctl2_def
  have hctl0 : 0 ≤ ctl2 := sq_nonneg _
  set Pl : ℝ := length Z X₁ + length Z X₂ with hPl_def
  set S : ℝ := ∑ i, w i with hS_def
  set T₀ : ℝ := ((h+1 : ℕ) : ℝ)*Z^τ with hT₀_def
  have hT₀ : 2 < T₀ := by
    have h1 : (1:ℝ) ≤ ((h+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos h
    have h2 := mul_le_mul_of_nonneg_right h1 hZτ0
    rw [hT₀_def]; linarith
  -- the energy over a finite support
  obtain ⟨G, hG, hEn⟩ := energy_le_support st.character st.mask 1 t (p.profile 0) (p.profile 1)
    (fun i => primePool rayM H 2 (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v' i) I)
    (fun i => Z^(w i)) X₁ X₂
    (fun z => st.radial.keep z ∧ ¬ lowRow rayM H hH st η₀ hQM hQη e T₀ k z)
    st.radial.profile st.radial.scale bΦ (fun z => st.radial.nonneg z) st.radial.scale_pos
    st.radial_support
  set rowS : O → ℝ := fun z => ‖positiveSlotRow st.character st.mask 1 z (p.profile 0)
    (p.profile 1) (fun i => primePool rayM H 2 (Z^(w i)))
    (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v' i) I)
    (fun i => Z^(w i)) t X₁ X₂‖^2 with hrowS_def
  rw [highPriceW_f]
  refine hEn.trans ?_
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg st.radial.profile
  suffices hsum : ∑ z ∈ G, rowS z ≤
      (Ct * Kw + ((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D) * ctl2 *
      (1+|t|+height)^Jo * Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
        (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh)) by
    calc QuadraticInitialBound.diagonalControl st.radial.profile * ∑ z ∈ G, rowS z
        ≤ QuadraticInitialBound.diagonalControl st.radial.profile *
          ((Ct * Kw + ((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D) * ctl2 *
            (1+|t|+height)^Jo * Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
              (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh))) :=
          mul_le_mul_of_nonneg_left hsum hdiag
      _ = _ := by ring
  -- the rows of the support
  have hGk : ∀ z ∈ G, st.radial.keep z := fun z hz => (hG z hz).1.1
  have hGnl : ∀ z ∈ G, ¬ lowRow rayM H hH st η₀ hQM hQη e T₀ k z := fun z hz => (hG z hz).1.2
  have hGp : ∀ z ∈ G, st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0 :=
    fun z hz => (hG z hz).2
  set sel : O → BufferIndex e := selectBin rayM H hH st η₀ hQM hQη e T₀ with hsel_def
  have hbinG : ∀ z (hz : z ∈ G), Record1252270103Source.RetainedZeroBin rayM H hH st η₀ hQM hQη
      z (hGk z hz) e T₀ (sel z) := fun z hz =>
    selectBin_spec rayM H hH st η₀ hQM hQη e T₀ he hT₀ hβlo hβhi z (hGk z hz)
  have hhighG : ∀ z ∈ G, (k+1)/2 ≤ bufferValue e (sel z) := fun z hz =>
    selectBin_high rayM H hH st η₀ hQM hQη e T₀ k he hT₀ hβlo hβhi z (hGk z hz) (hGnl z hz)
  have hPW : ∀ z (hz : z ∈ G),
      rowS z ≤ Kr * ctl2 * Z^((2*bufferValue e (sel z)-1)*Pl + 2*ε₁*d) *
        ∏ x ∈ T, slotNs rayM H hH st η₀ W θ w σ v' t z x ∧
      ∀ x ∈ T, slotNs rayM H hH st η₀ W θ w σ v' t z x ≤
        Cs * Z^(2*ε₁*d) * Z^((2*bufferValue e (sel z)-1)*extSlot w 0 x) := by
    intro z hz
    have hbin := hbinG z hz
    have hcB : (sel z).1.val ≤ bufferCount e := hbin.2.1
    have hup := hbin.2.2.2.2.2.2.2.2
    rw [hT₀_def, binIndex_height] at hup
    exact hZpw.2 st hpunct hwidth hQM hQη (bufferValue e (sel z)) (binIndex (sel z).1.val h)
      hbin.2.2.1 (by linarith [hbin.2.2.2.2.1]) z (hGk z hz) (hGp z hz) hup T θ w σ v' t height
      hw0 hw1 hσ hσ' hh0 hv' (window_binIndex _ h hZτ0 hwin)
      (gate_binIndex _ h (bufferCount e) 4 hZτ0 hcB hgate) p X₁ X₂ hX₁ hX₂ hl₁ hl₂
  have hWB : ∀ z ∈ G, rowS z ≤ Kw * ctl2 * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hPW z hz
    have hbin := hbinG z hz
    have hν0 : 0 ≤ 2*bufferValue e (sel z) - 1 := by linarith [hbin.2.2.1]
    have hν : 2*bufferValue e (sel z) - 1 ≤ 3/4 := by linarith [hbin.2.2.2.2.1]
    have hprod := whole_row_prod_le T (slotNs rayM H hH st η₀ W θ w σ v' t z) (extSlot w 0)
      (Cs * Z^(2*ε₁*d)) Z (2*bufferValue e (sel z)-1) hZ0
      (fun x _ => slotNs_nonneg rayM H hH st η₀ W θ w σ v' t z x) h2
    rw [sum_extSlot] at hprod
    have hT : T.card ≤ N := Finset.card_le_univ T
    have hε : 0 ≤ ε₁*d := by positivity
    have hK0 : 0 ≤ Kr * ctl2 * Z^((2*bufferValue e (sel z)-1)*Pl + 2*ε₁*d) := by positivity
    rw [hKw_def]
    exact whole_bound_alg hZ1 hKr.le hctl0 hCs hε hν0 hν hPl0 hS0 hT
      (h1.trans (mul_le_mul_of_nonneg_left hprod hK0))
  -- nonzero frequencies
  have hG0 : ∀ z ∈ G, z ≠ 0 := fun z hz => st.row_ne_zero z (hGk z hz)
  set R : Finset NonzeroFrequency := G.subtype (fun z => z ≠ 0) with hR_def
  have hmemR : ∀ hh : NonzeroFrequency, hh ∈ R ↔ hh.val ∈ G := fun hh => Finset.mem_subtype
  have hsumR : ∑ z ∈ G, rowS z = ∑ hh ∈ R, rowS hh.val := by
    rw [hR_def, Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem hG0]
  have hnormR : ∀ hh ∈ R, LocalMoment.rawFrequencyNorm hh ≤ Z^M' := by
    intro hh hhR
    have hz := (hmemR hh).mp hhR
    have hs := st.radial_support (hGp _ hz)
    have h1 : ‖eisEmbedding hh.val‖^2 ≤ bΦ*st.radial.scale :=
      (div_le_iff₀ st.radial.scale_pos).mp hs
    rw [st.scale_eq, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at h1
    unfold LocalMoment.rawFrequencyNorm
    calc ((Ideal.span {hh.val}).absNorm : ℝ) ≤ bΦ * Z^st.rowWidth := h1
      _ ≤ Z^margin * Z^st.rowWidth :=
          mul_le_mul_of_nonneg_right hZb (Real.rpow_nonneg hZ0.le _)
      _ = Z^M' := by rw [← Real.rpow_add hZ0, hM'_def, add_comm]
  have hpair : ∀ (u : FreeRow) (B : NZIdeal), sixthFrequencyEquiv (u, B) ∈ R →
      ProbeHighRowFamily.rowNorm u ≤ Z^(Cofactor.coreWidth Z M' B) ∧
        (B.val.absNorm : ℝ) ≤ Z^Broot := by
    intro u B hR
    have hn := hnormR _ hR
    rw [LocalMoment.raw_sixth_norm] at hn
    refine ⟨rowNorm_le_coreWidth hZ1 u B hn, ?_⟩
    have h1 := ProbeHighRowFamily.rowNorm_ge_one u
    have hn' : ProbeHighRowFamily.rowNorm u * (B.val.absNorm : ℝ)^6 ≤ Z^M' := hn
    have hB6 : (B.val.absNorm : ℝ)^6 ≤ Z^M' :=
      le_trans (le_mul_of_one_le_left (by positivity) h1) hn'
    refine (le_rpow_of_pow_six_le (Nat.cast_nonneg _) hZ0 hB6).trans
      (Real.rpow_le_rpow_of_exponent_le hZ1.le ?_)
    rw [hBroot_def]; linarith
  -- tiny and large classes
  have hsplit : ∑ hh ∈ R, rowS hh.val =
      ∑ hh ∈ R.filter (fun hh => Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2 ≤ 2/25),
        rowS hh.val +
      ∑ hh ∈ R, (if Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2 ≤ 2/25 then 0
        else rowS hh.val) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_filter_add_sum_filter_not]
  -- the tiny classes
  have htinyS : ∑ hh ∈ R.filter (fun hh => Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2
      ≤ 2/25), rowS hh.val ≤ (Ct * Kw) * ctl2 *
        Z^(M'*(1/6+δs) + (5*(2/25)/6 + δs) + (3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1))) := by
    have hX1 : 1 ≤ Z^M' := Real.one_le_rpow hZ1.le hM'0
    have hcard := htiny Z hZ1.le (Z^M') hX1
      ((R.filter (fun hh => Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2 ≤ 2/25)).map
        ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro z hz
      obtain ⟨hh, hhm, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨hhR, hht⟩ := Finset.mem_filter.mp hhm
      refine ⟨hh.property, hnormR hh hhR, ?_⟩
      have e1 : sixthFrequencyEquiv (sixthFrequencyEquiv.symm hh) = hh :=
        Equiv.apply_symm_apply _ hh
      have hR' : sixthFrequencyEquiv ((sixthFrequencyEquiv.symm hh).1,
          (sixthFrequencyEquiv.symm hh).2) ∈ R := by
        rw [Prod.mk.eta, e1]; exact hhR
      obtain ⟨hcw, -⟩ := hpair _ _ hR'
      refine ⟨idealGenerator (sixthFrequencyEquiv.symm hh).2.val,
        (sixthFrequencyEquiv.symm hh).1.val, ?_, ?_⟩
      · show hh.val = _
        have e2 := congrArg Subtype.val e1
        rw [← e2, sixthFrequencyEquiv_apply]
        ring
      · exact hcw.trans (Real.rpow_le_rpow_of_exponent_le hZ1.le hht))
    rw [Finset.card_map] at hcard
    have hnn : 0 ≤ Kw * ctl2 * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) := by positivity
    have e : Z^(M'*(1/6+δs)) * Z^(5*(2/25)/6 + δs) * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) =
        Z^(M'*(1/6+δs) + (5*(2/25)/6 + δs) + (3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1))) := by
      rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]
    calc ∑ hh ∈ R.filter (fun hh => Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2
          ≤ 2/25), rowS hh.val
        ≤ ∑ hh ∈ R.filter (fun hh => Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2
          ≤ 2/25), Kw * ctl2 * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) :=
          Finset.sum_le_sum fun hh hhm => hWB hh.val ((hmemR hh).mp (Finset.mem_filter.mp hhm).1)
      _ = ((R.filter (fun hh => Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2
          ≤ 2/25)).card : ℝ) * (Kw * ctl2 * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Ct * (Z^M')^(1/6 + δs) * Z^(5*(2/25)/6 + δs)) *
          (Kw * ctl2 * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1))) :=
          mul_le_mul_of_nonneg_right hcard hnn
      _ = (Ct * Kw) * ctl2 * (Z^(M'*(1/6+δs)) * Z^(5*(2/25)/6 + δs) *
          Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1))) := by
          rw [← Real.rpow_mul hZ0.le]; ring
      _ = _ := by rw [e]
  -- the large classes
  set Y : ℝ := (1+|t|+height) * Z^τ with hY_def
  have hY1 : 1 ≤ Y := one_le_mul_of_one_le_of_one_le (by linarith [abs_nonneg t]) hZτ1
  have hY0 : 0 ≤ Y := zero_le_one.trans hY1
  have hYJ : 1 ≤ Y^Jo := one_le_pow₀ hY1
  obtain ⟨lamv, hlamv_def⟩ : ∃ x : ℝ, x = 2*ε₁*d*((N:ℝ)+1) + (N:ℝ)*wmin +
      (margin + dmax*(δs + 154*εd + εm + δs) + mesh + 2*bw*(N:ℝ)) := ⟨_, rfl⟩
  have class_bound : ∀ B : NZIdeal, 2/25 < Cofactor.coreWidth Z M' B →
      ∑ u ∈ LocalMoment.sixthFreeFiber R B, rowS (sixthFrequencyEquiv (u, B)).val ≤
        (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * ctl2 * Y^Jo) *
          Z^(Cofactor.coreWidth Z M' B +
            highPriceFW a0 a1 k wlo Pl S (Cofactor.coreWidth Z M' B) + lamv) := by
    intro B hbig
    have hfibG : ∀ u ∈ LocalMoment.sixthFreeFiber R B, (sixthFrequencyEquiv (u, B)).val ∈ G :=
      fun u hu => (hmemR _).mp (sfe_mem_of_fiber hu)
    have hdBM : Cofactor.coreWidth Z M' B ≤ M' := Cofactor.coreWidth_le Z M' hZ1 B
    have hq1 : (2/25:ℝ) ≤ Cofactor.coreWidth Z M' B + margin := by linarith
    have hq2 : Cofactor.coreWidth Z M' B + margin ≤ dmax := by rw [hdmax_def]; linarith
    have hq0 : 0 < Cofactor.coreWidth Z M' B + margin := by linarith
    have hdB0 : 0 < Cofactor.coreWidth Z M' B := by linarith
    set dB := Cofactor.coreWidth Z M' B with hdB_def
    set fib := LocalMoment.sixthFreeFiber R B with hfib_def
    obtain ⟨Ecls, hEcls_def⟩ : ∃ x : ℝ, x = Z^(dB + highPriceFW a0 a1 k wlo Pl S dB + lamv) :=
      ⟨_, rfl⟩
    have hEcls0 : 0 ≤ Ecls := by rw [hEcls_def]; exact Real.rpow_nonneg hZ0.le _
    -- the exceptional cores, paid pointwise
    have hexc : ∑ u ∈ fib.filter (fun u => ¬ RegularCore rayM H hH (anchors j) η₀ u),
        rowS (sixthFrequencyEquiv (u, B)).val ≤ (E:ℝ) * (Kw * ctl2 * Y^Jo * Ecls) := by
      have hsub : fib.filter (fun u => ¬ RegularCore rayM H hH (anchors j) η₀ u) ⊆
          (Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH (anchors j)
            η₀).exceptional_cores_finite.toFinset := by
        intro u hu
        have hnr := (Finset.mem_filter.mp hu).2
        unfold RegularCore at hnr
        rw [not_not] at hnr
        exact (Set.Finite.mem_toFinset _).mpr hnr
      have hcardE : ((fib.filter (fun u => ¬ RegularCore rayM H hH (anchors j) η₀ u)).card : ℝ)
          ≤ E := by
        have h1 := Finset.card_le_card hsub
        have h2 : ((Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH (anchors j)
            η₀).exceptional_cores_finite.toFinset).card ≤ E := by
          rw [hE_def]
          exact Finset.single_le_sum (f := fun j => ((Record12518109GainWholeGeometry.wholeRegularDictionary
            rayM H hH (anchors j) η₀).exceptional_cores_finite.toFinset).card)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        exact_mod_cast h1.trans h2
      have hexp : 3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1) ≤ dB + highPriceFW a0 a1 k wlo Pl S dB + lamv := by
        have ht := tinyEx_le_highPriceFW a0 a1 k wlo Pl S dB
        unfold tinyEx at ht
        have hl1 : 0 ≤ (N:ℝ)*wmin := by positivity
        have hl2 : 0 ≤ dmax*(δs + 154*εd + εm + δs) := by positivity
        have hl3 : 0 ≤ 2*bw*(N:ℝ) := by positivity
        rw [hlamv_def]
        linarith
      have hpt : ∀ u ∈ fib.filter (fun u => ¬ RegularCore rayM H hH (anchors j) η₀ u),
          rowS (sixthFrequencyEquiv (u, B)).val ≤ Kw * ctl2 * Y^Jo * Ecls := by
        intro u hu
        refine (hWB _ (hfibG u (Finset.mem_filter.mp hu).1)).trans ?_
        have hZle : Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) ≤ Ecls := by
          rw [hEcls_def]; exact Real.rpow_le_rpow_of_exponent_le hZ1.le hexp
        have hKc0 : 0 ≤ Kw * ctl2 := by positivity
        calc Kw * ctl2 * Z^(3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) ≤ Kw * ctl2 * Ecls :=
              mul_le_mul_of_nonneg_left hZle hKc0
          _ = (Kw * ctl2 * Ecls) * 1 := by ring
          _ ≤ (Kw * ctl2 * Ecls) * Y^Jo := mul_le_mul_of_nonneg_left hYJ (by positivity)
          _ = Kw * ctl2 * Y^Jo * Ecls := by ring
      calc _ ≤ ∑ _u ∈ fib.filter (fun u => ¬ RegularCore rayM H hH (anchors j) η₀ u),
            Kw * ctl2 * Y^Jo * Ecls := Finset.sum_le_sum hpt
        _ = ((fib.filter (fun u => ¬ RegularCore rayM H hH (anchors j) η₀ u)).card : ℝ) *
            (Kw * ctl2 * Y^Jo * Ecls) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (E:ℝ) * (Kw * ctl2 * Y^Jo * Ecls) :=
            mul_le_mul_of_nonneg_right hcardE (by positivity)
    -- the regular cores, one core batch per bin
    have hbins : ∀ pb : BufferIndex e,
        ∑ u ∈ (fib.filter (fun u => RegularCore rayM H hH (anchors j) η₀ u)).filter
          (fun u => sel (sixthFrequencyEquiv (u, B)).val = pb),
          rowS (sixthFrequencyEquiv (u, B)).val ≤ Kbin * ctl2 * Y^Jo * Ecls := by
      intro pb
      set F := (fib.filter (fun u => RegularCore rayM H hH (anchors j) η₀ u)).filter
          (fun u => sel (sixthFrequencyEquiv (u, B)).val = pb) with hF_def
      have hFm : ∀ u ∈ F, u ∈ fib ∧ RegularCore rayM H hH (anchors j) η₀ u ∧
          sel (sixthFrequencyEquiv (u, B)).val = pb := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
        obtain ⟨hu3, hu4⟩ := Finset.mem_filter.mp hu1
        exact ⟨hu3, hu4, hu2⟩
      rcases F.eq_empty_or_nonempty with hFe | ⟨u₁, hu₁⟩
      · rw [hFe, Finset.sum_empty]; positivity
      obtain ⟨hu₁f, -, hsel₁⟩ := hFm u₁ hu₁
      have hz₁ := hfibG u₁ hu₁f
      have hb := hbinG _ hz₁
      rw [hsel₁] at hb
      have hhb := hhighG _ hz₁
      rw [hsel₁] at hhb
      have hb51 : (51:ℝ)/100 < bufferValue e pb := by linarith
      have hb78 : bufferValue e pb ≤ 7/8 := hb.2.2.2.2.1
      have hpB : pb.1.val ≤ bufferCount e := hb.2.1
      have hν0 : 0 ≤ 2*bufferValue e pb - 1 := by linarith
      have hg := gate_binIndex pb.1.val h (bufferCount e) 4 hZτ0 hpB hgate
      have h3 : (1:ℝ) ≤ 3 + ((3*binIndex pb.1.val h+2 : ℕ) : ℝ)*Z^τ := by
        have : (0:ℝ) ≤ ((3*binIndex pb.1.val h+2 : ℕ) : ℝ) := Nat.cast_nonneg _
        have := mul_nonneg this hZτ0
        linarith
      have hwi := window_binIndex pb.1.val h hZτ0 hwin
      set big : Finset α := T.filter (fun x => wmin ≤ extSlot w 0 x) with hbig_def
      have hCsm : 1 ≤ Cs * Z^(2*ε₁*d) * Z^wmin :=
        one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hCs (Real.one_le_rpow hZ1.le (by positivity)))
          (Real.one_le_rpow hZ1.le hwmin.le)
      have hguard : ∀ u ∈ F, ∀ hn : (∀ j', (coreFamily rayM H hH (anchors j) η₀ u j').residue ≠ 1),
          HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH (anchors j) η₀ u) hn
            (3*(binIndex pb.1.val h+1 : ℕ)*Z^τ) < bufferValue e pb + 2*e ∧
          bufferValue e pb ≤ HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH (anchors j) η₀ u)
            hn ((3*binIndex pb.1.val h : ℕ)*Z^τ) := by
        intro u hu hn
        obtain ⟨hu1, -, hsel⟩ := hFm u hu
        have hz := hfibG u hu1
        have hbu := hbinG _ hz
        rw [hsel] at hbu
        have hfam : coreFamily rayM H hH st.character η₀ u =
            coreFamily rayM H hH (anchors j) η₀ u := by rw [hchar]
        have hnc : ∀ j', (coreFamily rayM H hH st.character η₀ u j').residue ≠ 1 := by
          rw [hfam]; exact hn
        have heq : ∀ T', Cycle61InitialMass.geometryRowMaximum rayM H hH st η₀ hQM hQη
            (sixthFrequencyEquiv (u, B)).val (hGk _ hz) T' =
            HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH (anchors j) η₀ u) hn T' :=
          fun T' => (geometryRowMaximum_eq_core rayM H hH st η₀ hQM hQη u B (hGk _ hz) hnc
            T').trans (zeroMaximum_congr hfam hnc hn T')
        have hup := hbu.2.2.2.2.2.2.2.2
        rw [hT₀_def, binIndex_height, heq] at hup
        have hlo' := hbu.2.2.2.2.2.1
        rw [heq] at hlo'
        refine ⟨hup, hlo'.trans (HeckeDetectorZeros.zeroMaximum_mono _ hn ?_)⟩
        rw [hT₀_def]
        have hpi : pb.1.val * (h+1) ≤ binIndex pb.1.val h := by
          have e1 := binIndex_succ pb.1.val h
          have e2 : (pb.1.val + 1) * (h+1) = pb.1.val * (h+1) + (h+1) := by ring
          rw [e2] at e1
          generalize pb.1.val * (h+1) = m at e1 ⊢
          omega
        have hc : ((3 * pb.1.val : ℕ) : ℝ) * (((h+1 : ℕ) : ℝ) * Z^τ) =
            ((3 * (pb.1.val * (h+1)) : ℕ) : ℝ) * Z^τ := by push_cast; ring
        rw [hc]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left 3 hpi) hZτ0
      have hrowF : ∀ u ∈ F, rowS (sixthFrequencyEquiv (u, B)).val ≤
          (Kr * ctl2 * Z^(2*ε₁*d)) * Z^((2*bufferValue e pb-1)*Pl) *
            ∏ x ∈ T, slotNs rayM H hH st η₀ W θ w σ v' t (sixthFrequencyEquiv (u, B)).val x := by
        intro u hu
        obtain ⟨hu1, -, hsel⟩ := hFm u hu
        have h1 := (hPW _ (hfibG u hu1)).1
        rw [hsel, Real.rpow_add hZ0] at h1
        calc _ ≤ _ := h1
          _ = _ := by ring
      have hsmallF : ∀ u ∈ F, ∀ x ∈ T, x ∉ big →
          slotNs rayM H hH st η₀ W θ w σ v' t (sixthFrequencyEquiv (u, B)).val x ≤
            Cs * Z^(2*ε₁*d) * Z^wmin := by
        intro u hu x hx hxb
        obtain ⟨hu1, -, hsel⟩ := hFm u hu
        have h2 := (hPW _ (hfibG u hu1)).2 x hx
        rw [hsel] at h2
        refine h2.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1.le ?_)
          (by positivity))
        have hwx : extSlot w 0 x < wmin := by
          by_contra hc
          exact hxb (Finset.mem_filter.mpr ⟨hx, not_lt.mp hc⟩)
        have hw0x : 0 ≤ extSlot w 0 x := by rw [extSlot_mem w 0 hx]; exact hw0 _
        have := mul_le_mul_of_nonneg_right (show 2*bufferValue e pb - 1 ≤ 1 by linarith) hw0x
        linarith
      have hbigF : ∀ u ∈ F, ∀ x ∈ big,
          slotNs rayM H hH st η₀ W θ w σ v' t (sixthFrequencyEquiv (u, B)).val x =
          ‖CenteredMomentCommonMaskExpansion.naturalSlot
            (excluded (naturalRow (anchors j) (sixthFrequencyEquiv (u, B)).val
              (sixthFrequencyEquiv (u, B)).property).character 1)
            (primePool rayM H 2 (Z^(extSlot w 0 x)))
            (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (extSlot θ 1 x)) I *
              HeckePrimeAnnular.annularWeight W (Z^(extSlot w 0 x)) (extSlot σ (33/50) x)
                (t + extSlot v' 0 x) I) (Z^(extSlot w 0 x))‖^2 := by
        intro u _ x _
        rw [slotNs_eq_raw rayM H hH st η₀ hpunct W θ w σ v' t _
          (sixthFrequencyEquiv (u, B)).property x, hchar]
      have hcb := (hZj j).2.2 dB hq1 hq2 B F T big (extSlot θ 1) (extSlot w 0)
        (extSlot σ (33/50)) (extSlot v' 0) t (|t| + height) mesh (bufferValue e pb) k Pl δs
        (Kr * ctl2 * Z^(2*ε₁*d)) (Cs * Z^(2*ε₁*d) * Z^wmin) (binIndex pb.1.val h)
        (fun u => rowS (sixthFrequencyEquiv (u, B)).val)
        (fun u x => slotNs rayM H hH st η₀ W θ w σ v' t (sixthFrequencyEquiv (u, B)).val x)
        (hpair u₁ B (sfe_mem_of_fiber hu₁f)).2
        (fun u hu => (hpair u B (sfe_mem_of_fiber (hFm u hu).1)).1)
        (fun u hu => (hFm u hu).2.1) (Finset.filter_subset _ _)
        (fun x hx => (Finset.mem_filter.mp hx).2)
        (fun x hx => by rw [extSlot_mem w 0 (Finset.mem_filter.mp hx).1]; exact hw1 _) hmesh0
        (fun x hx => by rw [extSlot_mem w 0 (Finset.mem_filter.mp hx).1]; exact hwm _)
        (by rw [div_le_iff₀ hq0]; linarith [mul_le_mul_of_nonneg_left hq1 hmeshm.le])
        (fun x hx => by
          rw [extSlot_mem σ _ (Finset.mem_filter.mp hx).1]
          exact le_antisymm (hσ' _) (hσ _))
        (fun x hx => by
          rw [extSlot_mem v' 0 (Finset.mem_filter.mp hx).1]
          linarith [hv' ⟨x, (Finset.mem_filter.mp hx).1⟩, abs_nonneg t])
        (by positivity) (by linarith)
        (fun x hx => by
          rw [extSlot_mem v' 0 (Finset.mem_filter.mp hx).1]
          have h1 := abs_add_le t (v' ⟨x, (Finset.mem_filter.mp hx).1⟩)
          have h2 := hv' ⟨x, (Finset.mem_filter.mp hx).1⟩
          linarith)
        (hg.trans (by
          rw [← Real.rpow_mul hZ0.le, ← Real.rpow_mul hZ0.le]
          apply Real.rpow_le_rpow_of_exponent_le hZ1.le
          rw [hηw_def]
          have e : d*v/(2/25) = d*v*(25/2) := by ring
          rw [e]
          linarith [mul_nonneg hdv (show (0:ℝ) ≤ (dB + margin)*(25/2) - 1 by linarith)]))
        (le_trans (pow_le_pow_right₀ h3 (by norm_num)) hg)
        hb51 (by linarith) (by linarith) (by linarith) (by linarith) hlo ha1 ha1' hδs
        (by positivity) hCsm hguard
        (fun u _ x _ => slotNs_nonneg rayM H hH st η₀ W θ w σ v' t _ x) hrowF hsmallF hbigF
      rw [← Finset.sum_div] at hcb
      have hSbS : ∑ x ∈ big, extSlot w 0 x ≤ S := by
        rw [hS_def, ← sum_extSlot]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun x hx _ => by rw [extSlot_mem w 0 hx]; exact hw0 _)
      have hSb0 : 0 ≤ ∑ x ∈ big, extSlot w 0 x := Finset.sum_nonneg fun x hx => by
        rw [extSlot_mem w 0 (Finset.mem_filter.mp hx).1]; exact hw0 _
      have hSbN : ∑ x ∈ big, extSlot w 0 x ≤ (N:ℝ) := by
        calc ∑ x ∈ big, extSlot w 0 x ≤ ∑ _x ∈ big, (1:ℝ) := Finset.sum_le_sum fun x hx => by
              rw [extSlot_mem w 0 (Finset.mem_filter.mp hx).1]; exact hw1 _
          _ = (big.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          _ ≤ (N:ℝ) := by
              exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
                (Finset.card_le_univ T)
      have hX := bin_exponent_le (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hk1
        (q := dB + margin) (dB := dB) (margin := margin) (Mc := dmax) (P := Pl) (S := S)
        (Sb := ∑ x ∈ big, extSlot w 0 x) (ε' := δs) (ε := εd) (εm := εm) (ηd := δs) (bw := bw)
        (mesh := mesh) (a := bufferValue e pb) (N := (N:ℝ)) rfl hdB0 hmargin.le hq2 hSb0 hSbS
        hSbN hδs.le hεd.le hεm.le hδs.le hbw.le hmesh0 hν0 (by linarith)
      have hHD1 : 1 ≤ 1 + (2*Real.pi*((Z^(dB+margin))^(τ/(2*dmax))) +
          ((3*binIndex pb.1.val h : ℕ) : ℝ)*Z^τ + (|t| + (|t| + height))) := by
        have : 0 ≤ 2*Real.pi*((Z^(dB+margin))^(τ/(2*dmax))) := by
          have := Real.pi_pos
          have := Real.rpow_nonneg (Real.rpow_nonneg hZ0.le (dB+margin)) (τ/(2*dmax))
          positivity
        have : 0 ≤ ((3*binIndex pb.1.val h : ℕ) : ℝ)*Z^τ := by positivity
        have := abs_nonneg t
        linarith
      have hHDY : 1 + (2*Real.pi*((Z^(dB+margin))^(τ/(2*dmax))) +
          ((3*binIndex pb.1.val h : ℕ) : ℝ)*Z^τ + (|t| + (|t| + height))) ≤ Ch * Y := by
        have hYq : (Z^(dB+margin))^(τ/(2*dmax)) ≤ Z^τ := by
          rw [← Real.rpow_mul hZ0.le]
          apply Real.rpow_le_rpow_of_exponent_le hZ1.le
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          linarith [mul_le_mul_of_nonneg_right hq2 hτ.le, mul_pos hdmax0 hτ]
        have hi : ((binIndex pb.1.val h : ℕ) : ℝ) ≤ ((bufferCount e : ℝ) + 1) * ((h:ℝ) + 1) := by
          have h1 := Nat.le_of_succ_le (binIndex_le pb.1.val h (bufferCount e) hpB)
          exact_mod_cast h1
        have hfac := height_factor_le (x := |t| + (|t| + height)) hYq hZτ1 (by positivity) hi
          (by linarith [abs_nonneg t])
        have hB0 : (0:ℝ) ≤ 8 + 6*((bufferCount e : ℝ) + 1) := by positivity
        have h1x : 1 + (|t| + (|t| + height)) ≤ 2*(1+|t|+height) := by linarith
        have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1x hB0) hZτ0
        calc _ ≤ _ := hfac
          _ ≤ (8 + 6*((bufferCount e : ℝ) + 1)) * (2*(1+|t|+height)) * Z^τ := hm
          _ = Ch * Y := by rw [hCh_def, hY_def]; ring
      have hJ : Jf j + 1 ≤ Jo := by
        rw [hJo_def]
        have := Finset.single_le_sum (f := Jf) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      have hn : (T \ big).card + big.card ≤ N := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)]
        exact Finset.card_le_univ T
      have hfin := bin_constant_le (Ch := Ch) (Y := Y) (Jo := Jo) (N := N) hZ1 hKr.le hctl0 hCs
        (hCcf j) (hKcf j) hHD1 hHDY hJ hn hε₁.le hd.le hwmin.le hX
      have hKj : Kr * (4*Cs*Ccf j^2)^N * Kcf j * Ch^Jo ≤ Kbin := by
        rw [hKbin_def]
        exact Finset.single_le_sum (f := fun j => Kr * (4*Cs*Ccf j^2)^N * Kcf j * Ch^Jo)
          (fun j _ => hKbinj j) (Finset.mem_univ j)
      have hexpeq : 2*ε₁*d*((N:ℝ)+1) + (N:ℝ)*wmin + (dB + highPriceFW a0 a1 k wlo Pl S dB +
          (margin + dmax*(δs + 154*εd + εm + δs) + mesh + 2*bw*(N:ℝ))) =
          dB + highPriceFW a0 a1 k wlo Pl S dB + lamv := by rw [hlamv_def]; ring
      have hpos : 0 ≤ ctl2 * Y^Jo * Ecls := by positivity
      calc _ ≤ (Kr * (4*Cs*Ccf j^2)^N * Kcf j * Ch^Jo) * ctl2 * Y^Jo *
            Z^(2*ε₁*d*((N:ℝ)+1) + (N:ℝ)*wmin + (dB + highPriceFW a0 a1 k wlo Pl S dB +
              (margin + dmax*(δs + 154*εd + εm + δs) + mesh + 2*bw*(N:ℝ)))) := hcb.trans hfin
        _ = (Kr * (4*Cs*Ccf j^2)^N * Kcf j * Ch^Jo) * (ctl2 * Y^Jo * Ecls) := by
            rw [hexpeq, hEcls_def]; ring
        _ ≤ Kbin * (ctl2 * Y^Jo * Ecls) := mul_le_mul_of_nonneg_right hKj hpos
        _ = Kbin * ctl2 * Y^Jo * Ecls := by ring
    -- the class sum
    have hsplit2 : ∑ u ∈ fib, rowS (sixthFrequencyEquiv (u, B)).val =
        ∑ u ∈ fib.filter (fun u => ¬ RegularCore rayM H hH (anchors j) η₀ u),
          rowS (sixthFrequencyEquiv (u, B)).val +
        ∑ pb : BufferIndex e, ∑ u ∈ (fib.filter (fun u => RegularCore rayM H hH (anchors j) η₀ u)).filter
          (fun u => sel (sixthFrequencyEquiv (u, B)).val = pb),
          rowS (sixthFrequencyEquiv (u, B)).val := by
      rw [Finset.sum_fiberwise, Finset.sum_filter_not_add_sum_filter]
    rw [hsplit2, ← hEcls_def]
    calc _ ≤ (E:ℝ) * (Kw * ctl2 * Y^Jo * Ecls) +
          ∑ _pb : BufferIndex e, Kbin * ctl2 * Y^Jo * Ecls :=
          add_le_add hexc (Finset.sum_le_sum fun pb _ => hbins pb)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hlarge := hcof a0 a1 k wlo (by linarith) hk1 R
    (fun hh => if Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2 ≤ 2/25 then 0
      else rowS hh.val) Z M' Pl S
    (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * ctl2 * Y^Jo) lamv hZ1 hM'0 hS0
    (by positivity) hnormR (by
      intro B _
      have hfval : ∀ u ∈ LocalMoment.sixthFreeFiber R B,
          (fun hh => if Cofactor.coreWidth Z M' (sixthFrequencyEquiv.symm hh).2 ≤ 2/25 then 0
            else rowS hh.val) (sixthFrequencyEquiv (u, B)) =
          if Cofactor.coreWidth Z M' B ≤ 2/25 then 0
            else rowS (sixthFrequencyEquiv (u, B)).val := by
        intro u _
        simp only [Equiv.symm_apply_apply]
      refine ⟨fun hbig => ?_, fun hsmall => ?_⟩
      · rw [Finset.sum_congr rfl hfval]
        simp only [if_neg (not_le.mpr hbig)]
        exact class_bound B hbig
      · rw [Finset.sum_congr rfl hfval]
        simp only [if_pos hsmall, Finset.sum_const_zero]
        positivity)
  -- the budget
  have hδsdef2 : δs * (Mcap + 2) = δu / 100 := by rw [hδs_def]; field_simp
  have hδsM : δs * (M' + 1) ≤ δu / 100 := by
    rw [← hδsdef2]; exact mul_le_mul_of_nonneg_left (by linarith) hδs.le
  have hNw : (N:ℝ) * wmin ≤ δu / 100 := by
    have e1 : ((N:ℝ) + 1) * wmin = δu / 100 := by rw [hwmin_def]; field_simp
    linarith
  have hbwN : 2*bw*(N:ℝ) ≤ δu / 100 := by
    have e1 : 2*bw*((N:ℝ) + 1) = δu / 100 := by rw [hbw_def]; field_simp; ring
    linarith
  have hdδs : dmax * δs ≤ δu / 100 := by
    have h1 := mul_le_mul_of_nonneg_right (show dmax ≤ Mcap + 2 by rw [hdmax_def]; linarith) hδs.le
    linarith
  have hdεd : dmax * εd ≤ δu / 200 := by rw [hdmax_def]; linarith [hεd2]
  have hdεm : dmax * εm ≤ loss * Mcap / 100 := by
    rw [hdmax_def, hεm_def]
    have hpos : 0 < 100*(Mmin+1) := by positivity
    rw [show (Mcap + 1) * (loss * Mmin / (100 * (Mmin + 1))) =
      ((Mcap+1)*(loss*Mmin)) / (100*(Mmin+1)) by ring, div_le_iff₀ hpos]
    linarith [mul_le_mul_of_nonneg_left hMM hloss.le]
  have hprice := highPriceFW_antitoneM (a0 := a0) (a1 := a1) (wlo := wlo) hk0 hk1 Pl S hM'M
  have htinyM := tinyEx_le_highPriceFW a0 a1 k wlo Pl S st.rowWidth
  unfold tinyEx at htinyM
  have hτJ : 0 ≤ τ*(Jo:ℝ) := by positivity
  have hE1 : M'*(1/6+δs) + (5*(2/25)/6 + δs) + (3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1)) ≤
      st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
        (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh) := by
    rw [hM'_def] at hδsM ⊢
    linarith
  have hE2 : τ*(Jo:ℝ) + (M' + highPriceFW a0 a1 k wlo Pl S M' + lamv + δs*M') ≤
      st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
        (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh) := by
    have hexp2 : dmax*(δs + 154*εd + εm + δs) = 2*(dmax*δs) + 154*(dmax*εd) + dmax*εm := by ring
    rw [hlamv_def, hexp2]
    rw [hM'_def] at hδsM hprice ⊢
    linarith
  -- assembly
  have hHt : 1 ≤ (1+|t|+height)^Jo := one_le_pow₀ (by linarith [abs_nonneg t])
  have hZtgt : 0 ≤ Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
      (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh)) := Real.rpow_nonneg hZ0.le _
  have hA : (Ct * Kw) * ctl2 *
      Z^(M'*(1/6+δs) + (5*(2/25)/6 + δs) + (3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1))) ≤
      (Ct * Kw) * ctl2 * ((1+|t|+height)^Jo *
        Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
          (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh))) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hZ1.le hE1
    have h2 : Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
        (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh)) ≤ (1+|t|+height)^Jo *
        Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
          (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh)) :=
      le_mul_of_one_le_left hZtgt hHt
    exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
  have hZτJ : (Z^τ)^Jo = Z^(τ*(Jo:ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
  have hB : (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * ctl2 * Y^Jo) * D *
      Z^(M' + highPriceFW a0 a1 k wlo Pl S M' + lamv + δs*M') ≤
      (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D * ctl2) *
        ((1+|t|+height)^Jo * Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
          (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh))) := by
    rw [hY_def, mul_pow, hZτJ]
    have hz : Z^(τ*(Jo:ℝ)) * Z^(M' + highPriceFW a0 a1 k wlo Pl S M' + lamv + δs*M') ≤
        Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
          (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh)) := by
      rw [← Real.rpow_add hZ0]
      exact Real.rpow_le_rpow_of_exponent_le hZ1.le hE2
    have h0 : 0 ≤ ((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D * ctl2 *
        (1+|t|+height)^Jo := by positivity
    calc _ = (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D * ctl2 *
          (1+|t|+height)^Jo) * (Z^(τ*(Jo:ℝ)) *
            Z^(M' + highPriceFW a0 a1 k wlo Pl S M' + lamv + δs*M')) := by ring
      _ ≤ (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D * ctl2 *
          (1+|t|+height)^Jo) * Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
            (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh)) :=
          mul_le_mul_of_nonneg_left hz h0
      _ = _ := by ring
  rw [hsumR, hsplit]
  calc _ ≤ (Ct * Kw) * ctl2 *
        Z^(M'*(1/6+δs) + (5*(2/25)/6 + δs) + (3/4*Pl + S + 2*ε₁*d*((N:ℝ)+1))) +
      (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * ctl2 * Y^Jo) * D *
        Z^(M' + highPriceFW a0 a1 k wlo Pl S M' + lamv + δs*M') := add_le_add htinyS hlarge
    _ ≤ (Ct * Kw) * ctl2 * ((1+|t|+height)^Jo *
          Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
            (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh))) +
        (((E:ℝ) * Kw + (Fintype.card (BufferIndex e) : ℝ) * Kbin) * D * ctl2) *
          ((1+|t|+height)^Jo * Z^(st.rowWidth + highPriceFW a0 a1 k wlo Pl S st.rowWidth +
            (2*ε₁*d*((N:ℝ) + 1) + loss*Mcap + τ*(Jo:ℝ) + mesh))) := add_le_add hA hB
    _ = _ := by ring

end
end Qrh.MarkedAnchor.High
