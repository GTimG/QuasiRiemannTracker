/- Copyright (c) 2026 Sil. Apache-2.0.
The localized family follows Hailey Collet's `NaturalBatch.localizeFamily`
(`Record12518109Gain/LocalizedBatch.lean`, Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafMarkedInput
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.BatchMax
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.BatchAbs
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafCoreSlot
import Submissions.hailey_collet_1252270103.LocalMoment.ActualUnmarkedInputs

/-!
# High.LeafCoreBatch

The detector bound of ONE core batch of the HIGH leaf (the core half):
regular sixth-free cores `rows` of the fixed dictionary of `η`, at the core scale `U = Z^q`
(`q ∈ [dmin, dmax]`), with
* the buffered zero guards of the core family at heights `3 i Z^τ` / `3 (i+1) Z^τ`;
* conductors `≤ Z^q`;
* the core slot envelope `‖coreSlot‖ ≤ A (Z^w)^((2a-1)/2)` (`High.LeafCoreSlot.core_slot_bound`);
* slot widths `w ≥ wmin` with relative widths `w/q ≤ meshm`;

satisfy

`(∑ ∏ max 1 ‖coreSlot‖²) Z^((2a-1)P) ≤ (A²)^#slots Kc (1+height)^(J+1) (Z^q)^(1 + max 0 detPriceW(P/q, S, 1) + ε' + losses + ηd)`.

The proof localizes the core family at a batch row (`locFamily`), rescales the slots by `A⁻¹`, and
runs `High.BatchMax.core_batch_guards` with the fiber moments of `High.LeafMarkedInput.locFiberInputsH`.
The bin and label counts are absorbed by `binLabel_card_le` and HC's `fixed_label_dyadic_cost`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDyadic HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open HeckeDetectorDyadicProfiles Cycle61Moment HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
local instance leafCoreBatchQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- An eventual property of the scale `U` holds uniformly at `U = Z^q`, `q ≥ dmin > 0`. -/
theorem eventually_rpow_uniform {p : ℝ → Prop} (hp : ∀ᶠ U : ℝ in atTop, p U) {dmin : ℝ}
    (hdmin : 0 < dmin) : ∀ᶠ Z : ℝ in atTop, ∀ q : ℝ, dmin ≤ q → p (Z^q) := by
  obtain ⟨U₀, hU₀⟩ := Filter.eventually_atTop.mp hp
  filter_upwards [(tendsto_rpow_atTop hdmin).eventually (eventually_ge_atTop U₀),
    eventually_ge_atTop (1:ℝ)] with Z hZ hZ1 q hq
  exact hU₀ _ (hZ.trans (Real.rpow_le_rpow_of_exponent_le hZ1 hq))

/-- The amplitude labels are few. -/
theorem labels_card_le (cap mesh : ℝ) (hcap : 0 ≤ cap) (hm : 0 < mesh) :
    ((HeckePrimeAmplitudeBins.labels cap mesh).card : ℝ) ≤ cap/mesh + 4 := by
  unfold HeckePrimeAmplitudeBins.labels
  have h1 := Finset.card_insert_le (0:ℝ)
    (insert cap ((Finset.Icc (0:ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n:ℝ))))
  have h2 := Finset.card_insert_le cap
    ((Finset.Icc (0:ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n:ℝ)))
  have h3 := Finset.card_image_le (s := Finset.Icc (0:ℤ) ⌈cap/mesh⌉)
    (f := fun n : ℤ => mesh*(n:ℝ))
  rw [Int.card_Icc] at h3
  have hc : (0:ℤ) ≤ ⌈cap/mesh⌉ := Int.ceil_nonneg (div_nonneg hcap hm.le)
  have h4 : (((⌈cap/mesh⌉ + 1 - 0).toNat : ℕ) : ℝ) ≤ cap/mesh + 2 := by
    have e1 : (((⌈cap/mesh⌉ + 1 - 0).toNat : ℕ) : ℤ) = ⌈cap/mesh⌉ + 1 := by
      rw [sub_zero]; exact Int.toNat_of_nonneg (by linarith)
    have e2 : (((⌈cap/mesh⌉ + 1 - 0).toNat : ℕ) : ℝ) = ((⌈cap/mesh⌉ : ℤ) : ℝ) + 1 := by
      exact_mod_cast e1
    rw [e2]
    have := Int.ceil_lt_add_one (cap/mesh)
    linarith
  have hn : (insert (0:ℝ) (insert cap ((Finset.Icc (0:ℤ) ⌈cap/mesh⌉).image
      (fun n : ℤ => mesh*(n:ℝ))))).card ≤ (⌈cap/mesh⌉ + 1 - 0).toNat + 2 := by omega
  have hn' : ((insert (0:ℝ) (insert cap ((Finset.Icc (0:ℤ) ⌈cap/mesh⌉).image
      (fun n : ℤ => mesh*(n:ℝ))))).card : ℝ) ≤ (((⌈cap/mesh⌉ + 1 - 0).toNat : ℕ) : ℝ) + 2 := by
    exact_mod_cast hn
  linarith

/-- The amplitude bin labels of a slot set are few, uniformly in the cap `≤ 1`. -/
theorem binLabel_card_le {Slot : Type*} [Fintype Slot] (slots : Finset Slot)
    (cap mesh : ℝ) (hcap : 0 ≤ cap) (hcap' : cap ≤ 1) (hm : 0 < mesh) :
    (Fintype.card (BinLabel slots cap mesh) : ℝ) ≤ (1/mesh + 4)^(Fintype.card Slot) := by
  have hc : Fintype.card (BinLabel slots cap mesh) =
      (HeckePrimeAmplitudeBins.labels cap mesh).card ^ slots.card := by
    simp only [BinLabel, Fintype.card_fun, Fintype.card_coe]
  rw [hc]
  push_cast
  have hl := labels_card_le cap mesh hcap hm
  have hcm : cap/mesh ≤ 1/mesh := div_le_div_of_nonneg_right hcap' hm.le
  have h1 : (1:ℝ) ≤ 1/mesh + 4 := by have := one_div_pos.mpr hm; linarith
  calc ((HeckePrimeAmplitudeBins.labels cap mesh).card : ℝ)^slots.card
      ≤ (1/mesh + 4)^slots.card := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
    _ ≤ (1/mesh + 4)^(Fintype.card Slot) := pow_le_pow_right₀ h1 (Finset.card_le_univ _)

/-- Zero maxima of equal families agree. -/
theorem zeroMaximum_congr {ι : Type*} [Fintype ι] {f g : ι → Character} (h : f = g)
    (hf : ∀ j, (f j).residue ≠ 1) (hg : ∀ j, (g j).residue ≠ 1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum f hf T = HeckeDetectorZeros.zeroMaximum g hg T := by
  subst h; rfl

/-- The constant bookkeeping of `core_batch_class`. -/
theorem core_batch_final {Sc SQ ZP NB NL D2 Hh HJ C Lb Kdy ZE Zd Ap : ℝ}
    (hsum : Sc ≤ Ap * SQ) (hbatch : SQ * ZP ≤ NB * NL * D2 * (192*Hh*(C*HJ)) * ZE)
    (hbin : NB ≤ Lb) (hdy : NL * D2 ≤ Kdy * Zd) (hZP : 0 ≤ ZP) (hAp : 0 ≤ Ap) (hZE : 0 ≤ ZE)
    (hNB : 0 ≤ NB) (hNL : 0 ≤ NL * D2) (hH : 0 ≤ 192*Hh*(C*HJ)) {HJ1 ZEd : ℝ}
    (hHJ : HJ1 = HJ * Hh) (hZEd : ZEd = ZE * Zd) :
    Sc * ZP ≤ Ap * ((Lb * Kdy * 192 * C) * HJ1) * ZEd := by
  rw [hHJ, hZEd]
  have h1 : NB * (NL*D2) ≤ Lb * (Kdy*Zd) := mul_le_mul hbin hdy hNL (hNB.trans hbin)
  calc Sc * ZP ≤ (Ap * SQ) * ZP := mul_le_mul_of_nonneg_right hsum hZP
    _ = Ap * (SQ * ZP) := by ring
    _ ≤ Ap * (NB * NL * D2 * (192*Hh*(C*HJ)) * ZE) := mul_le_mul_of_nonneg_left hbatch hAp
    _ = Ap * ((NB * (NL*D2)) * (192*Hh*(C*HJ)) * ZE) := by ring
    _ ≤ Ap * ((Lb * (Kdy*Zd)) * (192*Hh*(C*HJ)) * ZE) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 hH) hZE) hAp
    _ = _ := by ring

/-- **The detector bound of one core batch.** -/
theorem core_batch_class (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) {a0 a1 wlo : ℝ}
    (hM : HighMarkedCoreInputsH a0 a1 wlo) (εm : ℝ) (hεm : 0 < εm) :
    ∃ meshm : ℝ, 0 < meshm ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
      (hH : RayOrthogonality.globalUnits rayM ≤ H)
      (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
      ∀ (η η₀ : Character) {Slot : Type} [Fintype Slot] [DecidableEq Slot] (wmin dmin dmax : ℝ),
      0 < wmin → 0 < dmin → dmin ≤ dmax →
      ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (τ ε e ηw bw ηd : ℝ), 0 < τ → 0 < ε → ε ≤ 1/1000000 → 0 < e → e < 1/1000 →
        0 ≤ ηw → ηw ≤ 2 → 12*e*((22:ℝ)+2)+8*e+2*ηw ≤ ε/2 → 0 < bw → 0 < ηd →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ q : ℝ, dmin ≤ q → q ≤ dmax →
      ∀ (rows : Finset FreeRow) (slots : Finset Slot) (θ : Slot → RayQuotient.Characters rayM H)
        (w σ v : Slot → ℝ) (t : FreeRow → ℝ) (a height mesh A k P ε' : ℝ) (i : ℕ),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ Z^q) →
      (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) →
      (∀ u ∈ rows, ∀ j, ((coreFamily rayM H hH η η₀ u j).modulus.absNorm : ℝ) ≤ Z^q) →
      (∀ u ∈ rows, |t u| ≤ height) →
      (∀ s ∈ slots, wmin ≤ w s) → 0 ≤ mesh → (∀ s ∈ slots, w s ≤ mesh) → mesh/q ≤ meshm →
      (∀ s ∈ slots, σ s = 33/50) → (∀ s ∈ slots, |v s| ≤ height) →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^q)^ηw →
      51/100 < a → 2*a-1 ≤ 3/4 → 0 ≤ k → k ≤ 2*a-1 → wlo ≤ cutHi → 0 ≤ a1 → a1 ≤ 1/2 →
      0 < ε' → 1 ≤ A →
      2*Real.pi*((Z^q)^(τ/(2*dmax)))+(3*i : ℕ)*Z^τ ≤ height →
      (∀ u ∈ rows, ∀ hn : (∀ j, (coreFamily rayM H hH η η₀ u j).residue ≠ 1),
        HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ u) hn (3*(i+1 : ℕ)*Z^τ) <
          a+2*e ∧
        a ≤ HeckeDetectorZeros.zeroMaximum (coreFamily rayM H hH η η₀ u) hn ((3*i : ℕ)*Z^τ)) →
      (∀ u ∈ rows, ∀ s ∈ slots,
        ‖coreSlot rayM H hH η η₀ W (Z^q) θ (fun s => w s / q) σ v t u s‖ ≤
          A * (Z^(w s))^((2*a-1)/2)) →
      (∑ u ∈ rows, ∏ s ∈ slots,
          max 1 (‖coreSlot rayM H hH η η₀ W (Z^q) θ (fun s => w s / q) σ v t u s‖^2)) *
          Z^((2*a-1)*P) ≤
        (A^2)^slots.card * (Kc * (1+height)^(J+1)) *
          (Z^q)^(1 + max 0 (detPriceW a0 a1 k wlo (P/q) (∑ s ∈ slots, w s / q) 1) + ε' +
            (154*ε + (2*a-1)*(mesh/q) + εm + 2*bw*(∑ s ∈ slots, w s / q)) + ηd) := by
  obtain ⟨meshm, hmeshm, hloc⟩ := locFiberInputsH hβ hM εm hεm
  refine ⟨meshm, hmeshm, ?_⟩
  intro rayM _ H hH W hWs hW η η₀ Slot _ _ wmin dmin dmax hwmin hdmin hdd
  have hdmax : 0 < dmax := hdmin.trans_le hdd
  obtain ⟨J, C, hC, hev⟩ := hloc rayM H hH W hWs hW η η₀ (Slot := Slot) (wmin/dmax)
    (div_pos hwmin hdmax)
  refine ⟨J, C, hC, ?_⟩
  intro τ ε e ηw bw ηd hτ hε hε1 he he' hηw hηw2 hbud hbw hηd
  obtain ⟨Z₁, hZ₁⟩ := core_batch_guards dmin dmax τ ε e e ηw hdmin hdd hτ hε hε1 he he' he
    (by linarith) hηw hηw2 hbud
  obtain ⟨Kdy, hKdy, hdy⟩ :=
    OAI.SevenEighths.LocalMoment.fixed_label_dyadic_cost (Label := WholeSourceIndex rayM H) ηd hηd
  have hLb : (1:ℝ) ≤ 1/bw + 4 := by have := one_div_pos.mpr hbw; linarith
  refine ⟨(1/bw + 4)^(Fintype.card Slot) * Kdy * 192 * C, by positivity, ?_⟩
  filter_upwards [eventually_rpow_uniform hev hdmin, eventually_rpow_uniform hdy hdmin,
    eventually_ge_atTop Z₁, eventually_gt_atTop (1:ℝ)] with Z hZev hZdy hZ1' hZ1
  refine ⟨hZ1, ?_⟩
  intro q hq1 hq2 rows slots θ w σ v t a height mesh A k P ε' i hnorm hreg hcond ht hw hmesh hwm hmm hσ
    hv hgate ha hν hk0 hk hlo ha1 ha1' hε' hA hfreq hguard hQ
  have hZ0 : 0 < Z := zero_lt_one.trans hZ1
  have hq0 : 0 < q := hdmin.trans_le hq1
  have hU : 1 < Z^q := Real.one_lt_rpow hZ1 hq0
  have hU0 : 0 < Z^q := zero_lt_one.trans hU
  have hh0 : 0 ≤ height := by
    have h1 : 0 ≤ 2*Real.pi*((Z^q)^(τ/(2*dmax))) := by
      have := Real.pi_pos; have := Real.rpow_nonneg hU0.le (τ/(2*dmax)); positivity
    have h2 : 0 ≤ ((3*i : ℕ) : ℝ)*Z^τ := by
      have := Real.rpow_nonneg hZ0.le τ; positivity
    linarith
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hC' : 0 ≤ C * (1+height)^J := by positivity
  -- the right side is nonnegative
  have hRHS : 0 ≤ (A^2)^slots.card * (((1/bw + 4)^(Fintype.card Slot) * Kdy * 192 * C) *
      (1+height)^(J+1)) *
      (Z^q)^(1 + max 0 (detPriceW a0 a1 k wlo (P/q) (∑ s ∈ slots, w s / q) 1) + ε' +
        (154*ε + (2*a-1)*(mesh/q) + εm + 2*bw*(∑ s ∈ slots, w s / q)) + ηd) := by
    have := Real.rpow_nonneg hU0.le (1 + max 0 (detPriceW a0 a1 k wlo (P/q)
      (∑ s ∈ slots, w s / q) 1) + ε' + (154*ε + (2*a-1)*(mesh/q) + εm +
        2*bw*(∑ s ∈ slots, w s / q)) + ηd)
    positivity
  rcases rows.eq_empty_or_nonempty with hr | ⟨u0, hu0⟩
  · rw [hr, Finset.sum_empty, zero_mul]
    exact hRHS
  -- the localized family
  set χ : FreeRow → WholeSourceIndex rayM H → Character :=
    locFamily rayM H hH η η₀ rows u0 with hχdef
  have hsel : ∀ u, (if u ∈ rows then u else u0) ∈ rows := by
    intro u; split_ifs with hu
    · exact hu
    · exact hu0
  have hχ : ∀ u j, (χ u j).residue ≠ 1 := fun u =>
    core_nonprincipal rayM H hH η η₀ _ (hreg _ (hsel u))
  have hnext : ∀ u, HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) (3*(i+1 : ℕ)*Z^τ) < a+2*e :=
    fun u => (hguard _ (hsel u) (hχ u)).1
  have hcur : ∀ u, a ≤ HeckeDetectorZeros.zeroMaximum (χ u) (hχ u) ((3*i : ℕ)*Z^τ) :=
    fun u => (hguard _ (hsel u) (hχ u)).2
  have hmod : ∀ u j, ((χ u j).modulus.absNorm : ℝ) ≤ Z^q := fun u j => hcond _ (hsel u) j
  -- the rescaled slots
  set Qc : FreeRow → Slot → ℂ := coreSlot rayM H hH η η₀ W (Z^q) θ (fun s => w s / q) σ v t
    with hQcdef
  set Q : FreeRow → Slot → ℂ := fun u s => ((A⁻¹ : ℝ) : ℂ) * Qc u s with hQdef
  have hwq : ∀ s ∈ slots, 0 < w s / q := fun s hs => div_pos (hwmin.trans_le (hw s hs)) hq0
  have hscale : ∀ s, (Z^q)^(w s / q) = Z^(w s) := fun s => scale_rescale hZ0 hq0
  have hQenv : ∀ u ∈ rows, ∀ s ∈ slots,
      ‖Q u s‖ ≤ ((Z^q)^(w s / q))^((2*a-1)/2 + bw) := by
    intro u hu s hs
    have hb := hQ u hu s hs
    have hn : ‖Q u s‖ = A⁻¹ * ‖Qc u s‖ := by
      simp only [hQdef, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hA0)]
    rw [hn, hscale s]
    have h1 : A⁻¹ * ‖Qc u s‖ ≤ (Z^(w s))^((2*a-1)/2) := by
      rw [inv_mul_le_iff₀ hA0]; exact hb
    refine h1.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by linarith))
    exact Real.one_le_rpow hZ1.le (hwmin.le.trans (hw s hs))
  -- the fiber moments
  have hmom : ∀ wc ∈ cutoffs, wlo ≤ wc →
      ∀ wit : (∀ u, SupportedWitness (χ u) (Z^q) a ε (3*wc/2+1/1000000)
        (Z^τ) ((Z^q)^(τ/(2*dmax))) i),
      ∀ F : Finset FreeRow, F ⊆ rows → ∀ (j : WholeSourceIndex rayM H)
        (J' K' : Fin (dyadicLength (Z^q))),
      (∀ u ∈ F, (wit u).label = j ∧ (wit u).left = J' ∧ (wit u).right = K') →
      AnchorFiberMoments F slots χ Q (fun s => w s / q) (Z^q) a ε (3*wc/2+1/1000000) a0 a1 wc εm
        (C * (1+height)^J) height j J' K' := by
    intro wc hwc hwlo wit F hF j J' K' hfib
    have hm := (hZev q hq1).2 a ε (Z^τ) ((Z^q)^(τ/(2*dmax))) height i (by linarith) hε.le
      (by linarith) hh0 hfreq slots θ (fun s => w s / q) σ v t
      (fun s hs => (div_le_div_of_nonneg_left hwmin.le hq0 hq2).trans
        (div_le_div_of_nonneg_right (hw s hs) hq0.le))
      (fun s hs => (div_le_div_of_nonneg_right (hwm s hs) hq0.le).trans hmm)
      hσ hv rows hnorm hreg ht u0 wc hwc hwlo wit F hF j J' K' hfib (C * (1+height)^J) le_rfl
    exact hm.scale_slots (fun _ => A⁻¹) (fun _ => (inv_pos.mpr hA0).le)
      (fun _ => inv_le_one_of_one_le₀ hA)
  have hmesh0 : 0 ≤ mesh / q := div_nonneg hmesh hq0.le
  have hbatch := hZ₁ Z hZ1' q hq1 hq2 hU χ hχ rows slots Q (fun s => w s / q) a (mesh/q) bw εm
    (C * (1+height)^J) height a0 a1 k wlo (P/q) ε' i hgate ha hν hk0 hk hlo hmesh0 hbw hC' hh0
    hε' ha1 ha1' hfreq hnext hcur hmod hwq
    (fun s hs => div_le_div_of_nonneg_right (hwm s hs) hq0.le) hQenv hmom
  -- the slot rescaling
  have hprod : ∀ u, ∏ s ∈ slots, max 1 (‖Qc u s‖^2) ≤
      (A^2)^slots.card * ∏ s ∈ slots, max 1 (‖Q u s‖^2) := by
    intro u
    have h := prod_max_one_scaled slots (Qc u) A⁻¹ (inv_pos.mpr hA0)
      (inv_le_one_of_one_le₀ hA)
    have e : (A⁻¹ ^ 2)⁻¹ = A^2 := by rw [inv_pow, inv_inv]
    rw [e] at h
    exact h
  have hsum : (∑ u ∈ rows, ∏ s ∈ slots, max 1 (‖Qc u s‖^2)) ≤
      (A^2)^slots.card * ∑ u ∈ rows, ∏ s ∈ slots, max 1 (‖Q u s‖^2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun u _ => hprod u
  have hPq : (Z^q)^((2*a-1)*(P/q)) = Z^((2*a-1)*P) := by
    rw [← Real.rpow_mul hZ0.le]; congr 1; field_simp
  rw [hPq] at hbatch
  have hbin := binLabel_card_le slots ((2*a-1)/2) bw (by linarith) (by linarith) hbw
  have hdyq := hZdy q hq1
  refine core_batch_final hsum hbatch hbin hdyq (Real.rpow_nonneg hZ0.le _)
    (by positivity) (Real.rpow_nonneg hU0.le _) (Nat.cast_nonneg _) (by positivity)
    (by positivity) (pow_succ _ _) (Real.rpow_add hU0 _ _)

end
end Qrh.MarkedAnchor.High
