/- Copyright (c) 2026 Sil. Apache-2.0.
**The reference lane**: `ReferenceLaneFine D` for every step datum with the
explicit scalar gates `LaneGates D ρ`.

Proof. The finite initial-weight sum is dominated by the radial energy with a fixed majorant
(`finite_le_majorant`); the reference rectangle is the restored forward row (`rectangle_eq_row`),
which the forward `K₃` expansion (`Packet.Reduce.forward_dom`) dominates by canonical native
leaves at shortened lengths; every leaf has one factor of length `≤ Z^lref`, and is paid by the
parent `G(.99, 49/20, .14)` (`parent_source`, restricted from PR103's proved source) either
directly (long `log_Z`-length `≤ 1/2`) or after natural reflection of the long factor
(`leaf_core`). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Reference.LeafCore
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Reference.Rect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Reference
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic ConcreteTraceCRT
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion CenteredMomentLattice
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalRowSource
open CenteredMomentUncenteredTerminal
open QuadraticInitialBound
open CenteredMomentPrimeSlot (primePool)
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open QRH.SilDensitySplit.CubeFree.FP
open ReferencePrimeEnclosure NativeMaskedEnergy RestoredRootDictionary RestoredInitialSource
open MixedFirstReferenceEnergy
open Qrh.MarkedAnchor.Ordinary Qrh.MarkedAnchor.Ordinary.FP
open RestoredRootEnergy RecenteredRootRows RecenteredRootSetup
open Candidate.FourthPower KernelCollisionEnergy NativeFiniteHoles
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-- **The scalar gates of the lane** (checked per stage):
the short side `lref`, the half-length reflected side and the marked capacity fit in the parent
face `G(.99, 49/20, .14)` with reserve `ρ`. -/
structure LaneGates (D : StepData) (ρ : ℝ) : Prop where
  reserve : 0 < ρ
  lref_nonneg : 0 ≤ D.lref
  c_nonneg : 0 ≤ D.c
  half : D.lref + 1/2 + Lref*D.c + ρ ≤ Bref
  cap : D.c ≤ cref
  lref_c : D.lref + D.c ≤ 1

theorem eventually_log_le (e : ℝ) (he : 0 < e) : ∀ᶠ Z : ℝ in atTop, 1 + 6*Real.log Z ≤ Z^e := by
  have h1 := (isLittleO_log_rpow_atTop he).bound (show (0:ℝ) < 1/12 by norm_num)
  have h2 : ∀ᶠ Z : ℝ in atTop, 2 ≤ Z^e := (tendsto_rpow_atTop he).eventually_ge_atTop 2
  filter_upwards [h1, h2, eventually_gt_atTop (1:ℝ)] with Z h1 h2 h3
  have hl : 0 ≤ Real.log Z := Real.log_nonneg h3.le
  have hp : 0 ≤ Z^e := by linarith
  rw [Real.norm_of_nonneg hl, Real.norm_of_nonneg hp] at h1
  linarith

theorem radialEnergy_congr_keep (F G : O → ℂ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (h : ∀ z, keep z → F z = G z) : radialEnergy F keep Φ K = radialEnergy G keep Φ K := by
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hk : keep z
  · simp only [hk, ite_true, h z hk]
  · simp only [hk, ite_false]

section
variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Id) [NeZero M]
local instance instFiniteQuotLane : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [Fintype α] [DecidableEq α] in
theorem nativeLeaf_swap (W : ℝ → ℂ) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (Z : ℝ) (w σ freq : α → ℝ) (t : ℝ) (η : Character) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ : ℝ) (A : Finset α) (X₁ X₂ : ℝ) :
    nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₁ W₂ t₁ t₂ A X₁ X₂ =
      nativeLeaf M H hH W η₀ θ Z w σ freq t η keep Φ K W₂ W₁ t₂ t₁ A X₂ X₁ := by
  unfold nativeLeaf leafEnergy leafRow
  apply congrArg (fun F => radialEnergy F keep Φ K)
  funext z
  ring

end

set_option maxHeartbeats 4000000 in
/-- **The reference energy in source form** for every step datum with the lane gates. -/
theorem reference_energy_fine {D : StepData} {ρ : ℝ} (G : LaneGates D ρ)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) : ReferenceEnergyFine D := by
  intro ε hε
  have hεP : 0 < ε/4 := by positivity
  obtain ⟨meshP, hmP, hPsrc⟩ := parent_source hβ (ε/4) hεP
  refine ⟨min meshP 1, lt_min hmP one_pos, ?_⟩
  intro M _ H hH α _ W hW hWs Lcap hLcap bΦ hbΦ η η₀ Q₀ _ hQt hQ72 hQM hQη
  classical
  have hρ := G.reserve
  have hL : (0:ℝ) ≤ Lref := by norm_num [Lref]
  have hρ1 : ρ ≤ 1 := by
    have h1 := G.half; have h2 := mul_nonneg hL G.c_nonneg; have h3 := G.lref_nonneg
    simp only [Bref] at h1; linarith
  -- the majorant
  have hbΦ0 : 0 < bΦ := by linarith
  set Ψ := majorant bΦ hbΦ0 with hΨdef
  set bΨ := max 2 (majorantScale*bΦ) with hbΨdef
  have hΨs : Function.support (Ψ:ℝ → ℂ) ⊆ Iic bΨ :=
    (majorant_support bΦ hbΦ0).trans (Iic_subset_Iic.mpr (le_max_right _ _))
  have hΨ : ∀ x, 0 ≤ (Ψ x).re := majorant_nonneg bΦ hbΦ0
  have hbΨ : 2 ≤ bΨ := le_max_left _ _
  have hbΨ0 : 0 < bΨ := by linarith
  have hQ₀ : internalQ Q₀ η₀ = Q₀ := inf_eq_left.mpr hQη
  -- the parent
  obtain ⟨dP, SP, CP, hCP, hPev⟩ := hPsrc α M H hH W hW hWs bΨ hbΨ η η₀ Q₀ hQM
    (by rw [hQ₀]; exact NeZero.ne Q₀) (by rw [hQ₀]; exact hQt) (by rw [hQ₀]; exact hQ72)
  -- the reflected-child control
  obtain ⟨nC, TC, DC, hDC, hctl⟩ := CenteredMomentEnergyReferenceLowControl.reflected_child_control
    (1/4) (9/4) (by norm_num) le_rfl (by norm_num) SP dP
  -- the natural reflection
  set δ := ρ/4 with hδdef
  set xi := ρ/4 with hxidef
  set epsR := min (ε/32) (1/4) with hepsRdef
  have hδ : 0 < δ := by positivity
  have hxi : 0 < xi := by positivity
  have hepsR : 0 < epsR := lt_min (by positivity) (by norm_num)
  have hepsR2 : epsR ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hepsRε : epsR ≤ ε/32 := min_le_left _ _
  obtain ⟨nR, SR, CR, DR, hCR, hDR, hRev⟩ := reflection_eventually bΨ epsR xi hbΨ0 hepsR hxi nC
  -- the discarded tail
  obtain ⟨Cerr, hCerr, herr⟩ := CenteredMomentEnergyReferenceLowError.relative_slot_error
    (Finset.univ : Finset α) W 1 2 (33/50) (33/50) (9/4) one_pos hWs hW.continuous
  -- the direct control
  obtain ⟨nD, TD, CD, hCD, hnp⟩ := normPowerProfile_source_control (1/4) (9/4) (by norm_num) SP
  -- the forward K₃ domination, uniform over the finitely many row types
  choose Cf hCf hfwd using fun x : (Σ r : Setoid α, Finset {q // singletonBlock r q}) =>
    forward_dom M H hH (α := ↥(remainingSet x.1 x.2)) (2*Fintype.card α) W (1/4) (9/4) 3 1 Lcap
      16 0 (ε/4) (33/50) (33/50) hWs hW (by norm_num) (by norm_num) (by norm_num) (by linarith)
      (by norm_num) le_rfl (by norm_num) (by linarith) hεP
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, ∀ x, Cf x ≤ Cm := by
    obtain ⟨B, hB⟩ := (Set.finite_range Cf).bddAbove
    exact ⟨B, fun x => hB ⟨x, rfl⟩⟩
  set dg := diagonalControl Ψ with hdg_def
  have hdg : 0 ≤ dg := diagonalControl_nonneg Ψ
  set Kt := Ktot CP CR DR DC CD Cerr dg with hKt_def
  have hKt : 0 ≤ Kt := by
    rw [hKt_def]; unfold Ktot
    have := hCP.le; have := hCR.le; have := hDR.le; have := hDC.le; have := hCD.le
    positivity
  set control : Finset (ℕ×ℕ) := SR ∪ TC ∪ TD ∪ {((0:ℕ),(0:ℕ))} with hcontrol
  set J := dP+2*nC+2*nR+4*nD with hJ
  refine ⟨J, control, max Cm 1*Kt+1, by positivity, ?_⟩
  have hηev : ∀ᶠ Z : ℝ in atTop, (η.modulus.absNorm:ℝ) ≤ Z^δ :=
    (tendsto_rpow_atTop hδ).eventually_ge_atTop _
  filter_upwards [hPev, hRev, hηev, eventually_ge_atTop ((fixedConductorFactor:ℝ)*bΨ),
    eventually_log_le epsR hepsR, eventually_ge_atTop (5:ℝ)] with Z hPZ hRZ hηZ hcondZ hlogZ hZ5
  have hZ1 : 1 < Z := by linarith
  refine ⟨hZ1, ?_⟩
  intro s hsZ hsW hsL hsη hmesh V hV hv hn₁ hn₂ _ _ X Y hX hY hXY hXU hYU hshort Q hQ Φ hΦs _ rows
  subst hsZ hsW hsL hsη
  have hZ0 : 0 < s.Z := zero_lt_one.trans hZ1
  -- (a) the majorant
  have hmaj := finite_le_majorant
    (fun z => Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootRows.rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y)
    η s.η₀ Q Q₀ hQ Φ bΦ hbΦ0 hΦs s.Z hZ0 rows
  refine hmaj.trans ?_
  -- (b) the rectangle is the forward row
  let x : (Σ r : Setoid α, Finset {q // singletonBlock r q}) := ⟨s.r, s.A⟩
  have hrow := radialEnergy_congr_keep
    (fun z => Qrh.MarkedAnchor.Ordinary.FP.RecenteredRootRows.rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) X Y)
    (fun z => QRH.SilDensitySplit.CubeFree.FP.RestorationFamily.row false (enclosure (16*s.Z^s.Lcap))
        ((naturalCharacter η z).excludePrimes ∅ empty_primes)
        (fun i : remainingSet s.r s.A => supportedPool (primePool M H 2 (s.Z^(s.w i.val))))
        (fun i => heightCoefficient (holeCoefficient
          (slotBeta M H hH s.W s.η₀ (fun i : remainingSet s.r s.A => s.θ i.val) s.Z
            (fun i => s.w i.val) (fun _ => 33/50) (fun i => s.v i.val))
          (fun _ => restorationHoles s.r (primeEnclosure s.Z) s.tc s.A s.ti) i) s.t)
        (fun i => s.Z^(s.w i.val))
        (phaseProfile (s.p.profile 0) (s.t/(2*Real.pi)))
        (phaseProfile (s.p.profile 1) (s.t/(2*Real.pi))) (9/4) X Y)
    (initialKeep η Q₀) Ψ s.Z
    (fun z hz => rectangle_eq_row M H hH s hn₁ hn₂ η z hz.1 X Y hX hY hXU hYU)
  rw [hrow]
  -- (c) the forward domination
  set K2 := (sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2 with hK2
  have hK20 : 0 ≤ K2 := by positivity
  set h := 1+|s.t|+V with hhdef
  have hh1 : 1 ≤ h := by have := abs_nonneg s.t; linarith
  set Hh := QRH.SilDensitySplit.CubeFree.FP.MixedFirstProfileEnvelope.height 0 V s.t s.t with hHh
  have hhH : h ≤ Hh := by
    rw [hhdef, hHh]; unfold QRH.SilDensitySplit.CubeFree.FP.MixedFirstProfileEnvelope.height
    rw [abs_zero, Real.norm_eq_abs]; linarith [abs_nonneg s.t]
  have hfin : 0 ≤ (max Cm 1*Kt+1)*K2*Hh^J*s.Z^(1+ε) := by
    have : 0 ≤ Hh := (zero_le_one.trans hh1).trans hhH
    positivity
  have hrc := radial_control_nonneg Φ
  by_cases hsmall : X ≤ comparisonScale (9/4) ∨ Y ≤ comparisonScale (9/4)
  · have hzero : (fun z : O => QRH.SilDensitySplit.CubeFree.FP.RestorationFamily.row false (enclosure (16*s.Z^s.Lcap))
        ((naturalCharacter η z).excludePrimes ∅ empty_primes)
        (fun i : remainingSet s.r s.A => supportedPool (primePool M H 2 (s.Z^(s.w i.val))))
        (fun i => heightCoefficient (holeCoefficient
          (slotBeta M H hH s.W s.η₀ (fun i : remainingSet s.r s.A => s.θ i.val) s.Z
            (fun i => s.w i.val) (fun _ => 33/50) (fun i => s.v i.val))
          (fun _ => restorationHoles s.r (primeEnclosure s.Z) s.tc s.A s.ti) i) s.t)
        (fun i => s.Z^(s.w i.val))
        (phaseProfile (s.p.profile 0) (s.t/(2*Real.pi)))
        (phaseProfile (s.p.profile 1) (s.t/(2*Real.pi))) (9/4) X Y) = fun _ => 0 := by
      funext z
      exact literal_row_comparison_small false _ _ _ _ _ _ _ (9/4) X Y (by norm_num) hsmall
    rw [hzero]
    have h0 : radialEnergy (fun _ : O => (0:ℂ)) (initialKeep η Q₀) Ψ s.Z = 0 := by
      unfold radialEnergy; simp
    rw [h0, mul_zero]
    exact mul_nonneg hrc hfin
  have hX' : comparisonScale (9/4:ℝ) < X := lt_of_not_ge (fun h => hsmall (Or.inl h))
  have hcs : comparisonScale (9/4:ℝ) = 2/9 := QRH.SilDensitySplit.CubeFree.FP.RestoredRootSource.comparison_value
  have hYcap : s.Y₂ ≤ s.Z := (s.rootData hn₁ hn₂).hcap₂
  have hY1cap : s.Y₁ ≤ s.Z := (s.rootData hn₁ hn₂).hcap₁
  have hXZ : X ≤ s.Z^(3:ℝ) := by
    have h1 : X ≤ s.Z := hXU.trans (show (s.rootSource hH hn₁ hn₂).U₁ ≤ s.Z from
      max_le hY1cap (by rw [hcs]; linarith))
    have h2 : s.Z ≤ s.Z^(3:ℝ) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hZ1.le (by norm_num : (1:ℝ) ≤ 3)
    exact h1.trans h2
  have hYZ : Y ≤ s.Z^(3:ℝ) := by
    have hprod : X*Y ≤ s.Z*s.Z := by
      rw [hXY]; exact mul_le_mul hY1cap hYcap s.hY₂.le hZ0.le
    have hY9 : Y ≤ (9/2)*(s.Z*s.Z) := by
      rw [hcs] at hX'
      have : (2/9)*Y ≤ X*Y := mul_le_mul_of_nonneg_right hX'.le hY.le
      nlinarith
    have h3 : s.Z^(3:ℝ) = s.Z*s.Z*s.Z := by norm_num [Real.rpow_natCast, pow_succ, pow_two]
    rw [h3]
    have : (9/2)*(s.Z*s.Z) ≤ s.Z*s.Z*s.Z := by nlinarith [mul_pos hZ0 hZ0]
    linarith
  have hfd := hfwd x s.Z hZ1.le s.η₀ (fun i : remainingSet s.r s.A => s.θ i.val)
    (fun i => s.w i.val) (fun _ => 33/50) (fun i => s.v i.val) s.t
    (fun _ => restorationHoles s.r (primeEnclosure s.Z) s.tc s.A s.ti)
    (fun i => s.hw _) (fun i => ((hmesh _).trans (min_le_right _ _)))
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => restoration_holes_card s.r _ s.tc s.A s.ti)
    η (initialKeep η Q₀) Ψ s.Z bΨ hZ0 hΨs (fun z => hΨ _) (fun z hz => hz.1) ∅ empty_primes
    (by simp) (s.p.profile 0) (s.p.profile 1) (s.p.support 0) (s.p.support 1)
    (s.t/(2*Real.pi)) (s.t/(2*Real.pi)) X Y hX hY hXZ hYZ
  -- (d) every leaf is paid
  set E := Kt*K2*h^J*s.Z^(1+ε/4+4*epsR) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hsT : 0 ≤ ∑ i, s.w i := Finset.sum_nonneg (fun i _ => s.hw i)
  obtain ⟨hcapT, _⟩ := (globalFace_admissible_iff (length_nonneg s.Z s.X₁ hZ1)
    (length_nonneg s.Z s.X₂ hZ1) hsT s.hD.2.1).mp s.hface
  rw [mul_one] at hcapT
  have hgate : D.lref + (1/2+δ+xi) + Lref*D.c ≤ Bref := by have := G.half; linarith
  have htail : ∀ (A : Finset α) (Ws : 𝓢(ℝ,ℂ)), Function.support (Ws:ℝ→ℂ) ⊆ Icc (1/4) (9/4) →
      ∀ bshort : ℝ,
      radialEnergy (fun z => polynomial (naturalCharacter η z) false Ws (s.Z^bshort) 0 s.t *
          ∏ i ∈ A, naturalSlot (naturalCharacter η z) (primePool M H 2 (s.Z^(s.w i)))
            (heightCoefficient (slotBeta M H hH s.W s.η₀ s.θ s.Z s.w (fun _ => 33/50) s.v i) s.t)
            (s.Z^(s.w i)))
        (initialKeep η Q₀) Ψ s.Z ≤
        Cerr*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) Ws)^2*diagonalControl Ψ*max 1 s.Z*s.Z^bshort*
          ∏ i ∈ A, s.Z^(s.w i) :=
    fun A Ws hs bshort => herr A (Finset.subset_univ _) Ws (fun x hx => (hs hx).2)
      (naturalCharacter η) (fun i => relativeCharacter M H hH s.η₀ (s.θ i))
      (fun i => primePool M H 2 (s.Z^(s.w i))) (fun i => s.Z^(s.w i)) (fun _ => 33/50) s.v s.t
      (s.Z^bshort) s.Z Ψ (initialKeep η Q₀) (Real.rpow_pos_of_pos hZ0 _) hZ0
      (fun i _ => Real.rpow_pos_of_pos hZ0 _) (fun i _ => le_rfl) (fun i _ => le_rfl)
      (fun i _ I hI => (Finset.mem_filter.mp hI).2.1) (fun z => hΨ _)
  have hleaves : ∀ (A'' : Finset (remainingSet s.r s.A)),
      ∀ pr ∈ forwardLengths (enclosure (16*s.Z^s.Lcap)) (9/4) X Y ∅,
      nativeLeaf M H hH s.W s.η₀ (fun i : remainingSet s.r s.A => s.θ i.val) s.Z
        (fun i => s.w i.val) (fun _ => 33/50) (fun i => s.v i.val) s.t η (initialKeep η Q₀) Ψ s.Z
        (s.p.profile 0) (s.p.profile 1) (2*Real.pi*(s.t/(2*Real.pi))) (2*Real.pi*(s.t/(2*Real.pi)))
        A'' pr.1 pr.2 ≤ E := by
    intro A'' pr hpr
    obtain ⟨hp1, hp1X, hp2, hp2Y⟩ := forwardLengths_below empty_primes hX hY pr hpr
    have htt : 2*Real.pi*(s.t/(2*Real.pi)) = s.t := by field_simp
    rw [htt]
    let e : (remainingSet s.r s.A) ↪ α := Function.Embedding.subtype _
    refine le_trans (le_of_eq (QRH.SilDensitySplit.CubeFree.Assembly.nativeLeaf_map M H hH e s.W
      s.η₀ s.θ s.Z s.w (fun _ => 33/50) s.v s.t η (initialKeep η Q₀) Ψ s.Z
      (s.p.profile 0) (s.p.profile 1) s.t s.t A'' pr.1 pr.2)) ?_
    have hA : ∑ i ∈ A''.map e, s.w i ≤ D.c :=
      (Finset.sum_le_univ_sum_of_nonneg (fun i => s.hw i)).trans (by simpa using hcapT)
    rcases hshort with hs1 | hs2
    · rw [nativeLeaf_swap M H hH]
      have hb := leaf_core M H hH s.W η s.η₀ Q₀ hQ₀ Ψ bΨ hΨs hΨ meshP (ε/4) hεP.le dP SP CP s.Z δ
        hCP.le hZ1 hδ.le (by linarith) hηZ hPZ nC TC DC hDC.le hctl epsR xi hepsR.le hepsR2 hxi.le
        (by linarith) nR SR CR DR hCR.le hDR.le hRZ.2 nD TD CD hCD.le hnp control
        (by intro a ha; simp [hcontrol, ha]) (by intro a ha; simp [hcontrol, ha])
        (by intro a ha; simp [hcontrol, ha]) (by simp [hcontrol])
        s.θ s.w (fun _ => 33/50) s.v s.t V s.hw (fun i => (hmesh i).trans (min_le_left _ _))
        (fun _ => rfl) hV hv Cerr hCerr.le htail D.lref D.c G.lref_nonneg hgate G.cap G.lref_c
        hcondZ hbΨ0.le hlogZ (s.p.profile 1) (s.p.profile 0) (s.p.support 1) (s.p.support 0)
        (A''.map e) hA pr.2 pr.1 hp2 hp1 (hp1X.trans hs1)
      refine hb.trans (le_of_eq ?_)
      rw [hEdef, hK2]; ring
    · exact leaf_core M H hH s.W η s.η₀ Q₀ hQ₀ Ψ bΨ hΨs hΨ meshP (ε/4) hεP.le dP SP CP s.Z δ
        hCP.le hZ1 hδ.le (by linarith) hηZ hPZ nC TC DC hDC.le hctl epsR xi hepsR.le hepsR2 hxi.le
        (by linarith) nR SR CR DR hCR.le hDR.le hRZ.2 nD TD CD hCD.le hnp control
        (by intro a ha; simp [hcontrol, ha]) (by intro a ha; simp [hcontrol, ha])
        (by intro a ha; simp [hcontrol, ha]) (by simp [hcontrol])
        s.θ s.w (fun _ => 33/50) s.v s.t V s.hw (fun i => (hmesh i).trans (min_le_left _ _))
        (fun _ => rfl) hV hv Cerr hCerr.le htail D.lref D.c G.lref_nonneg hgate G.cap G.lref_c
        hcondZ hbΨ0.le hlogZ (s.p.profile 0) (s.p.profile 1) (s.p.support 0) (s.p.support 1)
        (A''.map e) hA pr.1 pr.2 hp1 hp2 (hp2Y.trans hs2)
  have hdom := hfd E hE0 hleaves
  -- (e) the constants
  refine mul_le_mul_of_nonneg_left (hdom.trans ?_) hrc
  have hCfx : Cf x ≤ max Cm 1 := (hCm x).trans (le_max_left _ _)
  have hCf0 : 0 ≤ Cf x := (hCf x).le
  have hZe : s.Z^(ε/4)*s.Z^(1+ε/4+4*epsR) ≤ s.Z^(1+ε) := by
    rw [← Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have hhJ : h^J ≤ Hh^J := pow_le_pow_left₀ (zero_le_one.trans hh1) hhH J
  have hZa : 0 ≤ s.Z^(ε/4) := Real.rpow_nonneg hZ0.le _
  have hZb : 0 ≤ s.Z^(1+ε/4+4*epsR) := Real.rpow_nonneg hZ0.le _
  have hhJ0 : 0 ≤ h^J := pow_nonneg (zero_le_one.trans hh1) J
  have hHh0 : 0 ≤ Hh := (zero_le_one.trans hh1).trans hhH
  calc Cf x*s.Z^(ε/4)*E = Cf x*Kt*K2*h^J*(s.Z^(ε/4)*s.Z^(1+ε/4+4*epsR)) := by rw [hEdef]; ring
    _ ≤ max Cm 1*Kt*K2*Hh^J*s.Z^(1+ε) := by
        gcongr
    _ ≤ (max Cm 1*Kt+1)*K2*Hh^J*s.Z^(1+ε) := by
        have : 0 ≤ K2*Hh^J*s.Z^(1+ε) := by
          have : 0 ≤ Hh := (zero_le_one.trans hh1).trans hhH
          positivity
        nlinarith

/-- **The reference lane**, in source form. -/
theorem reference_lane_fine {D : StepData} {ρ : ℝ} (G : LaneGates D ρ) : ReferenceLaneFine D :=
  fun hβ => reference_energy_fine G hβ

end
end Qrh.MarkedAnchor.Ordinary.Reference
