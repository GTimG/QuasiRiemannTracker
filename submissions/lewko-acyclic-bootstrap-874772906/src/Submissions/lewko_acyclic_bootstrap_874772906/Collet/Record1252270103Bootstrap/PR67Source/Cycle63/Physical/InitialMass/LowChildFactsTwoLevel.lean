import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildSelectedFacts
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildFactsRow
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildFactsCount
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildScale
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondEncodedGates
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalCapacity.UniformPadding
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.LowBranch.TwoLevelBridge
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The facts of the first level that pay the returned HIGH parts of row 5, for the first step of the two-level ledger:
the coordinates of the rows, the prefix count, the first-level payment of the coordinates with the uniform shift of the
side of the labels, the energy scale of the child, the reserve data and the margin. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
open CenteredMomentEnergyInputParentCapacity CenteredMomentSecondCanonicalNonunit CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplificationChildSourceCaps

variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

attribute [local instance] lowChildSelectedDecidable

/-- The multiplier of a child prefix is not zero when the first label and the second pair are supported, the fixed row
is not zero and the factors of the first label are units. -/
theorem child_multiplier_ne_zero (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O) (hu₀ : u₀ ≠ 0)
    (hunit : ∀ l, IsUnit (unit l)) (p : ChildPrefix) (hC : Supported p.1.1.1) (hC₂ : Supported p.2.1.1) :
    childMultiplier left u₀ unit p ≠ 0 := by
  unfold childMultiplier
  have hS : primeSubsetGenerator (fun P : CommonIndex p.1.1.1 p.1.1.2 => P.val) p.1.2.val ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mp (subsetGenerator_supported _ _ hC p.1.2.val).1
  have hF := first_source_numerator_ne_zero left p.1 hC
  have hG := CenteredMomentSecondCanonicalFrequency.commonFrequencyGenerator_ne_zero p.2.1.1 p.2.1.2 hC₂
  have hV := nonunitFrequencyGenerator_ne_zero p.2.1.1 p.2.1.2 hC₂ p.2.2
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hu₀ (hunit p.1).ne_zero) hS) hF) (mul_ne_zero hG hV)

/-- The logarithm to the base `Z` of a fixed positive real is eventually at most any positive bound. -/
theorem eventually_logb_le {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ Real.logb Z x ≤ c := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), (tendsto_rpow_atTop hc).eventually_ge_atTop x] with Z hZ hZc
  exact ⟨hZ, (Real.logb_le_iff_le_rpow hZ hx).mpr hZc⟩


/-- The support padding of the slots is not negative. -/
theorem facts_support_padding_nonneg (n : ℕ) (bs b₁ b₂ Z : ℝ) (hZ : 1 < Z) (hbs : 1 ≤ bs) :
    0 ≤ supportPadding n bs b₁ b₂ Z := by
  unfold supportPadding
  have h1 : 0 ≤ Real.logb Z bs := Real.logb_nonneg hZ hbs
  have h2 : 0 ≤ Real.logb Z (max 1 b₁ * max 1 b₂) :=
    Real.logb_nonneg hZ (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
  have h3 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg n)) h1
  linarith only [h2, h3]

/-- The density and the amplifier cost in a bin of the second step: the density lies in `[2/7, 1]` and the cost of the
amplifier is at most `23/7`. -/
theorem facts_density_bounds {δ : ℝ} (h1 : Cycle63.Optimization.secondJunction ≤ δ) (h2 : δ ≤ 3 / 4) :
    0 < δ ∧ Cycle63.Optimization.density δ ≤ 1 ∧ Cycle63.Optimization.amplifierCost δ ≤ 23 / 7 := by
  have hq0 : Cycle63.Arithmetic.q0 ≤ δ := by
    have h1' := Cycle63.Arithmetic.q0_bounds
    have h2' := Cycle63.Optimization.secondJunction_mem
    linarith [h1'.2, h2'.1, h1]
  obtain ⟨hρlo, hρhi, -⟩ := Cycle63.Physical.high_density_bounds ⟨hq0, h2⟩
  have hr := Cycle63.Arithmetic.rho0_bounds
  have hd : Cycle63.Optimization.density δ = LocalMoment.unmarkedDensity δ := rfl
  have hq := Cycle63.Arithmetic.q0_bounds
  refine ⟨by linarith [hq.1], ?_, ?_⟩
  · rw [hd]
    linarith [hr.2]
  · unfold Cycle63.Optimization.amplifierCost
    rw [hd]
    linarith

attribute [local irreducible] actualSecondLabels

set_option linter.unusedVariables false in
/-- The facts of the first level that pay the returned HIGH parts of row 5, for the first step of the two-level ledger.

The coordinates of the rows, the prefix count of the rows over one multiplier ideal, the first-level payment of the
coordinates with the uniform shift `p + exponent - log N(seed₀)` of the side of the labels, the energy scale of the
child, the reserve data of the pair (`m₁ = 1`, `A₁ = log (volume s)`, `a₁ = amp`, `γ₁ = 0`) and the margin of the
ledger hold. The witnesses are:
`small₁ = omega + ε + max (1 - Mrow) 0`, `κ = log 4 + 2 card α log bs + ξ/2` (all to the base `Z`), and
`Lmax = small₁ + lossFloor + κ + (3/4) (supportPadding + gridSlack) + q mesh + (23/7) ampSlack`.
The count constants are `Capre` and `εA = margin/4`, where `margin` is the difference of the two sides of `hnum`.

The hypothesis `hnum` is the numeric condition of the ledger: the largest frequency loss `ωmax`, the shell slack `ε`
of the fixed row, the loss floor of the second step, three quarters of the padding and of the grid slack, and `23/7`
of the amplifier slack are below the margin `highTwoMargin` of the depth-two HIGH rows less the LOW reserve, plus the
slacks `εwidth/2`, `εold`, `εlabels/2` and `lowRate εpad` of the row. -/
theorem lowReturnedFacts_two_level [Led : Cycle63.AffineLedger] [IsTwoLevelFirstStep Led] {α : Type} [Fintype α]
    [DecidableEq α]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs supply εv Bnorm εlabels ωmax : ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (lossFloor gridSlack ampSlack : ℝ)
    (hε : 0 < ε) (hbs : 1 ≤ bs) (hMcap : 0 < Mcap) (hBnorm : 0 ≤ Bnorm)
    (hew : 0 ≤ εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin) (hεold : 0 ≤ εold) (hel : 0 ≤ εlabels)
    (hgrid : 0 ≤ gridSlack) (hamp : 0 ≤ ampSlack)
    (hnum : ωmax + ε + lossFloor + 3 / 4 * (εpad + gridSlack) + 23 / 7 * ampSlack <
      Cycle63.Optimization.highTwoMargin - Cycle63.AffineLedger.lowReserve + εwidth / 2 + εold + εlabels / 2 +
        Cycle63.AffineLedger.lowRate * εpad) :
    LowReturnedFactsStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell N Cs supply εv Bnorm εlabels (fun u om _ => u=1 ∧ om≤ωmax) lowSideExponent Presented lossFloor
      gridSlack ampSlack := by
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨margin, hmargin⟩ : ∃ margin : ℝ, margin =
      Cycle63.Optimization.highTwoMargin - Cycle63.AffineLedger.lowReserve + εwidth / 2 + εold + εlabels / 2 +
        Cycle63.AffineLedger.lowRate * εpad - (ωmax + ε + lossFloor + 3 / 4 * (εpad + gridSlack) + 23 / 7 * ampSlack) :=
    ⟨_, rfl⟩
  have hmpos : 0 < margin := by rw [hmargin]; linarith only [hnum]
  have hcpos : 0 < min (margin / 4) 1 := lt_min (by positivity) one_pos
  obtain ⟨Capre, hCapre, hcount⟩ := facts_rows_over_ideal.{0, 0} (α := α)
    (Mcap + 5 * Bnorm + ε + 1 + Bnorm) (margin / 4) (by positivity) (by positivity)
  refine ⟨Capre, margin / 4, hCapre, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    support_padding_eventually_mass (Fintype.card α) bs b b εpad Mmin (zero_lt_one.trans_le hbs) hep hmin,
    eventually_logb_le (x := (4 : ℝ)) (by norm_num) (half_pos hcpos),
    eventually_logb_le (x := bs) (zero_lt_one.trans_le hbs)
      (show 0 < min (margin / 4) 1 / (4 * ((N : ℝ) + 1)) by positivity)]
    with Z hZ2 hpad hlog4 hlogbs
  refine ⟨hZ2, ?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin hAdm hω hξ hMcap' hfit hzslot haff Label _ reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    childSrc R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed hfirstproj hfirstnorm hrad hgeom hfirstshell rows hU box hbox label cell amp q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq hRadius hωeq χ hP hPN st src divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps left₁ u₀ unit₁ Tz hleft hu₀ hdict mult hpres
  obtain ⟨hunit, hωmax⟩ := hAdm
  subst hunit
  subst hleft
  have hZ0 : 0 < Z := zero_lt_one.trans hZone
  -- the volume and the amplifier of the cell of the parent
  have hM1 : (0 : ℝ) < 1 := one_pos
  obtain ⟨-, -, -, htot, hampos⟩ := Cycle63.AffineLedger.normalized_cell_bounds hM1 hzslot haff
  have hvol : Real.logb Z (volume s) ≤ Cycle63.AffineLedger.totalA cell := by
    rw [input_volume_log]
    have h1 := raw_log_le_length Z s.X₁ hZone s.X₁_pos
    have h2 := raw_log_le_length Z s.X₂ hZone s.X₂_pos
    simp only [one_mul] at htot
    linarith only [h1, h2, htot]
  have hA₁ : Real.logb Z (volume s) ≤ Cycle63.Optimization.twoLevelTotalA cell := by
    rw [← totalA_eq cell]
    exact hvol
  have hamp_eq : amp = Cycle63.Optimization.firstAmp cell := by
    show 1 * Cycle63.AffineLedger.amp cell = _
    rw [one_mul, amp_eq]
  have hamp0 : 0 ≤ amp := by
    show 0 ≤ 1 * Cycle63.AffineLedger.amp cell
    exact hampos.le
  -- the gates of the labels of the rows
  have hlab : ∀ r : rows, label r ∈ actualSecondLabels (childSrc r.val.1) (R r.val.1) (seed r.val.1) := fun r =>
    actual_second_supported_label_mem (childSrc r.val.1) (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ
      r.val.2 (hU r.val r.property)
  have hgate := fun r : rows => actual_second_labels_gates (childSrc r.val.1) (R r.val.1) (seed r.val.1)
    (hseed r.val.1) (hw₁ r.val.1) (hw₂ r.val.1) (label r) (hlab r)
  -- the multipliers of the rows
  have hmult0 : ∀ r : rows, firstRowMultiplier first (!reflected) u₀ unit₁ r.val ≠ 0 := fun r =>
    child_multiplier_ne_zero (!reflected) u₀ unit₁ hu₀ hdict.1 _ (hf r.val.1).1 (hgate r).1
  have hscale := fun r : rows => low_row_scale_le (g r) hZone (zero_lt_one.trans_le hbs) reflected (!reflected) second
    first reserve ε r.val (hU r.val r.property) (label r) rfl (hf r.val.1).1 (hf r.val.1).2 (heq r.val.1) (hRadius r)
    (hC₂ r) (hD₂ r) (hU₂ r) u₀ unit₁ hdict.1 hdict.2 (hmult0 r) ((g r).datum.τ (χ r)) (internalQ Q η₀)
    ((q r).R₂ * (q r).E₂) (hP r) (hPN r)

  have hlb4 : 0 ≤ Real.logb Z 4 := Real.logb_nonneg hZone (by norm_num)
  have hlbs : 0 ≤ Real.logb Z bs := Real.logb_nonneg hZone hbs
  have hcardN : (Fintype.card α : ℝ) ≤ N := by exact_mod_cast hcard
  -- the logarithms of the constants of the scale are small
  have hτκ : Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs ≤ min (margin / 4) 1 := by
    have hc : 0 < min (margin / 4) 1 / (4 * ((N : ℝ) + 1)) := by positivity
    have h1 : 2 * (Fintype.card α : ℝ) * Real.logb Z bs ≤ 2 * (N : ℝ) * (min (margin / 4) 1 / (4 * ((N : ℝ) + 1))) :=
      mul_le_mul (by linarith only [hcardN]) hlogbs.2 hlbs (by positivity)
    have h2 : 2 * (N : ℝ) * (min (margin / 4) 1 / (4 * ((N : ℝ) + 1))) ≤ min (margin / 4) 1 / 2 := by
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have : 2 * (N : ℝ) * (min (margin / 4) 1 / (4 * ((N : ℝ) + 1))) =
          min (margin / 4) 1 / 2 * ((N : ℝ) / ((N : ℝ) + 1)) := by
        field_simp
        ring
      rw [this]
      have hle : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      calc min (margin / 4) 1 / 2 * ((N : ℝ) / ((N : ℝ) + 1)) ≤ min (margin / 4) 1 / 2 * 1 :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = _ := mul_one _
    linarith only [h1, h2, hlog4.2]
  have hτκ1 : Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs ≤ 1 := hτκ.trans (min_le_right _ _)
  have hτκ4 : Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs ≤ margin / 4 := hτκ.trans (min_le_left _ _)
  have hκ0 : 0 ≤ Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs + ξ / 2 := by
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (Fintype.card α))) hlbs
    linarith only [hlb4, this, hξ]
  -- the row width of the parent and the bound of the norms
  have hmod0 : 0 ≤ Real.logb Z (s.η.modulus.absNorm : ℝ) := Real.logb_nonneg hZone (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr s.η.modulus_ne_bot))
  have hMrow : Mrow ≤ 1 + εwidth / 2 := by linarith only [hfit, hmod0]
  have hξ2 : ξ / 2 ≤ Mcap - 1 - εwidth := by linarith only [hMcap']
  have hlogN : ∀ r : rows, Real.logb Z (((first r.val.1).1.1.absNorm : ℕ) : ℝ) ≤ Bnorm := fun r =>
    (Real.logb_le_iff_le_rpow hZone (CenteredMomentFirstScale.norm_pos _ (hf r.val.1).1.1)).mpr (hfirstnorm r.val.1).1
  have hX2 : ∀ r : rows, actualHighCoordinates reflected (!reflected) second (first r.val.1) (label r).1.1
      (label r).1.2 (label r).2.val Z Mrow (Real.logb Z (volume s)) amp ξ reserve ε 2 ≤ Mrow + 5 * Bnorm + ε := by
    intro r
    have hx2 : actualHighCoordinates reflected (!reflected) second (first r.val.1) (label r).1.1 (label r).1.2
        (label r).2.val Z Mrow (Real.logb Z (volume s)) amp ξ reserve ε 2 =
        Mrow - Real.logb Z ((Ideal.span {activeConductor (first r.val.1).1.1 (first r.val.1).1.2}).absNorm : ℝ) -
          max (Real.logb Z ((if reflected then (first r.val.1).1.2 else (first r.val.1).1.1).absNorm : ℝ) -
            Real.logb Z ((if reflected then (first r.val.1).1.1 else (first r.val.1).1.2).absNorm : ℝ)) 0 +
          Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) (first r.val.1)}).absNorm : ℝ) - 6 * amp -
          (frequencyLoss Z 32 ξ + reserve) + ε := rfl
    have hR0 : 0 ≤ Real.logb Z ((Ideal.span {activeConductor (first r.val.1).1.1 (first r.val.1).1.2}).absNorm : ℝ) :=
      Real.logb_nonneg hZone (norm_ge_one _ (activeConductor_supported _ _ (hf r.val.1).1).1)
    have hLc : Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) (first r.val.1)}).absNorm : ℝ) ≤
        5 * Bnorm := by
      have h := first_numerator_log_le (!reflected) (first r.val.1) (hf r.val.1).1 (hf r.val.1).2 Z hZone
      have h' : Real.logb Z ((Ideal.span {firstSourceNumerator (!reflected) (first r.val.1)}).absNorm : ℝ) ≤
          5 * Real.logb Z ((first r.val.1).1.1.absNorm : ℝ) := h
      linarith only [h', hlogN r]
    have hmax0 : 0 ≤ max (Real.logb Z ((if reflected then (first r.val.1).1.2 else (first r.val.1).1.1).absNorm : ℝ) -
        Real.logb Z ((if reflected then (first r.val.1).1.1 else (first r.val.1).1.2).absNorm : ℝ)) 0 :=
      le_max_right _ _
    rw [hx2]
    have hω' : 0 ≤ frequencyLoss Z 32 ξ + reserve := hωeq ▸ hω
    linarith only [hR0, hLc, hmax0, hω', hamp0]
  have hmultB : ∀ r : rows,
      Real.logb Z ((Ideal.span {firstRowMultiplier first (!reflected) u₀ unit₁ r.val}).absNorm : ℝ) ≤
        Mcap + 5 * Bnorm + ε + 1 := by
    intro r
    have h5 := hscale r
    have hrw := (retainedState Z Bmask hZone ((g r).datum.τ (χ r)) (internalQ Q η₀) ((q r).R₂ * (q r).E₂) (hP r)
      (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive).row_nonneg
    linarith only [h5, hrw, hX2 r, hMrow, hξ2, hτκ1, hew]
  have hB₂ : Z ^ Bnorm ≤ Z ^ (Mcap + 5 * Bnorm + ε + 1 + Bnorm) :=
    Real.rpow_le_rpow_of_exponent_le hZone.le (by linarith only [hMcap, hBnorm, hε])
  have hfg : ∀ r ∈ rows, Supported (first r.1).1.1 ∧ Supported (first r.1).1.2 ∧
      primeSupport (first r.1).1.1 = primeSupport (first r.1).1.2 ∧
      ((first r.1).1.1.absNorm : ℝ) ≤ Z ^ (Mcap + 5 * Bnorm + ε + 1 + Bnorm) ∧
      ((first r.1).1.2.absNorm : ℝ) ≤ Z ^ (Mcap + 5 * Bnorm + ε + 1 + Bnorm) := fun r _ =>
    ⟨(hf r.1).1, (hf r.1).2, heq r.1, (hfirstnorm r.1).1.trans hB₂, (hfirstnorm r.1).2.trans hB₂⟩
  have hsg : ∀ r ∈ rows, Supported r.2.1.val.val.1 ∧ Supported r.2.1.val.val.2 ∧
      primeSupport r.2.1.val.val.1 = primeSupport r.2.1.val.val.2 ∧
      (r.2.1.val.val.1.absNorm : ℝ) ≤ Z ^ (Mcap + 5 * Bnorm + ε + 1 + Bnorm) ∧
      (r.2.1.val.val.2.absNorm : ℝ) ≤ Z ^ (Mcap + 5 * Bnorm + ε + 1 + Bnorm) := by
    intro r hr
    have hg := hgate ⟨r, hr⟩
    exact ⟨hg.1, hg.2.1, hg.2.2.1, (hg.2.2.2.2.2.1.trans (hsource r.1)).trans hB₂,
      (hg.2.2.2.2.2.2.trans (hsource r.1)).trans hB₂⟩
  have hmultR : ∀ r ∈ rows, firstRowMultiplier first (!reflected) u₀ unit₁ r ≠ 0 ∧
      ((Ideal.span {firstRowMultiplier first (!reflected) u₀ unit₁ r} *
        firstSourceMissing (!reflected) (first r.1)).absNorm : ℝ) ≤ Z ^ (Mcap + 5 * Bnorm + ε + 1 + Bnorm) := by
    intro r hr
    refine ⟨hmult0 ⟨r, hr⟩, ?_⟩
    have hposN : (0 : ℝ) < ((Ideal.span {firstRowMultiplier first (!reflected) u₀ unit₁ r}).absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (hmult0 ⟨r, hr⟩)))
    have hN1 : ((Ideal.span {firstRowMultiplier first (!reflected) u₀ unit₁ r}).absNorm : ℝ) ≤
        Z ^ (Mcap + 5 * Bnorm + ε + 1) := (Real.logb_le_iff_le_rpow hZone hposN).mp (hmultB ⟨r, hr⟩)
    have hmiss : ((firstSourceMissing (!reflected) (first r.1)).absNorm : ℝ) ≤ Z ^ Bnorm :=
      (Nat.cast_le.mpr (first_missing_norm_le (!reflected) (first r.1) (hf r.1).1 (hf r.1).2).2.1).trans
        (hfirstnorm r.1).1
    rw [map_mul, Nat.cast_mul, Real.rpow_add hZ0]
    exact mul_le_mul hN1 hmiss (Nat.cast_nonneg _) (Real.rpow_nonneg hZ0.le _)
  have hF2 : ∀ (cap : ℝ) (D : Ideal O), (((Finset.univ : Finset rows).filter (fun r : rows =>
      (Real.logb Z ((firstSourceMissing (!reflected) (first r.val.1)).absNorm : ℝ) ≤ cap) ∧
      (Ideal.span {firstRowMultiplier first (!reflected) u₀ unit₁ r.val} = D))).card : ℝ) ≤
      Capre * (box.card : ℝ) * Z ^ (margin / 4) * Z ^ cap := by
    intro cap D
    have h := hcount Z hZ2 (fun l => liveIndices (alloc l).val) childSrc R seed hseed hw₁ hw₂ K Tsec ξ first hinj
      (!reflected) u₀ unit₁ rows box hbox hfg hsg hmultR cap D
    have hEq := card_univ_filter_subtype rows (fun r =>
      Real.logb Z ((firstSourceMissing (!reflected) (first r.1)).absNorm : ℝ) ≤ cap ∧
        Ideal.span {firstRowMultiplier first (!reflected) u₀ unit₁ r} = D)
    rw [hEq]
    exact h
  refine ⟨fun _ => omega + ε + max (1 - Mrow) 0, fun _ => 1, fun _ => Real.logb Z (volume s), fun _ => amp,
    fun _ => 0, Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs + ξ / 2,
    omega + ε + max (1 - Mrow) 0 + lossFloor + (Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs + ξ / 2) +
      3 / 4 * (supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z + gridSlack) + Cycle63.AffineLedger.q * mesh +
      23 / 7 * ampSlack, ?_⟩
  dsimp only
  refine ⟨?_, hF2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the missing radical
    intro r
    exact facts_missing_bounds (!reflected) (first r.val.1) (hf r.val.1).1 (hf r.val.1).2 Z Bnorm hZone
      (hfirstnorm r.val.1).1
  · -- the first-level payment of the coordinates
    intro r δ h1 h2
    have hside := lowLabelSide_le reflected Z (Real.logb Z (volume s)) p exponent (first r.val.1) hZone (hrad r.val.1)
      (hgeom r.val.1) seed₀ hs₀0 (hfirstproj r.val.1) (hf r.val.1).1
    have hω' : 0 ≤ frequencyLoss Z 32 ξ + reserve := hωeq ▸ hω
    have hrow := facts_row_payment reflected second (first r.val.1) (hf r.val.1).1 (hf r.val.1).2 (heq r.val.1)
      (label r).1.1 (label r).1.2 (hgate r).1 (hgate r).2.1 (hgate r).2.2.1 (label r).2.val Z δ Mrow
      (Real.logb Z (volume s)) amp ξ reserve ε (p + exponent - Real.logb Z (seed₀.absNorm : ℝ)) hZone ⟨h1, h2⟩
      hω' hε.le hside
    have hd : Cycle63.Optimization.density δ = LocalMoment.unmarkedDensity δ := rfl
    unfold highExponentValue at hrow
    rw [← hd, ← hωeq] at hrow
    linarith only [hrow]
  · -- the saving is not negative
    intro r
    exact le_refl 0
  · -- the energy scale of the child
    intro r
    exact hscale r
  · -- the reserve data of the pair
    intro r
    exact ⟨le_refl 1, hA₁, hamp_eq.le⟩
  · -- the losses of the second step
    intro r δ h1 h2
    obtain ⟨hδ0, hρ1, hcost⟩ := facts_density_bounds h1 h2
    have hsp0 := facts_support_padding_nonneg (Fintype.card α) bs s.b₁ s.b₂ Z hZone hbs
    have e1 : Cycle63.Optimization.density δ * (Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs + ξ / 2) ≤
        Real.logb Z 4 + 2 * (Fintype.card α : ℝ) * Real.logb Z bs + ξ / 2 := mul_le_of_le_one_left hκ0 hρ1
    have e2 : δ * (supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z + gridSlack) ≤
        3 / 4 * (supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z + gridSlack) :=
      mul_le_mul_of_nonneg_right h2 (add_nonneg hsp0 hgrid)
    have e3 : Cycle63.Optimization.amplifierCost δ * ampSlack ≤ 23 / 7 * ampSlack :=
      mul_le_mul_of_nonneg_right hcost hamp
    have e4 : Cycle63.AffineLedger.q - Cycle63.Optimization.firstJunction = 0 := by
      rw [IsTwoLevelFirstStep.q_eq (L := Led)]
      ring
    rw [e4, zero_mul]
    linarith only [e1, e2, e3]
  · -- the margin of the ledger
    have hsp : supportPadding (Fintype.card α) bs s.b₁ s.b₂ Z ≤ εpad := by
      rw [hsb₁, hsb₂]
      have h := hpad.2 1 hMmin
      linarith only [h]
    have hlr := Cycle63.AffineLedger.lowRate_mem
    have hmax : max (1 - Mrow) 0 ≤ (1 - Mrow) + εwidth / 2 :=
      max_le (by linarith only [hew]) (by linarith only [hMrow])
    have hlrω : 0 ≤ Cycle63.AffineLedger.lowRate * omega := mul_nonneg hlr.1.le hω
    linarith [hmax, hωmax, hlrω, hsp, hτκ4, hmargin, hmpos]
  · -- the norms of the multipliers of the rows
    intro r
    have hposN : (0 : ℝ) < ((Ideal.span {firstRowMultiplier first (!reflected) u₀ unit₁ r.val}).absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (hmult0 r)))
    exact (Real.logb_le_iff_le_rpow hZone hposN).mp (hmultB r)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
