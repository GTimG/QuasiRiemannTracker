/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B093
import Submissions.gao_cycle61_plane_20261013.Bundles.B106
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion

/- BEGIN ORIGINAL Cycle61.Moment.HighRawExponent; sha256 a81aeefd32443067dac9d2c9b0b19eb2390eb8547840d799941a87f1457e7200 -/
section
                                      

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEligibleEnergy CenteredMomentAllocatedChildCapacity
open Cycle61.Physical CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O
variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable {P : HighSourceParameters} {η₀ : Character} {Z : ℝ}
variable {Dict : Type*} [Fintype Dict]

/-- The clipped total retains exactly the post-clipping cost. This identity
uses the literal source scales and residual allocation, on either rectangle. -/
theorem high_source_total_raw (D : HighSourceDatum M H P η₀ Z Dict) (hZ : 1< Z)
    (hscale : ∀i,D.source.P i=Z^(D.w i)) :
    D.total P=Real.logb Z (preVolume D.source)-
      Real.logb Z (formalReductionFactor D.projector D.allocation D.source.P)+
      sourcePostClip D.source.toSource D.second Z D.projector D.allocation := by
  let X := sourcePlainScales D.source.toSource D.second
  have hX : ∀j,0< X j := by
    intro j
    cases hs : D.second <;> fin_cases j
    · simpa [X,sourcePlainScales,hs] using D.source.X₁_pos
    · simpa [X,sourcePlainScales,hs] using D.source.X₂_pos
    · simpa [X,sourcePlainScales,hs] using D.source.Y₁_pos
    · simpa [X,sourcePlainScales,hs] using D.source.Y₂_pos
  have hprod : X 0*X 1=D.source.X₁*D.source.X₂ := by
    cases hs : D.second <;> simp [X,sourcePlainScales,hs,D.source.same_product]
  have hraw : Real.logb Z (preVolume D.source)=
      Real.logb Z (X 0)+Real.logb Z (X 1)+∑i,D.w i := by
    rw [preVolume,←hprod,Real.logb_mul (mul_pos (hX 0) (hX 1)).ne'
      (Finset.prod_pos (fun i _=>D.source.P_pos i)).ne',
      Real.logb_mul (hX 0).ne' (hX 1).ne',
      Real.logb_prod _ _ (fun i _=>(D.source.P_pos i).ne')]
    simp_rw [hscale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  have hpre : (∑j,Real.logb Z (CenteredMomentRetainedProfile.clippedScale (X j)))=
      Real.logb Z (X 0)+Real.logb Z (X 1)+negativeTotal (fun j=>Real.logb Z (X j)) := by
    simp only [negativeTotal,Fin.sum_univ_two]
    rw [logb_clipped_scale Z _ hZ (hX 0),logb_clipped_scale Z _ hZ (hX 1)]
    linarith [max_positive_sub (Real.logb Z (X 0)),max_positive_sub (Real.logb Z (X 1))]
  unfold HighSourceDatum.total
  change (∑j,Real.logb Z (CenteredMomentRetainedProfile.clippedScale (X j)))+
    (∑i,D.w i)-clippedReduction _ (fun j=>Real.logb Z (X j)) _=_
  rw [hpre,hraw]
  unfold clippedReduction sourcePostClip
  dsimp [X]
  ring

/-- For every high-bin exponent in [0,1], division by the actual clipping
normalizer pays all clipping growth. Residual divisors can only lower the
remaining exponent, so the bound is uniform before summing their dyads. -/
theorem high_source_exponent_le_raw (D : HighSourceDatum M H P η₀ Z Dict)
    (hZ : 1< Z) (hscale : ∀i,D.source.P i=Z^(D.w i))
    (hw : ∀i,0≤ D.w i) (δ : ℝ) (hδ : 0≤δ) (hδ' : δ≤1) :
    δ*D.total P-sourcePostClip D.source.toSource D.second Z D.projector D.allocation ≤
      δ*Real.logb Z (preVolume D.source) := by
  have hP : ∀i,1≤ D.source.P i := by
    intro i
    rw [hscale]
    exact Real.one_le_rpow hZ.le (hw i)
  have hr : 0≤ Real.logb Z (formalReductionFactor D.projector D.allocation D.source.P) :=
    Real.logb_nonneg hZ (formalReduction_ge_one _ _ _ hP)
  have hc : 0≤ sourcePostClip D.source.toSource D.second Z D.projector D.allocation := by
    unfold sourcePostClip negativeTotal
    exact Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  rw [high_source_total_raw D hZ hscale]
  nlinarith [mul_nonneg hδ hr,mul_nonneg (sub_nonneg.mpr hδ') hc]

end
end OAI.SevenEighths.Cycle61Moment
#print axioms OAI.SevenEighths.Cycle61Moment.high_source_total_raw
#print axioms OAI.SevenEighths.Cycle61Moment.high_source_exponent_le_raw

end
/- END ORIGINAL Cycle61.Moment.HighRawExponent -/

/- BEGIN ORIGINAL Cycle61.Moment.WholeSourceFamily; sha256 ad46ff7a0ff6c329d1979fae3dede0c78059d69630b8029b6decd0dfb8e041bd -/
section
                                      
                                                                

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open Filter Set HeckeFamily HeckePrimeRay HeckeDetectorZeros ConcreteTraceCRT LocalMoment
open ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
open CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open HeckeDetectorFamilyInclusion LowBranch
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

abbrev WholeSourceIndex := Unit ⊕
  (RayQuotient.Characters M H × RayQuotient.Characters M H)

def wholeSourceFamily (η₀ χ : Character) : WholeSourceIndex M H → Character :=
  Sum.elim (fun _ => χ) (fun j => twistedFamily M H hH
    (χ.product (relativeCharacter M H hH η₀ j.1).inverse.inverse) j.2)

def wholeSourceBase (η₀ η : Character) : WholeSourceIndex M H → Character :=
  Sum.elim (fun _ => η) (fun j =>
    (η.product (relativeCharacter M H hH η₀ j.1).inverse.inverse).product
      (HeckeRayQuotient.character M H hH j.2))

/-- Every plain and further relative ray is a member of the same fixed
natural dictionary, with the actual moving Euler puncture retained. -/
theorem whole_source_family_mask (η₀ η χ : Character) (w : O) (hw : w ≠ 0)
    (F : NaturalRow η w) (R : Ideal O) (hR : R ≠ 0)
    (hcoeff : ∀ I : Ideal O, idealCoeff χ I = idealCoeff (excluded F.character R) I)
    (G : ∀ j : WholeSourceIndex M H, NaturalRow (wholeSourceBase M H hH η₀ η j) w)
    (j : WholeSourceIndex M H) (I : Ideal O) :
    idealCoeff (wholeSourceFamily M H hH η₀ χ j) I =
      idealCoeff (excluded (G j).character R) I := by
  cases j with
  | inl j =>
    have he : ∀ I : Ideal O, idealCoeff F.character I = idealCoeff (G (.inl j)).character I := by
      intro I
      rw [F.ideal I,(G (.inl j)).ideal I]
      rfl
    rw [wholeSourceFamily,Sum.elim_inl,hcoeff I,
      excluded_ideal _ _ hR,
      excluded_ideal _ _ hR,he I]
  | inr j =>
    let ν := (relativeCharacter M H hH η₀ j.1).inverse.inverse
    let F₁ := naturalRow (η.product ν) w hw
    have h₁ := actual_fixed_product_natural_mask η χ ν w F F₁ R hR hcoeff
    exact actual_fixed_product_natural_mask (η.product ν) (χ.product ν)
      (HeckeRayQuotient.character M H hH j.2) w F₁ (G (.inr j)) R hR h₁ I

/-- Nonexceptionality is tested at the actual state's fixed ideal. It
excludes principal plains and every further relative ray. -/
theorem whole_source_family_nonprincipal {Z Bmask bΦ : ℝ}
    (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : s.radial.keep z) (F : NaturalRow s.character z) :
    ∀ j : WholeSourceIndex M H,
      (wholeSourceFamily M H hH η₀ (excluded F.character s.puncture) j).residue ≠ 1 := by
  intro j
  cases j with
  | inl j =>
    change (excluded F.character s.puncture).residue ≠ 1
    intro hp
    exact F.nonprincipal (s.row_ne_zero z hz) s.fixedModulus s.puncture
      s.puncture_ne_zero (s.nonexceptional z hz)
      ((HeckeFiniteDeletion.principal_iff_of_mask _ _
        (excludePrimes_mask F.character
          _ (support_prime s.puncture))).mp hp)
  | inr j =>
    exact whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ j.1).inverse hQM
      (relativeCharacter_fixedQ M H hH η₀ j.1 _ hQM hQη) z hz F j.2

/-- One whole-family upper bin supplies all actual relative-slot gates,
including the radial support restriction required by the conductor bound. -/
theorem whole_source_upper_actual_low {Z Bmask bΦ : ℝ}
    (s : NaturalState Z Bmask bΦ) (η₀ : Character)
    (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : s.radial.keep z) (a e T : ℝ)
    (hs : s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0)
    (hupper : zeroMaximum
      (wholeSourceFamily M H hH η₀
        (excluded (naturalRow s.character z (s.row_ne_zero z hz)).character s.puncture))
      (whole_source_family_nonprincipal M H hH s η₀ hQM hQη z hz
        (naturalRow s.character z (s.row_ne_zero z hz))) T < a+2*e) :
    ActualLow M H hH s η₀ hQM hQη a e T z := by
  refine ⟨hs,?_⟩
  intro hz' θ
  have hχ := whole_nonprincipal M H hH s (relativeCharacter M H hH η₀ θ).inverse hQM
    (relativeCharacter_fixedQ M H hH η₀ θ _ hQM hQη) z hz'
    (naturalRow s.character z (s.row_ne_zero z hz'))
  have hh := zeroMaximum_subfamily
    (twistedFamily M H hH
      ((excluded (naturalRow s.character z (s.row_ne_zero z hz')).character s.puncture).product
        (relativeCharacter M H hH η₀ θ).inverse.inverse))
    (wholeSourceFamily M H hH η₀
      (excluded (naturalRow s.character z (s.row_ne_zero z hz')).character s.puncture)) hχ
    (whole_source_family_nonprincipal M H hH s η₀ hQM hQη z hz'
      (naturalRow s.character z (s.row_ne_zero z hz')))
    (fun θ' => Sum.inr (θ,θ')) (fun _ => rfl) T
  exact hh.trans_lt hupper

/-- Whole inversion leaves the family maximum unchanged, so both physical
orientations use this single partition. -/
theorem whole_source_maximum_inverse (η₀ χ : Character)
    (hn : ∀ j : WholeSourceIndex M H,
      (wholeSourceFamily M H hH η₀ χ j).residue ≠ 1) (T : ℝ) :
    zeroMaximum (fun j => (wholeSourceFamily M H hH η₀ χ j).inverse)
      (fun j => inverse_nonprincipal _ (hn j)) T =
      zeroMaximum (wholeSourceFamily M H hH η₀ χ) hn T :=
  maximum_inverse _ hn T

/-- The actual supported nonexceptional source supplies the whole high
family. No selected zero or principal-character hypothesis is assumed. -/
theorem actual_whole_joint_high_row_count {Base : Type*} [Fintype Base]
    (base : Base → Character) (η₀ : Character) (B Q loss : ℝ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (Z : ℝ), 2 ≤ Z → ∀ q m a T Bmask bΦ : ℝ,
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z Bmask bΦ,
      ∀ hQM : ∀ l, (st l).fixedModulus ≤ M,
      ∀ hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus,
      ∀ z : NonzeroJointSourceLabel left u₀ unit → O,
      ∀ hz : ∀ l, (st l).radial.keep (z l),
      ∀ F : ∀ l, NaturalRow (st l).character (z l),
      ∀ index : NonzeroJointSourceLabel left u₀ unit → Base,
      ∀ holes : NonzeroJointSourceLabel left u₀ unit → Ideal O,
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (F l).character (st l).puncture) I =
          idealCoeff (excluded (naturalRow (base (index l))
            (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
            (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded (F l).character (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l)
            (z l) (hz l) (F l)) T) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm:ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm:ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm:ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm:ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm:ℝ) ≤ Z^m) →
      (labels.card:ℝ) ≤ C*(1+T)^J*Z^(m+q*unmarkedDensity (2*a-1)+loss) := by
  let bases : Base×WholeSourceIndex M H → Character :=
    fun j => wholeSourceBase M H hH η₀ (base j.1) j.2
  obtain ⟨J,C,hC,hcount⟩ := actual_joint_buffered_high_row_count bases B Q loss hB hQ hQB hloss
  refine ⟨J,C,hC,?_⟩
  intro left u₀ unit Z hZ q m a T Bmask bΦ hq ha ha' hT labels st hQM hQη z hz F
    index holes hholes hmask hzero hnonzero heq hsupport hnorm hmissing
  let characters := fun l => wholeSourceFamily M H hH η₀
    (excluded (F l).character (st l).puncture)
  have hn := fun l => whole_source_family_nonprincipal M H hH (st l) η₀
    (hQM l) (hQη l) (z l) (hz l) (F l)
  apply hcount left u₀ unit Z hZ q m a T hq ha ha' hT labels characters
    (fun l j => (index l,j)) (fun l _ => holes l) (fun _ _ => false) hn
    ?_ hzero hnonzero heq hsupport hnorm hmissing
  intro l hl j I
  exact whole_source_family_mask M H hH η₀ (base (index l))
    (excluded (F l).character (st l).puncture) (nonzeroJointSourceRow l).val
    (nonzeroJointSourceRow l).property
    (naturalRow (base (index l)) _ (nonzeroJointSourceRow l).property)
    (holes l) (hholes l hl) (hmask l hl)
    (fun j => naturalRow (wholeSourceBase M H hH η₀ (base (index l)) j)
      (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property) j I

#print axioms actual_whole_joint_high_row_count
#print axioms whole_source_family_mask
#print axioms whole_source_family_nonprincipal
#print axioms whole_source_upper_actual_low
#print axioms whole_source_maximum_inverse
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.WholeSourceFamily -/

/- BEGIN ORIGINAL Cycle61.Moment.WholeSourceConductor; sha256 740d84045f624d42ed666cf252afb1ed33b2cb79e9d5556dcd5a2654fa587836 -/
section
                                       
                                         

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open LowBranch
open ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

theorem eventual_whole_source_conductor (η₀ : Character) (bΦ Mcap Bmask margin : ℝ)
    (hbΦ : 0 ≤ bΦ) (hmargin : 0 < margin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ s : NaturalState Z Bmask bΦ,
      s.width ≤ Mcap → ∀ z : O, ∀ F : NaturalRow s.character z,
      s.radial.profile (‖eisEmbedding z‖^2/s.radial.scale) ≠ 0 →
      ∀ j : WholeSourceIndex M H,
      ((wholeSourceFamily M H hH η₀ (excluded F.character s.puncture) j).modulus.absNorm : ℝ)
        ≤ Z^(Mcap+Bmask+margin) := by
  have hrelative := eventual_relative_conductor M H hH η₀ bΦ Mcap Bmask margin hbΦ hmargin
  have hfixed : ∀ᶠ Z : ℝ in atTop, (fixedConductorFactor : ℝ)*bΦ ≤ Z^margin :=
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop _)
  filter_upwards [hrelative,hfixed] with Z hrel hfixed
  refine ⟨hrel.1,?_⟩
  intro s hwidth z F hs j
  cases j with
  | inr j => exact hrel.2 s hwidth z F hs j.1 j.2
  | inl j =>
    change ((excluded F.character s.puncture).modulus.absNorm : ℝ) ≤ _
    have hZp : 0 < Z := zero_lt_one.trans hrel.1
    have hn : ((Ideal.span {z}).absNorm : ℝ) ≤ bΦ*Z^s.rowWidth := by
      rw [← ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span, ← s.scale_eq]
      exact (div_le_iff₀ s.radial.scale_pos).mp (s.radial_support hs)
    have hF := F.modulus_power_bound Z s.characterWidth s.rowWidth bΦ hZp hbΦ
      s.modulus_bound hn
    have hw : Z^(s.characterWidth+s.rowWidth) ≤ Z^Mcap :=
      Real.rpow_le_rpow_of_exponent_le hrel.1.le
        (by simpa only [NaturalState.width,add_comm] using hwidth)
    have hFn : (F.character.modulus.absNorm : ℝ) ≤
        (fixedConductorFactor : ℝ)*bΦ*Z^Mcap :=
      hF.trans (mul_le_mul_of_nonneg_left hw (by positivity))
    rw [excluded_conductor _ _ s.puncture_ne_zero, Nat.cast_mul]
    calc
      _ ≤ ((fixedConductorFactor : ℝ)*bΦ*Z^Mcap)*Z^Bmask :=
        mul_le_mul hFn s.radical_bound (Nat.cast_nonneg _) (by positivity)
      _ = ((fixedConductorFactor : ℝ)*bΦ)*Z^(Mcap+Bmask) := by
        rw [Real.rpow_add hZp]
        ring
      _ ≤ Z^margin*Z^(Mcap+Bmask) :=
        mul_le_mul_of_nonneg_right hfixed (Real.rpow_nonneg hZp.le _)
      _ = Z^(Mcap+Bmask+margin) := by
        rw [← Real.rpow_add hZp]
        congr 1
        ring

#print axioms eventual_whole_source_conductor
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.WholeSourceConductor -/

/- BEGIN ORIGINAL Cycle61.Moment.WholeSourceDatum; sha256 b3c2f6c1d35a42ea59a2526dc7402d137406852f88a9574a25ac21d61ac3b2c3 -/
section
                                          

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical
open HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open ConcreteTraceCRT LowBranch CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def wholeHighDatum {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (s : Data ι) (second : Bool)
    (L : Ideal O) (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (ap bp : ℝ) :
    HighSourceDatum M H P η₀ Z (WholeSourceIndex M H) where
  state := st
  hQM := hQM
  hQη := hQη
  z := z
  hz := hz
  natural := naturalRow st.character z (st.row_ne_zero z hz)
  character := wholeSourceFamily M H hH η₀
    (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture)
  hcharacter := whole_source_family_nonprincipal M H hH st η₀ hQM hQη z hz _
  member := Sum.inl ()
  Slot := ι
  source := s
  second := second
  projector := L
  allocation := alloc
  w := w
  σ := σ
  v := v
  θ := θ
  t := s.t
  W := ![s.W₁,s.W₂]
  X := Cycle61.Physical.postPlainScale L alloc
    (Cycle61.Physical.sourcePlainScales s.toSource second)
  r := fun j => Real.logb Z (clippedScale (Cycle61.Physical.postPlainScale L alloc
    (Cycle61.Physical.sourcePlainScales s.toSource second) j))/P.d
  A := fun _ => ap
  B := fun _ => bp


theorem whole_high_datum_low {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : HighSourceParameters) (η₀ : Character) (Z : ℝ)
    (st : NaturalState Z P.Bmask P.bΦ)
    (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
    (z : O) (hz : st.radial.keep z) (s : Data ι) (second : Bool)
    (L : Ideal O) (alloc : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (w σ v : ι → ℝ) (θ : ι → RayQuotient.Characters M H) (ap bp a : ℝ) (i : ℕ)
    (hs : st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale) ≠ 0)
    (hupper : let D := wholeHighDatum M H hH P η₀ Z st hQM hQη z hz s second L alloc w σ v θ ap bp
      HeckeDetectorZeros.zeroMaximum D.character D.hcharacter (3*(i+1 : ℕ)*Z^P.τ) < a+2*P.e) :
    ActualLow M H hH st η₀ hQM hQη a P.e (3*(i+1 : ℕ)*Z^P.τ) z := by
  exact whole_source_upper_actual_low M H hH st η₀ hQM hQη z hz a P.e _ hs hupper

#print axioms wholeHighDatum
#print axioms whole_high_datum_low
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.WholeSourceDatum -/
