import Candidate.Target830.Physical.Contract
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialCoarse
import Candidate.Cycle63.Physical.ExternalHeight
import Candidate.Cycle63.Moment.InitialAffineContract

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
open OAI.SevenEighths.Cycle63Physical
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle63Moment
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R ≤ H)

/-- The analytic input is restricted to the bounded external-height range,
with the same literal initial energy and geometric gates as OAI.SevenEighths.Target830.Physical.InitialAffineAt (P:=plane). -/
def BoundedInitialAffineAt (plane : SourcePlane) (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax ε τ Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters R H) (w σ v : T → ℝ)
    (t height : ℝ), (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
    1+|t|+height ≤ Z^τ →
  ∀ width : ℝ, Mmin ≤ width → width ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    plainLower*width ≤ length Z X₁ → length Z X₁ ≤ plainUpper*width →
    plainLower*width ≤ length Z X₂ → length Z X₂ ≤ plainUpper*width →
    (17/500)*width ≤ ∑ i, w i → (∑ i, w i) ≤ (1/25)*width →
    length Z X₁+length Z X₂+plane.lambda*(∑ i, w i) ≤
      plane.B*width →
    initialEnergy R H hH W bslot Z width η η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(width+ε)

lemma profile_control_mono {a b : ℝ} (p : Profiles a b)
    {S T : Finset (ℕ × ℕ)} (hST : S ⊆ T) : p.control S ≤ p.control T := by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hST) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

lemma initial_plain_length_cap (Z X width Mmax : ℝ) (hZ : 1 < Z) (_hX : 0 < X)
    (hMmax : 0 ≤ Mmax) (hw : width ≤ Mmax)
    (hL : length Z X ≤ plainUpper*width) : X ≤ Z^(Mmax+1) := by
  apply (le_max_right 1 X).trans
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mp
  change length Z X ≤ Mmax+1
  norm_num [plainUpper] at hL
  linarith

/-- The degree is fixed after the two genuine estimates and before the base,
slot data, profiles, and all external frequencies and heights. -/
theorem initial_height_extend (plane : SourcePlane) (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax extra ε τ : ℝ)
    (hτ : 0 < τ) (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (jSmall jCoarse : ℕ) (Ssmall Scoarse : Finset (ℕ × ℕ)) :
    ∃ degree : ℕ, ∀ (η : Label → Character) (η₀ : Character) (Q : Ideal O)
      (Csmall Ccoarse : ℝ), 0 ≤ Csmall → 0 ≤ Ccoarse →
    (∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      BoundedInitialAffineAt (plane:=plane) (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε τ Z (η label) η₀ Q jSmall Ssmall Csmall) →
    (∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      InitialCoarseAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        extra Z (η label) η₀ Q jCoarse Scoarse Ccoarse) →
    ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      OAI.SevenEighths.Target830.Physical.InitialAffineAt (P:=plane) (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε Z (η label) η₀ Q degree (Ssmall ∪ Scoarse) (Csmall+Ccoarse) := by
  obtain ⟨degree,hdegree⟩ := Cycle63.Physical.extend_bounded_height_bound hτ extra ε jSmall jCoarse
  refine ⟨degree,?_⟩
  intro η η₀ Q Csmall Ccoarse hCs hCc hsmall hcoarse
  filter_upwards [hsmall,hcoarse,eventually_gt_atTop (1 : ℝ)] with Z hzsmall hzcoarse hZ
  intro label T θ w σ v t height hw hwm hσlo hσhi hheight hv width hwidth hwidthmax
    Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
  have hMmax : 0 ≤ Mmax := hMmin.le.trans hMM
  have hXcap₁ := initial_plain_length_cap Z X₁ width Mmax hZ hX₁ hMmax hwidthmax hu₁
  have hXcap₂ := initial_plain_length_cap Z X₂ width Mmax hZ hX₂ hMmax hwidthmax hu₂
  let control := diagonalControl Φ*(p.control (Ssmall ∪ Scoarse))^2
  have hd := diagonalControl_nonneg Φ
  have hcontrol : 0 ≤ control := mul_nonneg hd (sq_nonneg _)
  have hpcS := profile_control_mono p (Finset.subset_union_left (s₁ := Ssmall) (s₂ := Scoarse))
  have hpcC := profile_control_mono p (Finset.subset_union_right (s₁ := Ssmall) (s₂ := Scoarse))
  have hpS := p.control_nonneg Ssmall
  have hpC := p.control_nonneg Scoarse
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hSmall : 1+|t|+height ≤ Z^τ →
      initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
        (p.profile 0) (p.profile 1) Φ ≤ Csmall*control*(1+|t|+height)^jSmall*Z^(width+ε) := by
    intro hheightcap
    have hh := hzsmall label T θ w σ v t height hw hwm hσlo hσhi hheight hv hheightcap
      width hwidth hwidthmax Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hl₁ hu₁ hl₂ hu₂ hwl hwu hcap
    apply hh.trans
    dsimp only [control]
    rw [←mul_assoc Csmall]
    gcongr
  have hCoarse : initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ ≤ Ccoarse*control*(1+|t|+height)^jCoarse*Z^(width+extra) := by
    have hh := hzcoarse label T θ w σ v t height hw hwm hσlo hσhi hheight
      width hwidth hwidthmax Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hXcap₁ hXcap₂
    apply hh.trans
    dsimp only [control]
    rw [←mul_assoc Ccoarse]
    gcongr
  have hh := hdegree Z (1+|t|+height) width
    (initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
      (p.profile 0) (p.profile 1) Φ) control Csmall Ccoarse hZ.le
    (by linarith [abs_nonneg t]) hcontrol hCs hCc hSmall hCoarse
  change initialEnergy R H hH W bslot Z width (η label) η₀ Q T θ w σ v t X₁ X₂
    (p.profile 0) (p.profile 1) Φ ≤ _
  exact hh.trans_eq (by dsimp only [control]; ring)

/-- A bounded-height affine theorem is the sole new analytic input. The
all-height coarse side is obtained from the original incumbent, with a common
final degree before the fixed bases and the live initial configurations. -/
theorem original_initial_height (plane : SourcePlane) (W : ℝ → ℂ) (aslot bslot a b bΦ mesh lo hi Mmin Mmax coarseError ε τ : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hbΦ : 0 < bΦ)
    (hmesh : 0 ≤ mesh) (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (hcError : 0 < coarseError) (hcOne : coarseError ≤ 1)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hτ : 0 < τ)
    (η : Label → Character) (jSmall : ℕ) (Ssmall : Finset (ℕ × ℕ))
    (hsmall : ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ R → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Csmall : ℝ, 0 < Csmall ∧ ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
        BoundedInitialAffineAt (plane:=plane) (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
          ε τ Z (η label) η₀ Q jSmall Ssmall Csmall) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ R → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      OAI.SevenEighths.Target830.Physical.InitialAffineAt (P:=plane) (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε Z (η label) η₀ Q degree S C := by
  obtain ⟨jCoarse,Scoarse,hcoarse⟩ := original_initial_coarse (α := α) R H hH W
    aslot bslot a b bΦ mesh lo hi Mmin Mmax coarseError haslot hWs hW hbslot
    ha haUpper hb hbΦ hmesh hMmin hMM hcError hcOne hbeta η
  obtain ⟨degree,hextend⟩ := initial_height_extend (plane:=plane) (α := α) (Label := Label) R H hH W
    bslot a b bΦ mesh lo hi Mmin Mmax
    (coarseError+2*(Fintype.card α : ℝ)*mesh) ε τ hτ hMmin hMM
    jSmall jCoarse Ssmall Scoarse
  refine ⟨degree,Ssmall ∪ Scoarse,?_⟩
  intro η₀ Q hQR hQ0 hQt hQ72
  obtain ⟨Csmall,hCs,hsmall⟩ := hsmall η₀ Q hQR hQ0 hQt hQ72
  obtain ⟨Ccoarse,hCc,hcoarse⟩ := hcoarse η₀ Q hQR hQ0 hQt hQ72
  refine ⟨Csmall+Ccoarse,add_pos hCs hCc,?_⟩
  exact hextend η η₀ Q Csmall Ccoarse hCs.le hCc.le hsmall
    (hcoarse.mono (fun _ h => h.2))

#print axioms profile_control_mono
#print axioms initial_plain_length_cap
#print axioms initial_height_extend
#print axioms original_initial_height
end
end OAI.SevenEighths.Target830.Source.Assembly
