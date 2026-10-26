import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialCoarse
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.ExternalHeight
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.InitialAffineContract
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Arithmetic.Constants
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Physical
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle63Moment
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (R : Ideal O) [NeZero R]
local instance initialHeightFinite : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
variable (H : Subgroup (O ⧸ R)ˣ) (hH : RayOrthogonality.globalUnits R ≤ H)

/-- The analytic input is restricted to the bounded external-height range,
with the same literal initial energy and geometric gates as InitialAffineAt. -/
def BoundedInitialAffineAt (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax ε τ Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters R H) (w σ v : T → ℝ)
    (t height : ℝ), (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |v i| ≤ height) →
    1+|t|+height ≤ Z^τ →
  ∀ width : ℝ, Mmin ≤ width → width ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    Cycle63.CountAffine.windowBottom*width ≤ length Z X₁ → length Z X₁ ≤ Cycle63.CountAffine.plainLengthTop*width →
    Cycle63.CountAffine.windowBottom*width ≤ length Z X₂ → length Z X₂ ≤ Cycle63.CountAffine.plainLengthTop*width →
    Cycle63.AffineLedger.slotFloor*width ≤ ∑ i, w i → (∑ i, w i) ≤ Cycle63.AffineLedger.slotTop*width →
    length Z X₁+length Z X₂+Cycle63.AffineLedger.lam*(∑ i, w i) ≤
      Cycle63.AffineLedger.B*width →
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
    (hL : length Z X ≤ Cycle63.CountAffine.plainLengthTop*width) : X ≤ Z^(Mmax+1) := by
  apply (le_max_right 1 X).trans
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mp
  change length Z X ≤ Mmax+1
  simp only [Cycle63.CountAffine.plainLengthTop] at hL
  linarith

omit [Fintype α] [DecidableEq α] [Fintype Label] in
/-- The degree is fixed after the two genuine estimates and before the base,
slot data, profiles, and all external frequencies and heights. -/
theorem initial_height_extend (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax extra ε τ : ℝ)
    (hτ : 0 < τ) (hMmin : 0 < Mmin) (hMM : Mmin ≤ Mmax)
    (jSmall jCoarse : ℕ) (Ssmall Scoarse : Finset (ℕ × ℕ)) :
    ∃ degree : ℕ, ∀ (η : Label → Character) (η₀ : Character) (Q : Ideal O)
      (Csmall Ccoarse : ℝ), 0 ≤ Csmall → 0 ≤ Ccoarse →
    (∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      BoundedInitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε τ Z (η label) η₀ Q jSmall Ssmall Csmall) →
    (∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      InitialCoarseAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        extra Z (η label) η₀ Q jCoarse Scoarse Ccoarse) →
    ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      InitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
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

end
end OAI.SevenEighths.Cycle63Physical

end Record1252270103Bootstrap.PR67
