/- Copyright (c) 2026 Sil. Apache-2.0.
Union/max of the two genuine contribution bounds and the EXISTING finite
split into the literal raw side. This introduces no new Cauchy count.
Both branch suppliers are visible inputs to this finite mechanism.
-/
import Candidate.SilPrior.FourthPower.RepairedContributionContract

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedCombinedFinite
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSourceProfileMass CenteredMomentFirstSectors CenteredMomentActiveSource
open CenteredMomentSecondBlockAggregate
open CenteredMomentSecondRetainedAggregate
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedPrincipalWindow MixedFirstProfileEnvelope
open RepairedRawContext RepairedFirstFrame RepairedSourceSideSupply
open RepairedContributionContract RepairedSupplierSplit RepairedFirstRawSides
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character} (d : RootInput M H hH ι W N Holes ε Z Kslot η η₀)

theorem contributionBound_mono (f : Frame d) (j J : ℕ) (S T : Finset (ℕ×ℕ))
    (C C' : ℝ) (u : Id) (tp : ℝ) (hC : 0 ≤ C) (hCC : C ≤ C') (hj : j ≤ J) (hS : S ⊆ T) :
    contributionBound d f j S C u tp ≤ contributionBound d f J T C' u tp := by
  have h₁ : sourceControl S d.root.W₁ ≤ sourceControl T d.root.W₁ :=
    Seminorm.le_def.mp (Finset.sup_mono hS) d.root.W₁
  have h₂ : sourceControl S d.root.W₂ ≤ sourceControl T d.root.W₂ :=
    Seminorm.le_def.mp (Finset.sup_mono hS) d.root.W₂
  have hproduct := mul_le_mul h₁ h₂ (sourceControl_nonneg S d.root.W₂) (sourceControl_nonneg T d.root.W₁)
  have hp := pow_le_pow_left₀
    (mul_nonneg (sourceControl_nonneg S d.root.W₁) (sourceControl_nonneg S d.root.W₂)) hproduct 2
  have hheight : 1 ≤ height d.t₀ d.V d.root.t₁ d.root.t₂ := by
    unfold height
    linarith [abs_nonneg d.t₀,norm_nonneg d.root.t₁,norm_nonneg d.root.t₂,d.hV]
  have hh := pow_le_pow_right₀ hheight hj
  have hheight0 := zero_le_one.trans hheight
  have hC' := hC.trans hCC
  have hv := pow_le_pow_right₀ (show 1 ≤ 1+‖tp‖ by linarith [norm_nonneg tp]) (Nat.mul_le_mul_left 2 hj)
  have href : 0 ≤ f.reference := by
    have hz := (zero_lt_one.trans d.one_lt_Z).le
    unfold Frame.reference MixedFirstExceptionalNormalization.reference
    positivity
  have hz := (zero_lt_one.trans d.one_lt_Z).le
  unfold contributionBound amplitude
  gcongr

theorem contributionBound_add (f : Frame d) (J : ℕ) (S : Finset (ℕ×ℕ)) (CL CS : ℝ) (u : Id) (tp : ℝ) :
    contributionBound d f J S CL u tp+contributionBound d f J S CS u tp =
      contributionBound d f J S (CL+CS) u tp := by
  unfold contributionBound amplitude
  ring

def FrameRawFor (J : ℕ) (S : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ f : Frame d,∀ u : Id,Squarefree u → (u.absNorm:ℝ) ≤ Z^(8:ℝ) → ∀ tp : ℝ,
    rawEnergy d.root (by norm_num) f.label.val.2 f.label.val.1
      (commonLabels_supported _ _ _ f.label.property).1 u f.tau tp f.scale ≤
      contributionBound d f J S C u tp

/-- Actual finite Large+Small are already disjoint pieces of one
previous Cauchy bound. Taking max degree and union controls costs only
the sum of the two fixed constants, never a new moving cardinality. -/
theorem frame_raw_of_contributions (hε : 0 < ε)
    (JL JS : ℕ) (SL SS : Finset (ℕ×ℕ)) (CL CS : ℝ) (hCL : 0 ≤ CL) (hCS : 0 ≤ CS)
    (hLarge : ContributionFor d hε true JL SL CL)
    (hSmall : ContributionFor d hε false JS SS CS) :
    FrameRawFor d (max JL JS) (SL∪SS) (CL+CS) := by
  intro f u hu hucap tp
  have hs := commonLabels_supported _ _ _ f.label.property
  have hCD := (commonLabels_data _ _ _ _ f.label.property).2.2
  have hK : 0 < f.scale := Real.rpow_pos_of_pos (zero_lt_one.trans d.one_lt_Z) _
  have he := raw_energy_of_branch_bounds d.root (by norm_num) (by norm_num) d.cover
    f.label.val.2 f.label.val.1 hs.2 hs.1 hCD.symm u
    (d.choose hε f.label.val.1) (d.large f.label.val.1) f.tau tp f.scale
    (contributionBound d f JL SL CL u tp) (contributionBound d f JS SS CS u tp) hK
    (fun rows => by
      simpa only [RootInput.contribution, Bool.false_eq_true, if_false, if_true]
        using (hLarge f u hu hucap tp rows))
    (fun rows => by
      simpa only [RootInput.contribution, Bool.false_eq_true, if_false, if_true]
        using (hSmall f u hu hucap tp rows))
  apply he.trans
  have hl := contributionBound_mono d f JL (max JL JS) SL (SL∪SS) CL CL u tp hCL le_rfl
    (le_max_left _ _) Finset.subset_union_left
  have hs := contributionBound_mono d f JS (max JL JS) SS (SL∪SS) CS CS u tp hCS le_rfl
    (le_max_right _ _) Finset.subset_union_right
  exact (add_le_add hl hs).trans_eq (contributionBound_add d f (max JL JS) (SL∪SS) CL CS u tp)

end
end Candidate.SilPrior.FourthPower.RepairedCombinedFinite
