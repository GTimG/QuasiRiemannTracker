/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B064
import Submissions.cycle61_c0125139.Bundles.B078
import Submissions.cycle61_c0125139.Bundles.B079
import Lean
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Cauchy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCommonSourceBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstReferenceSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstSourceConductorCaps

/- BEGIN ORIGINAL Cycle61.Physical.InitialHeight; sha256 8902f0d89111cca2ea29c333a4c8ca6bee84129d7768985dc54d1d4a9f85b13c -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                     
                                      
                                           

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Physical
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource QuadraticInitialBound Cycle61Moment
local notation "O" => HeckeFamily.O
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
variable (R : Ideal O) [NeZero R]
local instance : Finite (O ⧸ R) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne R)
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
    (41/100)*width ≤ length Z X₁ → length Z X₁ ≤ (44/100)*width →
    (41/100)*width ≤ length Z X₂ → length Z X₂ ≤ (44/100)*width →
    (17/500)*width ≤ ∑ i, w i → (∑ i, w i) ≤ (1/25)*width →
    length Z X₁+length Z X₂+Cycle61.Arithmetic.lambda*(∑ i, w i) ≤
      Cycle61.Arithmetic.B*width →
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
    (hL : length Z X ≤ (44/100)*width) : X ≤ Z^(Mmax+1) := by
  apply (le_max_right 1 X).trans
  apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le (le_max_left 1 X))).mp
  change length Z X ≤ Mmax+1
  linarith

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
  obtain ⟨degree,hdegree⟩ := Cycle61.Physical.extend_bounded_height_bound hτ extra ε jSmall jCoarse
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
theorem original_initial_height (W : ℝ → ℂ) (aslot bslot a b bΦ mesh lo hi Mmin Mmax coarseError ε τ : ℝ)
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
        BoundedInitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
          ε τ Z (η label) η₀ Q jSmall Ssmall Csmall) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ R → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ label : Label,
      InitialAffineAt (α := α) R H hH W bslot a b bΦ mesh lo hi Mmin Mmax
        ε Z (η label) η₀ Q degree S C := by
  obtain ⟨jCoarse,Scoarse,hcoarse⟩ := original_initial_coarse (α := α) R H hH W
    aslot bslot a b bΦ mesh lo hi Mmin Mmax coarseError haslot hWs hW hbslot
    ha haUpper hb hbΦ hmesh hMmin hMM hcError hcOne hbeta η
  obtain ⟨degree,hextend⟩ := initial_height_extend (α := α) (Label := Label) R H hH W
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
end OAI.SevenEighths.Cycle61Physical

end
/- END ORIGINAL Cycle61.Physical.InitialHeight -/

/- BEGIN ORIGINAL Cycle61.Moment.JointKernel; sha256 55e690d231a3cf5544d016a1f659c209d811370228249038c33e056724faf167 -/
section
                                                 

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap
open CenteredMomentCauchy CenteredMomentSmooth

def jointPaddedCoefficient {Label κ : Type*} [DecidableEq Label]
    {α : Label → Type*} (tag : κ → Label) (c : (k : κ) → α (tag k) → ℂ)
    (k : κ) (i : Sigma α) : ℂ :=
  if h : i.1 = tag k then c k (h ▸ i.2) else 0

theorem joint_padded_sum {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α : Label → Type*} [∀ l, Fintype (α l)] (tag : κ → Label)
    (c : (k : κ) → α (tag k) → ℂ) (f : (l : Label) → α l → ℂ) (k : κ) :
    (∑ i : Sigma α, jointPaddedCoefficient tag c k i * f i.1 i.2) =
      ∑ i : α (tag k), c k i * f (tag k) i := by
  rw [Fintype.sum_sigma]
  have hinner (l : Label) :
      (∑ i : α l, jointPaddedCoefficient tag c k ⟨l,i⟩ * f l i) =
        if h : l = tag k then ∑ i : α (tag k), c k i * f (tag k) i else 0 := by
    by_cases h : l = tag k
    · subst l
      simp only [jointPaddedCoefficient, dite_true]
    · simp only [jointPaddedCoefficient, h, dite_false, zero_mul, Finset.sum_const_zero]
  simp_rw [hinner]
  simp

theorem joint_padded_left_column {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α : Label → Type*} [∀ l, Fintype (α l)] (tag : κ → Label)
    (c : (k : κ) → α (tag k) → ℂ) (u : (l : Label) → α l → ℝ)
    (V : ℝ → ℂ) (k : κ) (t : ℝ) :
    leftColumn Finset.univ (jointPaddedCoefficient tag c k) V (fun i => u i.1 i.2) t =
      leftColumn Finset.univ (c k) V (u (tag k)) t := by
  exact joint_padded_sum tag c (fun l i => columnPhase V (u l i) t) k

theorem joint_padded_right_column {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α : Label → Type*} [∀ l, Fintype (α l)] (tag : κ → Label)
    (c : (k : κ) → α (tag k) → ℂ) (u : (l : Label) → α l → ℝ)
    (V : ℝ → ℂ) (k : κ) (t : ℝ) :
    rightColumn Finset.univ (jointPaddedCoefficient tag c k) V (fun i => u i.1 i.2) t =
      rightColumn Finset.univ (c k) V (u (tag k)) t := by
  have he (i : Sigma α) : star (jointPaddedCoefficient tag c k i) =
      jointPaddedCoefficient tag (fun k i => star (c k i)) k i := by
    unfold jointPaddedCoefficient
    split_ifs <;> simp
  simp only [rightColumn, he]
  exact joint_padded_sum tag (fun k i => star (c k i))
    (fun l i => columnPhase V (u l i) t) k

theorem joint_padded_kernel {Label κ : Type*} [Fintype Label] [DecidableEq Label]
    {α β : Label → Type*} [∀ l, Fintype (α l)] [∀ l, Fintype (β l)]
    (tag : κ → Label) (c : (k : κ) → α (tag k) → ℂ)
    (d : (k : κ) → β (tag k) → ℂ)
    (u : (l : Label) → α l → ℝ) (v : (l : Label) → β l → ℝ)
    (K : ℝ → ℝ → ℂ) (k : κ) :
    (∑ i : Sigma α, ∑ j : Sigma β,
      (jointPaddedCoefficient tag c k i * star (jointPaddedCoefficient tag d k j)) *
        K (u i.1 i.2) (v j.1 j.2)) =
      ∑ i : α (tag k), ∑ j : β (tag k),
        (c k i * star (d k j)) * K (u (tag k) i) (v (tag k) j) := by
  have he (j : Sigma β) : star (jointPaddedCoefficient tag d k j) =
      jointPaddedCoefficient tag (fun k j => star (d k j)) k j := by
    unfold jointPaddedCoefficient
    split_ifs <;> simp
  simp_rw [he, mul_assoc]
  have hi (i : Sigma α) :
      (∑ j : Sigma β, jointPaddedCoefficient tag (fun k j => star (d k j)) k j *
        K (u i.1 i.2) (v j.1 j.2)) =
      ∑ j : β (tag k), star (d k j) * K (u i.1 i.2) (v (tag k) j) :=
    joint_padded_sum tag (fun k j => star (d k j))
      (fun l j => K (u i.1 i.2) (v l j)) k
  have hout : (∑ i : Sigma α, ∑ j : Sigma β,
      jointPaddedCoefficient tag c k i *
        (jointPaddedCoefficient tag (fun k j => star (d k j)) k j *
          K (u i.1 i.2) (v j.1 j.2))) =
      ∑ i : Sigma α, jointPaddedCoefficient tag c k i *
        (∑ j : β (tag k), star (d k j) * K (u i.1 i.2) (v (tag k) j)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, hi i]
  rw [hout]
  have hh := joint_padded_sum tag c
    (fun l i => ∑ j : β (tag k), star (d k j) * K (u l i) (v (tag k) j)) k
  simpa only [Finset.mul_sum, mul_assoc] using hh

theorem whole_kernel_dependent_row_estimate (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {Label κ : Type*} [Fintype Label] [DecidableEq Label]
        {α β : Label → Type*} [∀ l, Fintype (α l)] [∀ l, Fintype (β l)],
      ∀ (rows : Finset κ) (tag : κ → Label)
        (c : (k : κ) → α (tag k) → ℂ) (d : (k : κ) → β (tag k) → ℂ)
        (u : (l : Label) → α l → ℝ) (v : (l : Label) → β l → ℝ)
        (ρ x : κ → ℝ) (η : κ → ℂ),
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ,
        Real.sqrt (∑ k ∈ rows, ‖leftColumn Finset.univ (c k) (V 2) (u (tag k)) t‖^2) *
        Real.sqrt (∑ k ∈ rows, ‖rightColumn Finset.univ (d k) (V 3) (v (tag k)) t‖^2) ≤
          E*(1+‖t‖)^J) →
      (1+R)^A * ‖∑ k ∈ rows, η k *
        (∑ i : α (tag k), ∑ j : β (tag k), (c k i * star (d k j)) *
          wholeKernel W V R (ρ k) (x k) (u (tag k) i) (v (tag k) j))‖ ≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro R hR Label κ _ _ α β _ _ rows tag c d u v ρ x η hη hV₀ hV₁ E hE henergy
  have hh := hbound R hR rows (Finset.univ : Finset (Sigma α))
    (Finset.univ : Finset (Sigma β)) (jointPaddedCoefficient tag c)
    (jointPaddedCoefficient tag d) (fun i => u i.1 i.2) (fun j => v j.1 j.2)
    ρ x η hη hV₀ hV₁ E hE (by
      intro t
      simpa only [joint_padded_left_column, joint_padded_right_column] using henergy t)
  simpa only [joint_padded_kernel] using hh

#print axioms whole_kernel_dependent_row_estimate
#print axioms joint_padded_sum
#print axioms joint_padded_left_column
#print axioms joint_padded_right_column
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.JointKernel -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.Decomposition; sha256 68f9c45ce83059e6150a879de2365352a467e392e9ec0ab9ec9115e619a5abad -/
section
                                                                         
                                                                  
                                                               
           

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstSourceReduction CenteredMomentFirstReferenceSource
open CenteredMomentFirstAnnularInput CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationRadicalChoice
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentGaussEnergy
open CenteredMomentFirstScale CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCommonSourceBudget
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstRetainedNorm CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentFirstDiscardedEnergy CenteredMomentSourceLiveColumn
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Exact physical source mass, with all first labels, inactive subsets and
local dyadic blocks retained. There is no first-label counting envelope. -/
theorem actual_physical_mass_direct_sum (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (fixedBadMask*idealGenerator R) 1 W K Z ξ =
      ∑p : Labels s R seed, ∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n : SourceBlocks s R seed K Z ξ p E,
          ‖originalBlock s R seed W K Z ξ p E n‖ :=
  physicalMass_eq_sum s R seed W K Z ξ

/-- The physical source's complete coordinate, including every first label,
inactive subset and local dyadic block. -/
abbrev FirstSourceCoordinate (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) :=
  (p : Labels s R seed) ×
    (E : ↥(inactiveSubsets p.val.1 p.val.2)) × SourceBlocks s R seed K Z ξ p E.val

def coordinateBlock (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
    (K Z ξ : ℝ) (q : FirstSourceCoordinate s R seed K Z ξ) : ℂ :=
  originalBlock s R seed W K Z ξ q.1 q.2.1.val q.2.2

/-- A harmless unit phase converts the literal sum of block norms into one
joint complex sum, retaining its full coordinate. -/
def normPhase (z : ℂ) : ℂ := (‖z‖ : ℂ)/z

lemma normPhase_norm (z : ℂ) : ‖normPhase z‖≤1 := by
  by_cases hz : z=0
  · simp [normPhase,hz]
  · simp [normPhase,norm_ne_zero_iff.mpr hz]

lemma normPhase_mul (z : ℂ) : normPhase z*z=(‖z‖ : ℂ) := by
  by_cases hz : z=0
  · simp [normPhase,hz]
  · exact div_mul_cancel₀ _ hz

/-- Exact joint first-source representation. These phases have norm at most
one, so joint Mellin/sector contraction can consume the whole physical mass
without introducing a count of first labels. -/
theorem actual_physical_mass_joint_sum (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (fixedBadMask*idealGenerator R) 1 W K Z ξ =
      ‖∑q : FirstSourceCoordinate s R seed K Z ξ,
        normPhase (coordinateBlock s R seed W K Z ξ q)*
          coordinateBlock s R seed W K Z ξ q‖ := by
  simp_rw [normPhase_mul]
  rw [←Complex.ofReal_sum]
  rw [Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  rw [actual_physical_mass_direct_sum,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.sum_sigma]
  dsimp only [coordinateBlock]
  exact (Finset.sum_coe_sort (inactiveSubsets p.val.1 p.val.2)
    (fun E => ∑n : SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖)).symm

omit [DecidableEq ι] in
/-- Literal allocation reduction over the entire matched common-label family.
All live allocation coefficients and child normalizers remain visible. -/
theorem actual_common_allocation_direct_sum {Label : Type*} [Fintype Label]
    (N : ℕ) (a b : ℝ) (ha : 0< a) (s : Input ι)
    (hcard : Fintype.card ι≤ N) (haS : a≤ s.lower) (hbS : s.upper≤ b)
    (C : Label→Ideal O) (R seed : Ideal O) (hC : ∀j,Supported (C j))
    (hseed : ∀j,seed∣C j) (τ : Label→Character) (t : Label→ℝ)
    (L : Label→Ideal O) (W : 𝓢(ℝ,ℂ)) (K weight : Label→ℝ)
    (hK : ∀j,0< K j) (hw : ∀j,0≤ weight j)
    (hW : ∀j,∀z : O,0≤(W (‖eisEmbedding z‖^2/K j)).re) :
    (∑j,weight j*((CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) (C j) (hC j)
      (τ j) (t j) (L j) W (K j)).re/volume s)) ≤
    ∑j,weight j*((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
      ∑B : actualAllocations s.pools (C j),
        if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R (L j) B
            (τ j) (t j) W (K j)
        else 0) := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (common_energy_live_allocations N a b ha s hcard haS hbS (C j) R seed
      (hC j) (hseed j) (τ j) (t j) (L j) W (K j) (hK j) (hW j)) (hw j)

/-- Geometric data of a literal amplified source branch. -/
structure FirstBranchGeometry where
  (R seed I J E : Ideal O)
  (d cLog K X Tsec H0 : ℝ)

def FirstBranchGeometry.Eligible (g : FirstBranchGeometry) (Z BR Bs Mmax Csec ξ : ℝ) : Prop :=
  g.R≠0 ∧ g.seed≠0 ∧ (g.R.absNorm:ℝ)≤ Z^BR ∧ (g.seed.absNorm:ℝ)≤ Z^Bs ∧
  g.E≠0 ∧ 0< g.K ∧ 0< g.X ∧ g.Tsec≤ Csec*firstNominalScale g.I g.J g.E g.K g.X ∧
  0< g.H0 ∧ g.H0≤4*frequencyRadius g.Tsec Z ξ ∧ 8*g.H0≤ Z^Mmax

def actualMainSource (s : Input ι) (g : FirstBranchGeometry)
    (Z sigma Csec ξ reserve : ℝ) : ℝ :=
  normalizedGaussSource s g.R g.seed ballProfile
    (mainCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z) g.cLog sigma
      (frequencyLoss Z (32*Csec) ξ) reserve)

def actualErrorSources (s : Input ι) (g : FirstBranchGeometry)
    (Z sigma Csec ξ reserve : ℝ) (P : Finset (Ideal O))
    (τ : elementPool P→Fin 3→RayCharacter→Character) : ℝ :=
  ∑p : elementPool P, ∑i : Fin 3,
    (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
      ∑χ : RayCharacter, ∑B : actualAllocations (activeInput s).pools
          ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          g.R g.seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z) g.cLog sigma
            (frequencyLoss Z (32*Csec) ξ) reserve p (errorIndex i+1))

omit [DecidableEq ι] in
/-- Genuine source amplification in the full matched direct sum. The same
prime pool and threshold work before the live family. No first-label envelope
or terminal energy estimate is assumed. The three extracted branches remain
literal child sources, with their local error costs and allocation normalizers. -/
theorem actual_matched_source_amplification
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec ξ reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b)
    (hgap : eta< sigma/6) (hC : 1≤ Csec) (hξ : 0≤ξ) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀{Label : Type*} [Fintype Label],
    ∀s : Label→Input ι, ∀g : Label→FirstBranchGeometry, ∀weight : Label→ℝ,
      (∀j,0≤ weight j) → (∀j,g j |>.Eligible Z BR Bs Mmax Csec ξ) →
      (∀j,∀i,Function.support ((s j).W i)⊆Set.Iic b) →
    ∀z : Label→ι→ℝ, (∀j i,z j i≤ eta) → (∀j i,(s j).P i=Z^(z j i)) →
    ∃τ : Label→elementPool P→Fin 3→RayCharacter→Character,
      (∀j p i χ,(τ j p i χ).modulus.absNorm≤
        radicalBound (childCharacter (s j).η χ) fixedBadMask p.val
          (errorMovingExponent (errorIndex i))) ∧
      (∑j,weight j*normalizedGaussSource (s j) (g j).R (g j).seed
        CenteredMomentFirstAnnularMajorant.profile (g j).H0) ≤
      (56/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*(∑j,weight j*actualMainSource (s j) (g j) Z sigma Csec ξ reserve)+
          ∑j,weight j*actualErrorSources (s j) (g j) Z sigma Csec ξ reserve P (τ j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) rayM H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec ξ reserve hsigma hloss hM hb hgap hC hξ hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro Label _ s g weight hw hg hsupp z hz hlen
  choose τ hN henergy using (fun j => hfam (s j).η)
  refine ⟨τ,hN,?_⟩
  have hbranch (j : Label) := henergy j (s j) rfl (hsupp j) (z j) (hz j) (hlen j)
    (g j).R (g j).seed (hg j).1 (hg j).2.1 (hg j).2.2.1 (hg j).2.2.2.1
    (g j).d (g j).cLog (g j).I (g j).J (g j).E (hg j).2.2.2.2.1
    (g j).K (g j).X (g j).Tsec (hg j).2.2.2.2.2.1 (hg j).2.2.2.2.2.2.1
    (hg j).2.2.2.2.2.2.2.1 (g j).H0 (hg j).2.2.2.2.2.2.2.2.1
    (hg j).2.2.2.2.2.2.2.2.2.1 (hg j).2.2.2.2.2.2.2.2.2.2
  have hh := Finset.sum_le_sum (s:=Finset.univ)
    (fun j _ => mul_le_mul_of_nonneg_left (hbranch j) (hw j))
  apply hh.trans_eq
  change (∑j,weight j*((56/_)*(_*actualMainSource (s j) (g j) Z sigma Csec ξ reserve+
    actualErrorSources (s j) (g j) Z sigma Csec ξ reserve _ (τ j))))=_
  simp_rw [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_direct_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_joint_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.normPhase_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_allocation_direct_sum
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_matched_source_amplification

open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for (root, required) in #[
      (``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_direct_sum,
        ``OAI.SevenEighths.CenteredMomentFirstReferenceSource.physicalMass_eq_sum),
      (``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_joint_sum,
        ``OAI.SevenEighths.CenteredMomentFirstReferenceSource.physicalMass_eq_sum),
      (``OAI.SevenEighths.Cycle61InitialMass.actual_common_allocation_direct_sum,
        ``OAI.SevenEighths.CenteredMomentFirstCommonSourceBudget.common_energy_live_allocations),
      (``OAI.SevenEighths.Cycle61InitialMass.actual_matched_source_amplification,
        ``OAI.SevenEighths.CenteredMomentFirstAnnularInput.eventually_input_amplification)] do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut idx := 0
    let mut denied : Array Name := #[]
    let mut missing : Array Name := #[]
    while idx < todo.size do
      let n := todo[idx]!
      idx := idx+1
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``sorryAx || #["ColumnBounds", "actual_reference_block", "original_block_sum",
          "CenteredMomentEnergyOriginalHighReflectionPower", "Cycle61Moment.InitialAffineAt",
          "Cycle61.Assembly.Final", "PositiveHighSourceBound"].any
          (fun ban => (n.toString.splitOn ban).length>1) then
        denied := denied.push n
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          if #["OAI.", "Cycle25.", "Cycle61.", "ZetaZeroFree.",
              "_private.OAI.", "_private.Cycle25.", "_private.Cycle61.",
              "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
            todo := todo.push dep
    unless seen.contains required do throwError "Genuine source dependency missing: {required}"
    logInfo m!"{root}: {seen.size} project constants; denied={denied}; missing={missing}"
    unless denied.isEmpty && missing.isEmpty do throwError "Direct-sum decomposition audit rejected"

end
/- END ORIGINAL Cycle61.Physical.InitialMass.Decomposition -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.RatioBins; sha256 a3cc8fd468e3bc6686497d1063325f771f95cb75cdec02e609ec346fe1c0c06b -/
section
                                                 
                                                                   
                                                               

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic
open Filter HeckeFamily ConcreteTraceCRT CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentFirstReferenceSource
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentFirstScale
open CenteredMomentFirstSourceConductorCaps CenteredMomentSectorLocalization
open CenteredMomentDyadicCount CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFirstPhysicalLedger
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceRow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- An exact dyadic ratio index, independent of any first-label envelope. -/
def sourceRatioIndex (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) : ℤ :=
  (q.2.2 0).val+(q.2.2 1).val-(q.2.2 2).val-(q.2.2 3).val

def sourceRatioBins (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) : Finset ℤ :=
  Finset.univ.image (sourceRatioIndex s R seed K Z ξ)

abbrev SourceRatioFiber (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) (r : ℤ) :=
  {q : FirstSourceCoordinate s R seed K Z ξ // sourceRatioIndex s R seed K Z ξ q=r}

omit [DecidableEq ι] in
lemma actual_source_ratio (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (q : FirstSourceCoordinate s R seed K Z ξ) :
    dyadicScale (q.2.2 0)*dyadicScale (q.2.2 1)/
      (dyadicScale (q.2.2 2)*dyadicScale (q.2.2 3)) =
      dyadicScale (sourceRatioIndex s R seed K Z ξ q) := by
  simp only [sourceRatioIndex,dyadicScale,zpow_sub₀ (by norm_num : (2:ℝ)≠0),
    zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  ring

omit [DecidableEq ι] in
lemma actual_source_ratio_fiber (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ)
    (r : ℤ) (q : SourceRatioFiber s R seed K Z ξ r) :
    dyadicScale (q.val.2.2 0)*dyadicScale (q.val.2.2 1)/
      (dyadicScale (q.val.2.2 2)*dyadicScale (q.val.2.2 3)) = dyadicScale r := by
  rw [actual_source_ratio,q.property]

/-- Exact physical mass as a sum of norms of full first-label ratio groups.
Every phase has norm at most one; all first labels remain inside each fiber. -/
theorem actual_physical_mass_ratio_groups (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    CenteredMomentFirstSourceReduction.physicalMass s R seed
      (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ =
    ∑r∈sourceRatioBins s R seed K Z ξ,
      ‖∑q : SourceRatioFiber s R seed K Z ξ r,
        normPhase (coordinateBlock s R seed W K Z ξ q.val)*
          coordinateBlock s R seed W K Z ξ q.val‖ := by
  rw [actual_physical_mass_joint_sum]
  simp_rw [normPhase_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  simp_rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _=>norm_nonneg _))]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun q (hq : q∈(Finset.univ : Finset (FirstSourceCoordinate s R seed K Z ξ))) =>
      Finset.mem_image_of_mem (sourceRatioIndex s R seed K Z ξ) hq)]
  apply Finset.sum_congr rfl
  intro r _
  exact (Finset.sum_subtype (Finset.univ.filter (fun q : FirstSourceCoordinate s R seed K Z ξ =>
    sourceRatioIndex s R seed K Z ξ q=r))
    (fun q => by simp) (fun q => ‖coordinateBlock s R seed W K Z ξ q‖))

omit [DecidableEq ι] in
/-- The active and inactive conductor factors give an actual common interval
for the first dyadic center, even as the first labels vary. -/
lemma actual_effective_scale_bounds (s : Input ι) (R seed : Ideal O) (K Z ξ B : ℝ)
    (hK : 0< K) (hZ : 1≤ Z) (hs : Squarefree seed) (hz₁ : s.W₁ 0=0)
    (hz₂ : s.W₂ 0=0) (hsource : sourceRadius s≤ Z^B)
    (q : FirstSourceCoordinate s R seed K Z ξ) :
    K/Z^(2*B)≤ effectiveScale q.1.val.1 q.1.val.2 q.2.1.val K ∧
      effectiveScale q.1.val.1 q.1.val.2 q.2.1.val K≤ K := by
  let C := q.1.val.1
  let D := q.1.val.2
  let E := q.2.1.val
  have hg := actual_common_gates s R seed hs hz₁ hz₂ C D q.1.property
  have hc : Supported C :=
    (CenteredMomentSecondRetainedAggregate.commonLabels_supported
      (CenteredMomentActiveSource.activeSource (CenteredMomentSourceMass.finiteColumns
        (Fintype.piFinset s.pools)) (coefficient s R seed)) _ _ q.1.property).1
  have hf := original_factor_caps C D hc E
  let e := ‖eisEmbedding (primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E)‖^2
  let r := ‖eisEmbedding (activeConductor C D)‖^2
  have he1 : 1≤ e := by
    rw [show e=((Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}).absNorm:ℝ) by
      exact eisEmbedding_norm_sq_eq_absNorm_span _]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (subsetGenerator_supported C D hc E).1)
  have hr1 : 1≤ r := by
    rw [show r=((Ideal.span {activeConductor C D}).absNorm:ℝ) by
      exact eisEmbedding_norm_sq_eq_absNorm_span _]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (finitePrimeModulus_ne_zero _)))
  have he : e≤ Z^B := hf.1.trans (hg.2.2.2.2.2.1.trans hsource)
  have hr : r≤ Z^B := hf.2.trans (hg.2.2.2.2.2.1.trans hsource)
  have hep : 0< e := zero_lt_one.trans_le he1
  have hrp : 0< r := zero_lt_one.trans_le hr1
  have hz : 0< Z := zero_lt_one.trans_le hZ
  change K/Z^(2*B)≤(K/e)/r ∧ (K/e)/r≤ K
  rw [div_div]
  constructor
  · apply div_le_div_of_nonneg_left hK.le (mul_pos hep hrp)
    have hmul := mul_le_mul he hr hrp.le (Real.rpow_nonneg hz.le _)
    simpa only [←Real.rpow_add hz,show B+B=2*B by ring] using hmul
  · exact div_le_self hK.le (one_le_mul_of_one_le_of_one_le he1 hr1)

/-- The common dyadic box contains the dyads of every actual source label.
Its size is logarithmic in scale ratios, never in the number of first labels. -/
abbrev SourceDyadicEnvelope (K Z B L : ℝ) :=
  ∀i : Fin 4,↥(indices (![K/Z^(2*B),1,1,1] i) (![K,Z^L,Z^B,Z^B] i))

omit [DecidableEq ι] in
lemma actual_dyads_in_envelope (s : Input ι) (R seed : Ideal O) (K Z ξ A D B : ℝ)
    (hK : 0< K) (hZ : 1≤ Z) (hB : 0≤ B)
    (hA : 0≤ A) (_hD : 0≤ D) (hξ : 0≤ξ)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : 0< sourceRadius s) (hsourcecap : sourceRadius s≤ Z^B)
    (hV : CenteredMomentAmplificationChildInput.volume s≤ Z^A) (hKi : K⁻¹≤ Z^D)
    (q : FirstSourceCoordinate s R seed K Z ξ) (i : Fin 4) :
    (q.2.2 i).val∈indices (![K/Z^(2*B),1,1,1] i)
      (![K,Z^(3*max A D+ξ/2),Z^B,Z^B] i) := by
  have hz : 0< Z := zero_lt_one.trans_le hZ
  have hbpow : 1≤ Z^B := Real.one_le_rpow hZ hB
  have hf := actual_effective_scale_bounds s R seed K Z ξ B hK hZ hs hz₁ hz₂ hsourcecap q
  have hg := actual_common_gates s R seed hs hz₁ hz₂ q.1.val.1 q.1.val.2 q.1.property
  have hnC : (1:ℝ)≤ q.1.val.1.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hg.1)
  have hnD : (1:ℝ)≤ q.1.val.2.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hg.2.1)
  fin_cases i
  · apply (mem_indices_iff_scale _ _ (div_pos hK (Real.rpow_pos_of_pos hz _)) hK _).mpr
    have hn := (mem_indices_iff_scale _ _
      (effectiveScale_pos _ _ _ K hK) (effectiveScale_pos _ _ _ K hK) _).mp (q.2.2 0).property
    exact ⟨hf.1.trans hn.1,hn.2.trans (by linarith [hf.2])⟩
  · have hr := local_frequency_radius_cap q.1.val.1 q.1.val.2 q.2.1.val
      K (CenteredMomentAmplificationChildInput.volume s) Z (max A D) ξ hK
      (CenteredMomentAmplificationChildInput.volume_pos s).le hZ
      (hV.trans (Real.rpow_le_rpow_of_exponent_le hZ (le_max_left _ _)))
      (hKi.trans (Real.rpow_le_rpow_of_exponent_le hZ (le_max_right _ _)))
    obtain ⟨hret,a,ha,hne⟩ := (mem_retainedIndices _ _).mp (q.2.2 1).property
    have hi := retained_integral_mem _ a ha _ hret hne
    apply indices_mono_upper _ _ _ (by norm_num) (by positivity) _ hi
    apply max_le (Real.one_le_rpow hZ (by
      have hm : 0≤ max A D := hA.trans (le_max_left _ _)
      positivity)) hr
  · exact indices_mono_upper _ _ _ (by norm_num)
      (div_pos hsource (zero_lt_one.trans_le hnC))
      ((div_le_self hsource.le hnC).trans hsourcecap) (q.2.2 2).property
  · exact indices_mono_upper _ _ _ (by norm_num)
      (div_pos hsource (zero_lt_one.trans_le hnD))
      ((div_le_self hsource.le hnD).trans hsourcecap) (q.2.2 3).property

/-- A single common four-dimensional dyadic box has a uniform small-power
size. Its first interval is centered at the one global physical scale K. -/
theorem source_dyadic_envelope_subpower (B L ε : ℝ) (hB : 0≤ B) (hL : 0≤ L)
    (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,∀K : ℝ,0< K →
      (Fintype.card (SourceDyadicEnvelope K Z B L):ℝ)≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := four_indices_subpower 1 (3*B+L) ε (by norm_num)
    (by positivity) hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hz hZ
  intro K hK
  have hp : 0< Z := zero_lt_one.trans_le hZ
  have hb : 1≤ Z^B := Real.one_le_rpow hZ hB
  have hbb : 1≤ Z^(2*B) := Real.one_le_rpow hZ (by positivity)
  have hl : 1≤ Z^L := Real.one_le_rpow hZ hL
  apply hz ![K/Z^(2*B),1,1,1] ![K,Z^L,Z^B,Z^B]
  · intro i; fin_cases i
    · change 0< K/Z^(2*B); positivity
    · change (0:ℝ)<1; norm_num
    · change (0:ℝ)<1; norm_num
    · change (0:ℝ)<1; norm_num
  · intro i; fin_cases i
    · change K/Z^(2*B)≤ K; exact div_le_self hK.le hbb
    · change 1≤ Z^L; exact hl
    · change 1≤ Z^B; exact hb
    · change 1≤ Z^B; exact hb
  · intro i; fin_cases i
    · change K/(K/Z^(2*B))≤1*Z^(3*B+L)
      have he : K/(K/Z^(2*B))=Z^(2*B) := by field_simp
      rw [he,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · change Z^L/1≤1*Z^(3*B+L)
      rw [div_one,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · change Z^B/1≤1*Z^(3*B+L)
      rw [div_one,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
    · change Z^B/1≤1*Z^(3*B+L)
      rw [div_one,one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

omit [DecidableEq ι] in
/-- Counting the image of actual dyadic tuples costs no first-label count.
The uniform box includes every original physical-mass coordinate. -/
theorem actual_ratio_bins_subpower (A D B ξ ε : ℝ)
    (hA : 0≤ A) (hD : 0≤ D) (hB : 0≤ B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ),0< K →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B →
      CenteredMomentAmplificationChildInput.volume s≤ Z^A → K⁻¹≤ Z^D →
      ((sourceRatioBins s R seed K Z ξ).card:ℝ)≤ C*Z^ε := by
  let L := 3*max A D+ξ/2
  have hL : 0≤ L := by dsimp [L]; have hm := hA.trans (le_max_left A D); positivity
  obtain ⟨C,hC,hcount⟩ := source_dyadic_envelope_subpower B L ε hB hL hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_ge_atTop (1:ℝ)] with Z hcount hZ
  intro s R seed K hK hs hz₁ hz₂ hsource hsourcecap hV hKi
  let index : SourceDyadicEnvelope K Z B L→ℤ := fun n =>
    (n 0).val+(n 1).val-(n 2).val-(n 3).val
  have hsub : sourceRatioBins s R seed K Z ξ⊆Finset.univ.image index := by
    intro r hr
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hr
    let n : SourceDyadicEnvelope K Z B L := fun i =>
      ⟨(q.2.2 i).val,actual_dyads_in_envelope s R seed K Z ξ A D B hK hZ hB
        hA hD hξ hs hz₁ hz₂ hsource hsourcecap hV hKi q i⟩
    exact Finset.mem_image.mpr ⟨n,Finset.mem_univ _,rfl⟩
  have hcard : (sourceRatioBins s R seed K Z ξ).card≤
      Fintype.card (SourceDyadicEnvelope K Z B L) :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  exact (show ((sourceRatioBins s R seed K Z ξ).card:ℝ)≤
      Fintype.card (SourceDyadicEnvelope K Z B L) by exact_mod_cast hcard).trans (hcount K hK)

omit [DecidableEq ι] in
/-- Coherent ratio loss for actual physical mass: an arbitrary natural decay
power introduces at most the same uniform small-power overhead. -/
theorem actual_ratio_decay_sum_subpower (A D B ξ ε : ℝ)
    (hA : 0≤ A) (hD : 0≤ D) (hB : 0≤ B) (hξ : 0≤ξ) (hε : 0<ε) :
    ∃C : ℝ,0< C ∧ ∀ᶠ Z : ℝ in atTop,
      ∀(s : Input ι)(R seed : Ideal O)(K : ℝ),0< K →
      Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      0< sourceRadius s → sourceRadius s≤ Z^B →
      CenteredMomentAmplificationChildInput.volume s≤ Z^A → K⁻¹≤ Z^D →
      ∀N : ℕ,∑r∈sourceRatioBins s R seed K Z ξ,(1+dyadicScale r)^(-(N:ℝ))≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := actual_ratio_bins_subpower (ι:=ι) A D B ξ ε hA hD hB hξ hε
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount] with Z hcount
  intro s R seed K hK hs hz₁ hz₂ hsource hsourcecap hV hKi N
  apply (Finset.sum_le_sum (fun r _ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [dyadicScale_pos r])
      (neg_nonpos.mpr (Nat.cast_nonneg N)))).trans
  simpa using hcount s R seed K hK hs hz₁ hz₂ hsource hsourcecap hV hKi

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_source_ratio_fiber
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_ratio_groups
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_effective_scale_bounds
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_dyads_in_envelope
#print axioms OAI.SevenEighths.Cycle61InitialMass.source_dyadic_envelope_subpower
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_ratio_bins_subpower
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_ratio_decay_sum_subpower
open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_ratio_groups,
      ``OAI.SevenEighths.Cycle61InitialMass.actual_ratio_bins_subpower,
      ``OAI.SevenEighths.Cycle61InitialMass.actual_ratio_decay_sum_subpower] do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut idx := 0
    let mut denied : Array Name := #[]
    let mut missing : Array Name := #[]
    while idx < todo.size do
      let n := todo[idx]!
      idx := idx+1
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``sorryAx || #["ColumnBounds", "actual_reference_block", "original_block_sum",
          "CenteredMomentEnergyOriginalHighReflectionPower", "Cycle61Moment.InitialAffineAt",
          "Cycle61.Assembly.Final", "PositiveHighSourceBound"].any
          (fun ban => (n.toString.splitOn ban).length>1) then
        denied := denied.push n
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          if #["OAI.", "Cycle25.", "Cycle61.", "ZetaZeroFree.",
              "_private.OAI.", "_private.Cycle25.", "_private.Cycle61.",
              "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
            todo := todo.push dep
    let required := if root == ``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_ratio_groups
      then #[``OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_joint_sum]
      else #[``OAI.SevenEighths.CenteredMomentOriginalCommonHarmonic.actual_common_gates,
        ``OAI.SevenEighths.CenteredMomentFirstSourceConductorCaps.original_factor_caps,
        ``OAI.SevenEighths.CenteredMomentFirstPhysicalDyadicCount.local_frequency_radius_cap,
        ``OAI.SevenEighths.CenteredMomentDyadicCount.four_indices_subpower]
    for n in required do
      unless seen.contains n do throwError "Genuine source ratio dependency missing: {n}"
    logInfo m!"{root}: {seen.size} project constants; denied={denied}; missing={missing}"
    unless denied.isEmpty && missing.isEmpty do throwError "Actual ratio-bin audit rejected"

end
/- END ORIGINAL Cycle61.Physical.InitialMass.RatioBins -/
