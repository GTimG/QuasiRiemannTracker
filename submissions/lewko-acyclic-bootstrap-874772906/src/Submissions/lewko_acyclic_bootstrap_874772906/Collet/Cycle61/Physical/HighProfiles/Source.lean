import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.HighProfiles.Control
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.ClippedProjectorShell
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.EligibleEnergy

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61HighProfiles
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open CenteredMomentFiniteProfileExceptional CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentHeckeHeight
open HeckeFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Only the plain functions change; the natural character, masks, slots,
scales and literal selected-divisor quotients retain their original values. -/
def scalePlains (s : Data ι) (c₀ c₁ : ℝ) : Data ι :=
  {s with
    W₁ := c₀ • s.W₁
    W₂ := c₁ • s.W₂
    support₁ := by
      intro x hx
      apply s.support₁
      intro hw
      apply hx
      simp [Pi.smul_apply,hw]
    support₂ := by
      intro x hx
      apply s.support₂
      intro hw
      apply hx
      simp [Pi.smul_apply,hw]}

omit [DecidableEq ι] in
theorem scalePlains_coefficient (s : Data ι) (c₀ c₁ : ℝ) :
    (scalePlains s c₀ c₁).coefficient=s.coefficient := rfl

omit [DecidableEq ι] in
theorem scalePlains_plain_scales (s : Data ι) (c₀ c₁ : ℝ) (second : Bool) :
    Cycle61.Physical.sourcePlainScales (scalePlains s c₀ c₁).toSource second=
      Cycle61.Physical.sourcePlainScales s.toSource second := rfl

omit [DecidableEq ι] in
theorem scalePlains_core (s : Data ι) (c₀ c₁ : ℝ) :
    (scalePlains s c₀ c₁).η=s.η ∧ (scalePlains s c₀ c₁).m=s.m ∧
    (scalePlains s c₀ c₁).A=s.A ∧ (scalePlains s c₀ c₁).t=s.t ∧
    (scalePlains s c₀ c₁).slots=s.slots ∧ (scalePlains s c₀ c₁).P=s.P ∧
    (scalePlains s c₀ c₁).X₁=s.X₁ ∧ (scalePlains s c₀ c₁).X₂=s.X₂ ∧
    (scalePlains s c₀ c₁).Y₁=s.Y₁ ∧ (scalePlains s c₀ c₁).Y₂=s.Y₂ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem scalePlains_post_scale (s : Data ι) (c₀ c₁ : ℝ) (second : Bool)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) :
    Cycle61.Physical.postPlainScale D alloc
      (Cycle61.Physical.sourcePlainScales (scalePlains s c₀ c₁).toSource second)=
    Cycle61.Physical.postPlainScale D alloc
      (Cycle61.Physical.sourcePlainScales s.toSource second) := rfl

theorem dilated_smul (W : ℝ→ℂ) (c U : ℝ) :
    dilated (c • W) U=c • dilated W U := rfl

theorem rowTwistedSum_smul (η : Character) (m A z : O)
    (W : ℝ→ℂ) (c t X : ℝ) :
    rowTwistedSum η m A z (c • W) t X=(c:ℂ)*rowTwistedSum η m A z W t X := by
  unfold rowTwistedSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro I
  simp only [Pi.smul_apply,Complex.real_smul]
  ring

omit [DecidableEq ι] in
theorem retainedPositiveRow_smul (η : Character) (m A z : O) (W₀ W₁ : ℝ→ℂ)
    (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (c₀ c₁ t X₀ X₁ : ℝ) :
    retainedPositiveRow η m A z (c₀ • W₀) (c₁ • W₁) pool β P t X₀ X₁=
      ((c₀*c₁:ℝ):ℂ)*retainedPositiveRow η m A z W₀ W₁ pool β P t X₀ X₁ := by
  unfold retainedPositiveRow
  rw [dilated_smul,dilated_smul]
  unfold positiveSlotRow
  rw [rowTwistedSum_smul,rowTwistedSum_smul]
  push_cast
  ring

theorem allocatedPositiveRow_smul (η : Character) (m A z : O) (t : ℝ)
    (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (W₀ W₁ : ℝ→ℂ) (c₀ c₁ X₀ X₁ : ℝ) :
    allocatedPositiveRow η m A z t pool β P D alloc (c₀ • W₀) (c₁ • W₁) X₀ X₁=
      ((c₀*c₁:ℝ):ℂ)*allocatedPositiveRow η m A z t pool β P D alloc W₀ W₁ X₀ X₁ := by
  unfold allocatedPositiveRow
  exact retainedPositiveRow_smul _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem sourcePositiveRow_scalePlains (s : Data ι) (c₀ c₁ : ℝ) (second : Bool)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O) :
    Cycle61.Physical.sourcePositiveRow (scalePlains s c₀ c₁).toSource second D alloc z=
      ((c₀*c₁:ℝ):ℂ)*Cycle61.Physical.sourcePositiveRow s.toSource second D alloc z := by
  unfold Cycle61.Physical.sourcePositiveRow
  exact allocatedPositiveRow_smul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

def normalizedData {a b : ℝ} (ha : 0<a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (s : Data ι) : Data ι :=
  scalePlains s (clippedControl ha S p U hU 0)⁻¹ (clippedControl ha S p U hU 1)⁻¹

omit [DecidableEq ι] in
theorem normalizedData_plains {a b : ℝ} (ha : 0<a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (s : Data ι)
    (hW₀ : s.W₁=(p.profile 0:ℝ→ℂ)) (hW₁ : s.W₂=(p.profile 1:ℝ→ℂ)) :
    (normalizedData ha S p U hU s).W₁=
        ((normalizedPlains ha S p U hU).profile 0:ℝ→ℂ) ∧
    (normalizedData ha S p U hU s).W₂=
        ((normalizedPlains ha S p U hU).profile 1:ℝ→ℂ) := by
  constructor
  · simp [normalizedData,scalePlains,normalizedPlains,hW₀]
  · simp [normalizedData,scalePlains,normalizedPlains,hW₁]

theorem sourcePositiveRow_normalized {a b : ℝ} (ha : 0<a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (hret : ∀ i,1≤U i*b)
    (s : Data ι) (hW₀ : s.W₁=(p.profile 0:ℝ→ℂ))
    (hW₁ : s.W₂=(p.profile 1:ℝ→ℂ)) (second : Bool)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O) :
    Cycle61.Physical.sourcePositiveRow s.toSource second D alloc z=
      ((clippedControl ha S p U hU 0*clippedControl ha S p U hU 1:ℝ):ℂ)*
        Cycle61.Physical.sourcePositiveRow
          (normalizedData ha S p U hU s).toSource second D alloc z := by
  have hw := normalizedData_plains ha S p U hU s hW₀ hW₁
  have he₀ : s.W₁=clippedControl ha S p U hU 0 •
      (normalizedData ha S p U hU s).W₁ := by
    rw [hW₀,hw.1]
    exact congrArg (fun W : 𝓢(ℝ,ℂ) => (W:ℝ→ℂ))
      (normalizedPlains_reconstruct ha S hS p U hU hret 0).symm
  have he₁ : s.W₂=clippedControl ha S p U hU 1 •
      (normalizedData ha S p U hU s).W₂ := by
    rw [hW₁,hw.2]
    exact congrArg (fun W : 𝓢(ℝ,ℂ) => (W:ℝ→ℂ))
      (normalizedPlains_reconstruct ha S hS p U hU hret 1).symm
  unfold Cycle61.Physical.sourcePositiveRow
  conv_lhs => rw [he₀,he₁]
  exact allocatedPositiveRow_smul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem sourcePositiveRow_normalized_norm_sq {a b : ℝ} (ha : 0<a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (hret : ∀ i,1≤U i*b)
    (s : Data ι) (hW₀ : s.W₁=(p.profile 0:ℝ→ℂ))
    (hW₁ : s.W₂=(p.profile 1:ℝ→ℂ)) (second : Bool)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O) :
    ‖Cycle61.Physical.sourcePositiveRow s.toSource second D alloc z‖^2=
      (clippedControl ha S p U hU 0*clippedControl ha S p U hU 1)^2*
        ‖Cycle61.Physical.sourcePositiveRow
          (normalizedData ha S p U hU s).toSource second D alloc z‖^2 := by
  have hc := mul_nonneg (clippedControl_nonneg ha S p U hU 0)
    (clippedControl_nonneg ha S p U hU 1)
  rw [sourcePositiveRow_normalized ha S hS p U hU hret s hW₀ hW₁ second D alloc z,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg hc,mul_pow]

theorem sourcePositiveRow_normalized_bound {a b : ℝ} (ha : 0<a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (hret : ∀ i,1≤U i*b)
    (s : Data ι) (hW₀ : s.W₁=(p.profile 0:ℝ→ℂ))
    (hW₁ : s.W₂=(p.profile 1:ℝ→ℂ)) (second : Bool)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (T : Finset (ℕ×ℕ)) (C E : ℝ) (hC : 0≤C)
    (hcontrol : clippedControl ha S p U hU 0*clippedControl ha S p U hU 1≤C*p.control T)
    (hrow : ‖Cycle61.Physical.sourcePositiveRow
      (normalizedData ha S p U hU s).toSource second D alloc z‖^2≤E) :
    ‖Cycle61.Physical.sourcePositiveRow s.toSource second D alloc z‖^2≤
      C^2*(p.control T)^2*E := by
  have hc : 0≤clippedControl ha S p U hU 0*clippedControl ha S p U hU 1 :=
    mul_nonneg (clippedControl_nonneg ha S p U hU 0) (clippedControl_nonneg ha S p U hU 1)
  rw [sourcePositiveRow_normalized ha S hS p U hU hret s hW₀ hW₁ second D alloc z,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg hc,mul_pow]
  have hs := pow_le_pow_left₀ hc hcontrol 2
  have hn := sq_nonneg (‖Cycle61.Physical.sourcePositiveRow
    (normalizedData ha S p U hU s).toSource second D alloc z‖)
  exact (mul_le_mul hs hrow hn (pow_nonneg (mul_nonneg hC (Profiles.control_nonneg p T)) 2)).trans_eq (by ring)

end
end OAI.SevenEighths.Cycle61HighProfiles
