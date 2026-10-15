/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B085
import Submissions.gao_cycle61_plane_20261013.Bundles.B094
import Submissions.gao_cycle61_plane_20261013.Bundles.B106
import Submissions.gao_cycle61_plane_20261013.Bundles.B123
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.EligibleEnergy

/- BEGIN ORIGINAL Cycle61.Physical.HighProfiles.Control; sha256 be5482bfc84566ed565d8d901a4d53a52169613f654d6527fa5076ac7e7109d9 -/
section
                                     
                                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61HighProfiles
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set CenteredMomentFiniteProfileExceptional CenteredMomentEnergyAllocatedProfiles
open CenteredMomentRetainedProfile CenteredMomentEnergyProfiles

/-- The entire Mellin budget is fixed before the moving profile and before the
high-row theorem selects its required decay order. -/
theorem fixed_mellin_budget (a b : ℝ) (ha : 0< a) :
    ∃ bound : ℕ→ℝ, (∀ k,0< bound k) ∧ ∀ n : ℕ,
      ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ W : 𝓢(ℝ,ℂ), Function.support (W:ℝ→ℂ)⊆Icc a b →
      sourceControl S W≤1 → ∀ k : ℕ, (k=2 ∨ k=n+2) →
      ∀ x ∈ Icc (-1:ℝ) 2, ∀ u : ℝ,
        (1+|u|)^k*‖mellin W ((x:ℂ)+u*Complex.I)‖≤ bound k := by
  choose R C hC hbound using fun k : ℕ =>
    CubicReflectionKernel.mellin_strip_source_bound a b ha (-1) 2 k
  refine ⟨C,hC,?_⟩
  intro n
  let S := insert (0,0) (R 2 ∪ R (n+2))
  refine ⟨S,by simp [S],?_⟩
  intro W hs hnorm k hk x hx u
  have hsub : R k⊆S := by
    rcases hk with rfl | rfl
    · exact Finset.subset_union_left.trans (Finset.subset_insert _ _)
    · exact Finset.subset_union_right.trans (Finset.subset_insert _ _)
  have hle : sourceControl (R k) W≤ sourceControl S W :=
    Seminorm.le_def.mp (Finset.sup_mono hsub) W
  exact (hbound k W hs x hx u).trans
    ((mul_le_mul_of_nonneg_left (hle.trans hnorm) (hC k).le).trans_eq (mul_one _))

theorem high_strip_mem {a e x : ℝ} (ha : a≤1) (he : e≤1/1000)
    (hx : x∈Icc (1-a-6*e) 2) : x∈Icc (-1:ℝ) 2 := by
  exact ⟨by linarith [hx.1],hx.2⟩

def clippedControl {a b : ℝ} (ha : 0< a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (i : Fin 2) : ℝ :=
  sourceControl S ((retainedPair a b ha p U hU 0).profile i)

def normalizedPlains {a b : ℝ} (ha : 0< a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0< U i) : Profiles a b where
  profile := fun i => (clippedControl ha S p U hU i)⁻¹ • p.profile i
  support := by
    intro i x hx
    apply p.support i
    intro hw
    apply hx
    simp [hw]

theorem clippedControl_nonneg {a b : ℝ} (ha : 0< a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (i : Fin 2) :
    0≤ clippedControl ha S p U hU i := sourceControl_nonneg _ _

theorem normalizedPlains_clipped {a b : ℝ} (ha : 0< a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0< U i)
    (hret : ∀ i,1≤ U i*b) (i : Fin 2) :
    dilated ((normalizedPlains ha S p U hU).profile i) (clipDilation (U i)) =
      (normalizedProfile S ((retainedPair a b ha p U hU 0).profile i):ℝ→ℂ) := by
  have he := Cycle61FinalProfiles.actual_clipped_pair a b ha p U hU hret i
  funext x
  have hx := congrFun he x
  change (clippedControl ha S p U hU i)⁻¹ • p.profile i (clipDilation (U i)*x) = _
  simp only [normalizedProfile,smul_apply,clippedControl]
  rw [hx]
  rfl

theorem dilated_injective {W V : ℝ→ℂ} {c : ℝ} (hc : c≠0)
    (he : dilated W c=dilated V c) : W=V := by
  funext x
  have h := congrFun he (x/c)
  simpa [dilated,mul_div_cancel₀ _ hc] using h

theorem normalizedPlains_reconstruct {a b : ℝ} (ha : 0< a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (hret : ∀ i,1≤ U i*b) (i : Fin 2) :
    clippedControl ha S p U hU i • (normalizedPlains ha S p U hU).profile i =
      p.profile i := by
  have he := Cycle61FinalProfiles.actual_clipped_pair a b ha p U hU hret i
  by_cases hc : clippedControl ha S p U hU i=0
  · have hz : (retainedPair a b ha p U hU 0).profile i=0 :=
      sourceControl_zero S hS _ hc
    have hd : dilated (p.profile i) (clipDilation (U i))=dilated 0 (clipDilation (U i)) := by
      rw [←he,hz]
      rfl
    have hp : p.profile i=0 := by
      apply SchwartzMap.ext
      exact congrFun (dilated_injective (by
        have := clipDilation_ge_one (U i) (hU i)
        linarith) hd)
    simp [hc,hp]
  · simp [normalizedPlains,smul_smul,hc]

/-- Each plain is normalized separately. The discarded homogeneous product is
bounded by the original pair control, with no extra power of that control. -/
theorem fixed_clipped_normalization (a b : ℝ) (ha : 0< a) :
    ∃ bound : ℕ→ℝ, (∀ k,0< bound k) ∧ ∀ n : ℕ,
      ∃ S T : Finset (ℕ×ℕ), ∃ C : ℝ, (0,0)∈S ∧ 0< C ∧
      ∀ p : Profiles a b, ∀ U : Fin 2→ℝ, ∀ hU : ∀ i,0< U i,
      (∀ i,1≤ U i*b) →
      clippedControl ha S p U hU 0*clippedControl ha S p U hU 1≤ C*p.control T ∧
      (∀ i, clippedControl ha S p U hU i •
        (normalizedPlains ha S p U hU).profile i=p.profile i) ∧
      (∀ i, Function.support (dilated ((normalizedPlains ha S p U hU).profile i)
        (clipDilation (U i)))⊆Icc (a/max 1 b) b) ∧
      (∀ i, ContDiff ℝ ∞ (dilated ((normalizedPlains ha S p U hU).profile i)
        (clipDilation (U i)))) ∧
      (∀ i k, (k=2 ∨ k=n+2) → ∀ x ∈ Icc (-1:ℝ) 2, ∀ u : ℝ,
        (1+|u|)^k*‖mellin (dilated ((normalizedPlains ha S p U hU).profile i)
          (clipDilation (U i))) ((x:ℂ)+u*Complex.I)‖≤ bound k) := by
  have ha' : 0< a/max 1 b := div_pos ha (zero_lt_one.trans_le (le_max_left _ _))
  obtain ⟨bound,hbound,hbudget⟩ := fixed_mellin_budget (a/max 1 b) b ha'
  refine ⟨bound,hbound,?_⟩
  intro n
  obtain ⟨S,hS,hmellin⟩ := hbudget n
  obtain ⟨T,C,hC,hcontrol⟩ := Cycle61FinalProfiles.clipped_pair_control a b ha S
  refine ⟨S,T,C,hS,hC,?_⟩
  intro p U hU hret
  have hsup (i : Fin 2) : Function.support
      (normalizedProfile S ((retainedPair a b ha p U hU 0).profile i):ℝ→ℂ)⊆
      Icc (a/max 1 b) b :=
    (normalizedProfile_support S _).trans ((retainedPair a b ha p U hU 0).support i)
  refine ⟨hcontrol p U hU,normalizedPlains_reconstruct ha S hS p U hU hret,?_,?_,?_⟩
  · intro i
    rw [normalizedPlains_clipped ha S p U hU hret i]
    exact hsup i
  · intro i
    exact dilated_contDiff _ (((normalizedPlains ha S p U hU).profile i).smooth ⊤) _
  · intro i k hk x hx u
    rw [normalizedPlains_clipped ha S p U hU hret i]
    exact hmellin _ (hsup i) (normalizedProfile_control S _) k hk x hx u

/-- Derivative choices and clipping at two scale-supremum steps remain under a
fixed finite control of the original pair. No moving profile enters C or R. -/
theorem two_step_pair_control (a b : ℝ) (ha : 0< a) (S : Finset (ℕ×ℕ)) :
    ∃ J : ℕ, ∃ R : Finset (ℕ×ℕ), ∃ C : ℝ, 0< C ∧
      ∀ p : Profiles a b, ∀ H : ℝ, 0≤ H →
      ∀ V : Fin 2→ Test (lower a b 2) b,
      (∀ i,Path a b ha H ⟨p.profile i,p.support i⟩ 2 (V i)) →
      sourceControl S (V 0).profile*sourceControl S (V 1).profile≤
        C*p.control R*(1+H)^(2*J) := by
  obtain ⟨J,R,C,hC,hbound⟩ := path_control a b ha 2 S
  refine ⟨J,R,C^2,sq_pos_of_pos hC,?_⟩
  intro p H hH V hpath
  have h₀ := hbound ⟨p.profile 0,p.support 0⟩ H hH (V 0) (hpath 0)
  have h₁ := hbound ⟨p.profile 1,p.support 1⟩ H hH (V 1) (hpath 1)
  have hp₀ := sourceControl_nonneg R (p.profile 0)
  exact (mul_le_mul h₀ h₁ (sourceControl_nonneg _ _) (by positivity)).trans_eq (by
    simp only [Profiles.control,show 2*J=J+J by omega,pow_add]
    ring)

end
end OAI.SevenEighths.Cycle61HighProfiles

end
/- END ORIGINAL Cycle61.Physical.HighProfiles.Control -/

/- BEGIN ORIGINAL Cycle61.Physical.HighProfiles.Source; sha256 fffa548f083e31c8c25eac20546dd532052b94be948af723ea57b3d598da9704 -/
section
                                            
                                             
                                                         

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
    (pool : ι→ Finset (Ideal O)) (β : ι→ Ideal O→ℂ) (P : ι→ℝ)
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
    (pool : ι→ Finset (Ideal O)) (β : ι→ Ideal O→ℂ) (P : ι→ℝ)
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

def normalizedData {a b : ℝ} (ha : 0< a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (s : Data ι) : Data ι :=
  scalePlains s (clippedControl ha S p U hU 0)⁻¹ (clippedControl ha S p U hU 1)⁻¹

omit [DecidableEq ι] in
theorem normalizedData_plains {a b : ℝ} (ha : 0< a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (s : Data ι)
    (hW₀ : s.W₁=(p.profile 0:ℝ→ℂ)) (hW₁ : s.W₂=(p.profile 1:ℝ→ℂ)) :
    (normalizedData ha S p U hU s).W₁=
        ((normalizedPlains ha S p U hU).profile 0:ℝ→ℂ) ∧
    (normalizedData ha S p U hU s).W₂=
        ((normalizedPlains ha S p U hU).profile 1:ℝ→ℂ) := by
  constructor
  · simp [normalizedData,scalePlains,normalizedPlains,hW₀]
  · simp [normalizedData,scalePlains,normalizedPlains,hW₁]

theorem sourcePositiveRow_normalized {a b : ℝ} (ha : 0< a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (hret : ∀ i,1≤ U i*b)
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

theorem sourcePositiveRow_normalized_norm_sq {a b : ℝ} (ha : 0< a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (hret : ∀ i,1≤ U i*b)
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

theorem sourcePositiveRow_normalized_bound {a b : ℝ} (ha : 0< a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0< U i) (hret : ∀ i,1≤ U i*b)
    (s : Data ι) (hW₀ : s.W₁=(p.profile 0:ℝ→ℂ))
    (hW₁ : s.W₂=(p.profile 1:ℝ→ℂ)) (second : Bool)
    (D : Ideal O) (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (T : Finset (ℕ×ℕ)) (C E : ℝ) (hC : 0≤ C)
    (hcontrol : clippedControl ha S p U hU 0*clippedControl ha S p U hU 1≤ C*p.control T)
    (hrow : ‖Cycle61.Physical.sourcePositiveRow
      (normalizedData ha S p U hU s).toSource second D alloc z‖^2≤ E) :
    ‖Cycle61.Physical.sourcePositiveRow s.toSource second D alloc z‖^2≤
      C^2*(p.control T)^2*E := by
  have hc : 0≤ clippedControl ha S p U hU 0*clippedControl ha S p U hU 1 :=
    mul_nonneg (clippedControl_nonneg ha S p U hU 0) (clippedControl_nonneg ha S p U hU 1)
  rw [sourcePositiveRow_normalized ha S hS p U hU hret s hW₀ hW₁ second D alloc z,
    norm_mul,Complex.norm_real,Real.norm_of_nonneg hc,mul_pow]
  have hs := pow_le_pow_left₀ hc hcontrol 2
  have hn := sq_nonneg (‖Cycle61.Physical.sourcePositiveRow
    (normalizedData ha S p U hU s).toSource second D alloc z‖)
  exact (mul_le_mul hs hrow hn (pow_nonneg (mul_nonneg hC (Profiles.control_nonneg p T)) 2)).trans_eq (by ring)

end
end OAI.SevenEighths.Cycle61HighProfiles

end
/- END ORIGINAL Cycle61.Physical.HighProfiles.Source -/

/- BEGIN ORIGINAL Cycle61.Moment.ProfileHighEnergy; sha256 e8d8facdcb4125181fa5f93268c8fb01c319788223d0f6d0243e7fbe535252e0 -/
section
                                      
                                           

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open Cycle61HighProfiles LocalMoment ProbePhysical IdealMobiusDivisorSum CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Separate normalization of the two literal plain profiles restores a
single squared original profile control, after the actual high-row estimate. -/
theorem actual_profile_high_source_datum (P : HighSourceParameters) (N : ℕ)
    {ap bp : ℝ} (hap : 0 < ap) (S : Finset (ℕ × ℕ)) (hS : (0,0) ∈ S)
    (T : Finset (ℕ × ℕ)) (Cprofile : ℝ) (hCprofile : 0 < Cprofile) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character,
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ a : ℝ, 51/100 ≤ a → a ≤ 1 →
      ∀ i : ℕ, ∀ {Dict : Type*} [Fintype Dict]
        (D : HighSourceDatum M H P η₀ Z Dict),
      HighSourceAdmissible hH P η₀ Z a i n D →
      ∀ (p : Profiles ap bp) (U : Fin 2 → ℝ) (hU : ∀ j, 0 < U j),
      (∀ j, 1 ≤ U j * bp) → ∀ s : Data D.Slot,
      s.W₁ = (p.profile 0 : ℝ → ℂ) → s.W₂ = (p.profile 1 : ℝ → ℂ) →
      D.source = normalizedData hap S p U hU s →
      clippedControl hap S p U hU 0 * clippedControl hap S p U hU 1 ≤
        Cprofile * p.control T → ∀ E : ℝ,
      D.total P ≤ E → D.liveCard P ≤ N →
      ‖Cycle61.Physical.sourcePositiveRow s.toSource D.second
          D.projector D.allocation D.z‖^2 ≤
        C * (p.control T)^2 *
          Z^((2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hactual⟩ := actual_high_source_datum M H hH P
  let K := Cp^2 * (max 1 Cs)^N
  have hK : 0 < K := mul_pos (sq_pos_of_pos hCp)
    (pow_pos (zero_lt_one.trans_le (le_max_left 1 Cs)) _)
  refine ⟨n,Cprofile^2*K,mul_pos (sq_pos_of_pos hCprofile) hK,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i Dict _ D hD p U hU hret s hW₀ hW₁ hsource hcontrol E hE hN
  have ha₂ : 1/2 ≤ a := by linarith
  have hrow := high_source_datum_cap M H P hZ.1.le hCs.le ha₂
    (hZ.2 a ha ha' i D hD) hE hN
  have hnormalized : ‖Cycle61.Physical.sourcePositiveRow
      (normalizedData hap S p U hU s).toSource D.second
      D.projector D.allocation D.z‖^2 ≤
      K * Z^((2*a-1)*E+2*P.εplain*P.d+2*P.εslot*P.d*N) := by
    simpa only [HighSourceDatum.row,hsource] using hrow
  exact (sourcePositiveRow_normalized_bound hap S hS p U hU hret s hW₀ hW₁
    D.second D.projector D.allocation D.z T Cprofile _ hCprofile.le hcontrol
    hnormalized).trans_eq (by dsimp only [K]; ring)

theorem actual_profile_joint_high_energy {Base Family : Type*} [Fintype Base] [Fintype Family]
    (base : Base → Character) (B Q loss : ℝ) (N : ℕ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B) (hloss : 0 < loss)
    {ap bp : ℝ} (hap : 0 < ap) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ η₀ : Character, ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a E : ℝ) (i : ℕ), q ≤ Q → 33/40 ≤ a → a ≤ 7/8 →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ D : NonzeroJointSourceLabel left u₀ unit → HighSourceDatum M H P η₀ Z Family,
      ∀ dictionary : NonzeroJointSourceLabel left u₀ unit → Family → Base,
      ∀ puncture : NonzeroJointSourceLabel left u₀ unit → Family → Ideal O,
      (∀ l ∈ labels, HighSourceAdmissible hH P η₀ Z a i n (D l)) →
      (∀ l ∈ labels, (D l).total P ≤ E ∧ (D l).liveCard P ≤ N) →
      (∀ l ∈ labels, ∀ j, ∀ I : Ideal O, idealCoeff ((D l).character j) I =
        idealCoeff (CenteredMomentNaturalRowSource.excluded
          (CenteredMomentNaturalRowSource.naturalRow (base (dictionary l j))
          (nonzeroJointSourceRow l).val (nonzeroJointSourceRow l).property).character
            (puncture l j)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum (D l).character (D l).hcharacter
          (3*(i+1 : ℕ)*Z^P.τ)) →
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
      ∀ (S T : Finset (ℕ × ℕ)), (0,0) ∈ S →
      ∀ (p₀ : Profiles ap bp) (p : NonzeroJointSourceLabel left u₀ unit → Profiles ap bp)
        (U : NonzeroJointSourceLabel left u₀ unit → Fin 2 → ℝ)
        (hU : ∀ l j, 0 < U l j),
      (∀ l ∈ labels, ∀ j, 1 ≤ U l j * bp) →
      ∀ s : ∀ l, Data (D l).Slot,
      (∀ l ∈ labels, (s l).W₁ = ((p l).profile 0 : ℝ → ℂ) ∧
        (s l).W₂ = ((p l).profile 1 : ℝ → ℂ)) →
      (∀ l ∈ labels, (D l).source = normalizedData hap S (p l) (U l) (hU l) (s l)) →
      ∀ Cprofile : ℝ, 0 ≤ Cprofile →
      (∀ l ∈ labels, clippedControl hap S (p l) (U l) (hU l) 0 *
        clippedControl hap S (p l) (U l) (hU l) 1 ≤ Cprofile * p₀.control T) →
      (∑ l ∈ labels, ‖Cycle61.Physical.sourcePositiveRow (s l).toSource
        (D l).second (D l).projector (D l).allocation (D l).z‖^2) ≤
        C*Cprofile^2*(p₀.control T)^2*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
          Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
            2*P.εplain*P.d+2*P.εslot*P.d*N) := by
  obtain ⟨J,hjoint⟩ := actual_joint_high_source_energy (Family := Family)
    M H hH base B Q loss N hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,C,hC,hactual⟩ := hjoint P
  refine ⟨n,C,hC,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro left u₀ unit q m a E i hq ha ha' labels D dictionary puncture
    hvalid hsize hmask hzero hnonzero heq hsupport hnorm hmissing
    S T hS p₀ p U hU hret s hW hsource Cprofile hCp hcontrol
  have hsum := hZ.2 left u₀ unit q m a E i hq ha ha' labels D dictionary puncture
    hvalid hsize hmask hzero hnonzero heq hsupport hnorm hmissing
  have hpoint : ∀ l ∈ labels,
      ‖Cycle61.Physical.sourcePositiveRow (s l).toSource (D l).second
          (D l).projector (D l).allocation (D l).z‖^2 ≤
        Cprofile^2*(p₀.control T)^2*‖(D l).row P‖^2 := by
    intro l hl
    have hc := mul_nonneg (clippedControl_nonneg hap S (p l) (U l) (hU l) 0)
      (clippedControl_nonneg hap S (p l) (U l) (hU l) 1)
    rw [sourcePositiveRow_normalized hap S hS (p l) (U l) (hU l)
      (hret l hl) (s l) (hW l hl).1 (hW l hl).2,
      ←hsource l hl, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc, mul_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc (hcontrol l hl) 2)
      (sq_nonneg _)).trans_eq (by unfold HighSourceDatum.row; ring)
  calc
    _ ≤ ∑ l ∈ labels, Cprofile^2*(p₀.control T)^2*‖(D l).row P‖^2 :=
      Finset.sum_le_sum hpoint
    _ = (Cprofile^2*(p₀.control T)^2) * ∑ l ∈ labels, ‖(D l).row P‖^2 := by
      rw [Finset.mul_sum]
    _ ≤ (Cprofile^2*(p₀.control T)^2) *
        (C*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
          Z^(m+q*unmarkedDensity (2*a-1)+loss+(2*a-1)*E+
            2*P.εplain*P.d+2*P.εslot*P.d*N)) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

#print axioms actual_profile_joint_high_energy
#print axioms actual_profile_high_source_datum
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.ProfileHighEnergy -/

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.Payment; sha256 83d5da3eb0ff1f998ecaa6679ac8284353c57dfd7ea9f8b128d20609ec19bcad -/
section
                                    

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcreteTraceCRT CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O

/-- Adding the literal radial support does not change the actual energy.
This permits conductor control without bounding all elements of `keep`. -/
theorem energy_support_restriction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ)
    (pool : ι → Finset (Ideal O)) (coeff : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (keep low : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy χ m A t W₁ W₂ pool coeff P X₁ X₂ (fun z => keep z ∧ low z) Φ K =
    energy χ m A t W₁ W₂ pool coeff P X₁ X₂
      (fun z => keep z ∧ (Φ (‖eisEmbedding z‖^2/K) ≠ 0 ∧ low z)) Φ K := by
  unfold energy
  apply tsum_congr
  intro z
  by_cases hp : Φ (‖eisEmbedding z‖^2/K) = 0
  · simp [hp]
  · by_cases hk : keep z <;> by_cases hl : low z <;> simp [hp,hk,hl]

/-- The actual child width may be below the nominal width. The joint width
and deletion payment retains that deficit and leaves the exact low reserve. -/
theorem paid_low_exponent
    {b M width δ total padding εold buffer mesh : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hwidth : width-M ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-M ≤ M*Cycle61.Arithmetic.g b+6*(M*Cycle61.Arithmetic.amp b)+padding) :
    width+εold+buffer+(2*Cycle61.Arithmetic.q0/9)*max (total-width) 0+
        Cycle61.Arithmetic.q0*mesh ≤
      M+δ+M*Cycle61.Arithmetic.amp b-M*(1/3750000)+εold+buffer+
        (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh := by
  have hbnd := Cycle61.Physical.low_paid_excess_bound hb hM hwidth hδ hpad htotal
  have hid : total-M-(width-M) = total-width := by ring
  rw [hid] at hbnd
  linarith

/-- The second-transform nominal width is distinct from the original row
width which pays the amplifier and low reserve. Both are retained explicitly. -/
theorem paid_low_exponent_shifted
    {b M nominal width δ total padding εold buffer mesh : ℝ}
    (hb : 3401/100000 ≤ b ∧ b ≤ 1/25) (hM : 0 ≤ M)
    (hwidth : width-nominal ≤ δ) (hδ : 0 ≤ δ) (hpad : 0 ≤ padding)
    (htotal : total-nominal ≤ M*Cycle61.Arithmetic.g b+6*(M*Cycle61.Arithmetic.amp b)+padding) :
    width+εold+buffer+(2*Cycle61.Arithmetic.q0/9)*max (total-width) 0+
        Cycle61.Arithmetic.q0*mesh ≤
      nominal+δ+M*Cycle61.Arithmetic.amp b-M*(1/3750000)+εold+buffer+
        (2*Cycle61.Arithmetic.q0/9)*padding+Cycle61.Arithmetic.q0*mesh := by
  have hbnd := Cycle61.Physical.low_paid_excess_bound hb hM hwidth hδ hpad htotal
  have hid : total-nominal-(width-nominal) = total-width := by ring
  rw [hid] at hbnd
  linarith

/-- The squared slot buffer can be made arbitrarily small after the finite
slot count is fixed. All three positive prime-estimate parameters are chosen
before live rows and heights. -/
theorem exists_buffer_parameters (N : ℕ) (d Rwidth error : ℝ)
    (hd : 0 < d) (hRw : 0 ≤ Rwidth) (he : 0 < error) :
    ∃ ε e κ : ℝ, 0 < ε ∧ 0 < e ∧ e < 1/1000 ∧ 0 < κ ∧
      8*e*Rwidth+κ ≤ ε ∧ 2*ε*d*(N:ℝ) ≤ error := by
  let ε := error/(4*d*((N:ℝ)+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let e := min (ε/(32*(Rwidth+1))) (1/2000)
  have he0 : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e < 1/1000 := (min_le_right _ _).trans_lt (by norm_num)
  have hecap : e*(32*(Rwidth+1)) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  have hbudget : 8*e*Rwidth+ε/2 ≤ ε := by
    have hen : 0 ≤ e := he0.le
    nlinarith
  refine ⟨ε,e,ε/2,hε,he0,he1,by positivity,hbudget,?_⟩
  have hid : ε*(4*d*((N:ℝ)+1)) = error := div_mul_cancel₀ error (by positivity)
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

/-- Move the finite slot buffer out of the constant and into its exact source
exponent; the remaining factor is fixed before the live base. -/
theorem buffer_power_identity (C Z ε d : ℝ) (N : ℕ) (hZ : 0 < Z) :
    (C*Z^(2*ε*d))^N = C^N*Z^(2*ε*d*(N:ℝ)) := by
  rw [mul_pow, ← Real.rpow_natCast (Z^(2*ε*d)) N, ← Real.rpow_mul hZ.le]

#print axioms energy_support_restriction
#print axioms paid_low_exponent
#print axioms exists_buffer_parameters
#print axioms buffer_power_identity
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.Payment -/
