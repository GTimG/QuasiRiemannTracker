/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Balanced physical first block at the true independently colored source. -/
import Candidate.C092.transport.TwistedRawBallBlock
import Submissions.sil_density_split_20261026.CubeFree.First.RawSidesBlock
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion ActualEisensteinCubic
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentFirstColumns CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentSecondWindowBudget CenteredMomentLogDyadic CenteredMomentFirstMixedAllowance
open CenteredMomentFirstMixedRoot CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstPhysicalSourceSupport CenteredMomentRankinRadical CenteredMomentFirstCanonicalFamily
open CenteredMomentSourceLowerSupport
open CenteredMomentLattice CenteredMomentTwist CenteredMomentSourceProfileMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedFirstAveragedWindow MixedFirstPhysicalApplication
open MixedFirstPhysicalBudget MixedFirstCommonSum MixedInnerExceptionalBlock
open MixedFirstExceptionalNormalization RepairedFirstRawSides RepairedFirstRawScalar
open QRH.SilDensitySplit.CubeFree.Second.Concrete
open QRH.SilDensitySplit.CubeFree.First
open QRH.Cycle092.TwistedRawSource
open QRH.Record1252270103KernelMass (pairNorm pairNorm_pos)
open CenteredMomentHeckeExpansion
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}
theorem source_coefficient_lower (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (seed I : Id)
    (hI : sourceColumn s ha ω₁ ω₂ seed I≠0) :
    (a^2/pairNorm s.d)*sourceVolume s≤(I.absNorm:ℝ) := by
  unfold sourceColumn at hI
  obtain ⟨v,hv,hv0,hvI⟩ := CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness _ _ I hI
  have hs₁ := (normPowerProfile_support s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁).trans s.hs₁
  have hs₂ := (normPowerProfile_support s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂).trans s.hs₂
  have hl := profile_product_lower s.R s.ν s.Wslot s.P (fun _=>(1:ℝ))
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
    a a s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.d.1 s.d.2 seed
    (fun i=>zero_lt_one.trans_le (s.hP i)) (fun _=>zero_le_one) ha.le ha.le
    (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂) (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂)
    s.hd.1 s.hd.2 rfl (s.hpY.trans s.hpX.symm)
    (fun i x hx=>(s.hW i hx).1) (fun x hx=>(hs₁ hx).1) (fun x hx=>(hs₂ hx).1)
    v (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hv0).1).2
  simp only [Finset.prod_const_one,one_mul,hvI] at hl
  convert hl using 1 <;> unfold sourceVolume pairNorm <;> ring

theorem actual_source_reference_pair (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ)
    (seed : Id) (η : Character) (m A : O) (t : ℝ)
    (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) (F : FixedPair η C D hC E ξ₁ ξ₂)
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (U : Fin 4→ℝ→ℂ)
    (K K₀ H₀ A₀ B₀ M Z EL ER : ℝ)
    (hK : 0<K) (hA : 0<A₀) (hB : 0<B₀) (hZ : 1<Z)
    (hEL : 0≤EL) (hER : 0≤ER) (hwin : ∀i y,U i y≠0→|y|≤M)
    (hn : block η m A t (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)
      C D hC hD E rows W U K K₀ H₀ A₀ B₀≠0) :
    ‖scalar C D hC E K A₀ B₀‖/sourceVolume s*
      Real.sqrt (((F.left.modulus.absNorm:ℝ)*(sourceVolume s/(C.absNorm:ℝ))^2*
        Z^(allowance C D Z)*EL)*
        ((F.right.modulus.absNorm:ℝ)*(sourceVolume s/(D.absNorm:ℝ))^2*
        Z^(allowance D C Z)*ER))≤
      ‖inactiveWeight C D E‖*(Real.exp M/(a^2/pairNorm s.d))*fixedPresentationCost*K*
        (η.modulus.absNorm:ℝ)/(commonRadical C D).absNorm*Real.sqrt (EL*ER) := by
  have ha' : 0<a^2/pairNorm s.d := div_pos (sq_pos_of_pos ha) (pairNorm_pos s.hd.1 s.hd.2)
  obtain ⟨hl,hr⟩ := block_reference_lower η m A t (sourceColumns s) (sourceColumn s ha ω₁ ω₂ seed)
    C D hC hD E rows W U K K₀ H₀ A₀ B₀ (a^2/pairNorm s.d) (sourceVolume s) M
    hA hB (fun I hI=>source_coefficient_lower s ha ω₁ ω₂ seed I hI) hwin hn
  exact actual_fixed_reference_pair C D hC hD hCD E η ξ₁ ξ₂ F
    K A₀ B₀ (a^2/pairNorm s.d) (sourceVolume s) M Z EL ER
    hK hA hB ha' (sourceVolume_pos s) hZ hEL hER hl hr
/-- The paired reference theorem is used on the ACTUAL first block.
Its two allowances are not removed separately. Nu^-1 occurs on both
sides and remains Nu^-1 after the square root. -/
theorem window_pair_reference (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ)
    (η : Character) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D) (E : Finset (CommonIndex C D))
    (χ ξ : RayCharacter) (rows : Finset O) (Φ : 𝓢(ℝ,ℂ))
    (K K₀ H₀ A₀ B₀ Z A loss : ℝ) (hK : 0 < K) (hA₀ : 0 < A₀) (hB₀ : 0 < B₀)
    (hZ : 1 < Z) (hA : 0 ≤ A) (u : Id) (J : ℕ)
    (hne : block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s) (sourceColumn s ha ω₁ ω₂ 1)
      C D hC hD E rows Φ (fun _ => logAnnulus) K K₀ H₀ A₀ B₀≠0) :
    let F := fixedPair η C D hC E χ (ξ⁻¹)
    (‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
      (windowBudget J t (sideBudget s F.left C D u A Z loss)*
        windowBudget J t (sideBudget s F.right D C u A Z loss)) ≤
      referencePrefactor s η C D E K (Real.log 4)*(windowMass J t)^2*
        (A*Z^loss/(u.absNorm:ℝ)) := by
  intro F
  let cost := A*Z^loss/(u.absNorm:ℝ)
  have hc : 0 ≤ cost := div_nonneg (mul_nonneg hA (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) (Nat.cast_nonneg _)
  have hwin : ∀i y,(fun _ : Fin 4 => logAnnulus) i y≠0 → |y| ≤ Real.log 4 := by
    intro i y hy
    have hh := logAnnulus_support hy
    exact abs_le.mpr ⟨hh.1,hh.2.trans (Real.log_nonneg (by norm_num))⟩
  have hp := actual_source_reference_pair s ha ω₁ ω₂ 1 η (fixedBadMask*idealGenerator s.R) 1 t
    C D hC hD hCD E χ (ξ⁻¹) F rows Φ (fun _ => logAnnulus)
    K K₀ H₀ A₀ B₀ (Real.log 4) Z cost cost hK hA₀ hB₀ hZ hc hc hwin hne
  have hl : 0 ≤ sideBudget s F.left C D u A Z loss := sideBudget_nonneg _ _ _ _ _ _ _ _ hA (zero_lt_one.trans hZ).le
  have hprod : windowBudget J t (sideBudget s F.left C D u A Z loss)*
      windowBudget J t (sideBudget s F.right D C u A Z loss)=
      Real.sqrt (sideBudget s F.left C D u A Z loss*sideBudget s F.right D C u A Z loss)*
        (windowMass J t)^2 := by
    rw [Real.sqrt_mul hl]
    unfold windowBudget windowMass
    ring
  rw [hprod]
  have hroot : Real.sqrt (cost*cost)=cost := by
    rw [←pow_two,Real.sqrt_sq_eq_abs,abs_of_nonneg hc]
  rw [hroot] at hp
  change (‖scalar C D hC E K A₀ B₀‖/sourceVolume s)*
      Real.sqrt ((reference F.left C D (sourceVolume s) Z*cost)*
        (reference F.right D C (sourceVolume s) Z*cost)) ≤
      referencePrefactor s η C D E K (Real.log 4)*cost at hp
  have hleft : sideBudget s F.left C D u A Z loss=reference F.left C D (sourceVolume s) Z*cost := by
    unfold sideBudget
    dsimp only [cost]
    ring
  have hright : sideBudget s F.right D C u A Z loss=reference F.right D C (sourceVolume s) Z*cost := by
    unfold sideBudget
    dsimp only [cost]
    ring
  rw [hleft,hright]
  convert mul_le_mul_of_nonneg_right hp (sq_nonneg (windowMass J t)) using 1 <;>
    dsimp only [cost] <;> ring
private theorem norm_ne (I : Id) (hI : I≠0) : (I.absNorm:ℝ)≠0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem summed_kernel_balanced (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0<a, ∀ω₁ ω₂ : Id→ℂ,
    ∀ (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D)),
    ∀ (Us : Finset Id) (τL τR : Character) (t K K₀ H₀ A₀ B₀ KL KR : ℝ),
      0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR →
    ∀ rows : Finset O, (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL) →
      (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR) →
    ∀ EL ER l : ℝ, 0 ≤ EL → 0 ≤ ER → 0 < l →
    (∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ D C hC u τL v KL ≤ (l*EL)*(1+‖v‖)^(2*J)) →
    (∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha ω₁ ω₂ C D hD u τR v KR ≤ (ER/l)*(1+‖v‖)^(2*J)) →
      ‖summedMatrix s ha ω₁ ω₂ C D hC hD E Us τL τR t rows Φ K K₀ H₀ A₀ B₀‖ ≤
        Ckernel*(windowBudget J t EL*windowBudget J t ER) := by
  obtain ⟨Ckernel, hC0, hker⟩ := summed_kernel_from_raw (ι := ι) (a := a) (b := b) Φ J
  refine ⟨Ckernel, hC0, ?_⟩
  intro s ha ω₁ ω₂ C D hC hD E Us τL τR t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows hrL hrR
    EL ER l hEL hER hl h1 h2
  have h := hker s ha ω₁ ω₂ C D hC hD E Us τL τR t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows
    hrL hrR (l*EL) (ER/l) (mul_nonneg hl.le hEL) (div_nonneg hER hl.le) h1 h2
  rwa [windowBudget_balance J t EL ER l hl hEL] at h

def BalancedSummedRawSideBounds (s : Source ι a b) (ha : 0<a) (ω₁ ω₂ : Id→ℂ) (η : Character)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (KL KR A Z loss : ℝ) (J : ℕ) : Prop :=
  SummedRawSideBounds (concreteArtificial s C D hD.1)
    (rawEnergy s ha ω₁ ω₂ D C hC) (rawEnergy s ha ω₁ ω₂ C D hD)
    (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).left)
    (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).right)
    (fun τ => balancedBudget s τ C D A Z loss) (fun τ => balancedBudget s τ D C A Z loss) KL KR J

/-- **The balanced Seam 0 feeds the joint kernel with the original right-hand side**: for
every pair of ray characters, the summed matrix is bounded by
`Ckernel · windowBudget(jointBudget_C) · windowBudget(jointBudget_D)`, exactly the bound the
per-side Seam 0 would give. -/
theorem balanced_kernel (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0<a, ∀ω₁ ω₂ : Id→ℂ, ∀ η : Character,
    ∀ (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D)),
    ∀ (t K K₀ H₀ A₀ B₀ KL KR A Z loss : ℝ),
      0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR → 0 ≤ A → 0 ≤ Z →
    ∀ rows : Finset O, (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL) →
      (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR) →
    BalancedSummedRawSideBounds s ha ω₁ ω₂ η C D hC hD E KL KR A Z loss J →
    ∀ χ ξ : RayCharacter,
      ‖summedMatrix s ha ω₁ ω₂ C D hC hD E (concreteArtificial s C D hD.1)
          (fixedPair η C D hC E χ (ξ⁻¹)).left (fixedPair η C D hC E χ (ξ⁻¹)).right
          t rows Φ K K₀ H₀ A₀ B₀‖ ≤
        Ckernel*(windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss) *
          windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss)) := by
  obtain ⟨Ckernel, hC0, hker⟩ := summed_kernel_balanced (ι := ι) (a := a) (b := b) Φ J
  refine ⟨Ckernel, hC0, ?_⟩
  intro s ha ω₁ ω₂ η C D hC hD E t K K₀ H₀ A₀ B₀ KL KR A Z loss hK₀ hH₀ hA₀ hB₀ hKL hKR hA hZ rows
    hrL hrR hbal χ ξ
  obtain ⟨h1, h2⟩ := hbal χ ξ
  have hCn : 0 < (C.absNorm:ℝ) :=
    lt_of_le_of_ne (Nat.cast_nonneg _) (norm_ne C hC.1).symm
  have hDn : 0 < (D.absNorm:ℝ) :=
    lt_of_le_of_ne (Nat.cast_nonneg _) (norm_ne D hD.1).symm
  have hl : 0 < (C.absNorm:ℝ)/(D.absNorm:ℝ) := div_pos hCn hDn
  refine hker s ha ω₁ ω₂ C D hC hD E _ _ _ t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows hrL hrR
    _ _ _ (concreteJointBudget_nonneg _ _ _ _ _ _ _ hA hZ)
    (concreteJointBudget_nonneg _ _ _ _ _ _ _ hA hZ) hl (fun v => ?_) (fun v => ?_)
  · rw [balanced_left_eq s _ C D hC.1 hD.1]; exact h1 v
  · rw [balanced_right_eq s _ C D hC.1 hD.1]; exact h2 v
set_option maxHeartbeats 1400000 in
/-- **Balanced Seam 0 at block level** (design `block_of_summed_raw_sides`): the same
right-hand side as FP `block_of_raw_sides` WITHOUT the artificial-divisor mass. -/
theorem block_of_summed_raw_sides (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0<a, ∀ω₁ ω₂ : Id→ℂ, s.d = (1,1) →
    ∀ (η : Character) (t : ℝ) (C D : Id) (hC : Supported C) (hD : Supported D),
    CompletedGauss.primeSupport C = CompletedGauss.primeSupport D →
    ∀ E : Finset (CommonIndex C D), ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0) →
    ∀ K K₀ H₀ A₀ B₀ KL KR Z A loss : ℝ,
      0 < K → 0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR → 1 < Z → 0 ≤ A →
      (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL) → (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR) →
      BalancedSummedRawSideBounds s ha ω₁ ω₂ η C D hC hD E KL KR A Z loss J →
    ‖blockTerm s ha ω₁ ω₂ η t C D hC hD E rows Φ K K₀ H₀ A₀ B₀‖/sourceVolume s ≤
      (256*Ckernel*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*
        (windowMass J t)^2*A*Z^loss)*commonWeight C D E := by
  obtain ⟨Ckernel, hCkernel, hkernel⟩ := balanced_kernel (ι := ι) (a := a) (b := b) Φ J
  refine ⟨Ckernel, hCkernel, ?_⟩
  intro s ha ω₁ ω₂ hunit η t C D hC hD hCD E rows hrows K K₀ H₀ A₀ B₀ KL KR Z A loss
    hK hK₀ hH₀ hA₀ hB₀ hKL hKR hZ hA hrowsL hrowsR hside
  have hz : 0 < Z := zero_lt_one.trans hZ
  let pref := referencePrefactor s η C D E K (Real.log 4)
  let H := Ckernel*(pref*(windowMass J t)^2*(A*Z^loss/((1:Id).absNorm:ℝ)))
  let r := ‖scalar C D hC E K A₀ B₀‖/sourceVolume s
  let phase := activeRow C D hC (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
  let Us := concreteArtificial s C D hD.1
  let mat := fun (χ ξ : RayCharacter) => summedMatrix s ha ω₁ ω₂ C D hC hD E Us
    (fixedPair η C D hC E χ (ξ⁻¹)).left (fixedPair η C D hC E χ (ξ⁻¹)).right
    t rows Φ K K₀ H₀ A₀ B₀
  have hr : 0 ≤ r := div_nonneg (norm_nonneg _) (sourceVolume_pos s).le
  have hpref : 0 ≤ pref := referencePrefactor_nonneg s η C D E K (Real.log 4) hK.le
  have hphase : ‖phase‖ ≤ 1 := QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ _
  have hheight : ‖commonHeight s η t C D‖ ≤ 1 := by
    rw [commonHeight, norm_mul, norm_star]
    exact (mul_le_mul (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η
        (fixedBadMask*idealGenerator s.R) 1 1 t C hC.1)
      (CenteredMomentFirstTailAggregate.rowWeight_norm_le_one η
        (fixedBadMask*idealGenerator s.R) 1 1 t D hD.1)
      (norm_nonneg _) zero_le_one).trans_eq (by ring)
  have hRHS : 0 ≤ (256*Ckernel*(4/a^2)*fixedPresentationCost*((η.modulus.absNorm:ℝ)*K)*
      (windowMass J t)^2*A*Z^loss)*commonWeight C D E := by
    have hw := common_weight_nonneg C D E
    have hf := fixedPresentationCost_pos
    positivity
  by_cases hzero : block η (fixedBadMask*idealGenerator s.R) 1 t (sourceColumns s)
      (sourceColumn s ha ω₁ ω₂ 1) C D hC hD E rows Φ (fun _ => logAnnulus) K K₀ H₀ A₀ B₀ = 0
  · simp only [blockTerm, hzero, mul_zero, norm_zero, zero_div]
    exact hRHS
  have hmat : ∀ χ ξ, r*‖mat χ ξ‖ ≤ H := by
    intro χ ξ
    have hk := hkernel s ha ω₁ ω₂ η C D hC hD E t K K₀ H₀ A₀ B₀ KL KR A Z loss hK₀ hH₀ hA₀ hB₀ hKL hKR
      hA hz.le rows hrowsL hrowsR hside χ ξ
    have hnorm := window_pair_reference s ha ω₁ ω₂ η t C D hC hD hCD E χ ξ rows Φ
      K K₀ H₀ A₀ B₀ Z A loss hK hA₀ hB₀ hZ hA 1 J hzero
    simp only [sideBudget_one] at hnorm
    calc
      r*‖mat χ ξ‖ ≤ r*(Ckernel*(windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss)*
          windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss))) :=
        mul_le_mul_of_nonneg_left hk hr
      _ = Ckernel*(r*(windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss)*
          windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss))) := by ring
      _ ≤ H := mul_le_mul_of_nonneg_left hnorm hCkernel
  have hproj := summed_ray_projector r H hr mat hmat
  have hexp := actual_block_expansion s ha ω₁ ω₂ η t C D hC hD hCD E rows hrows Φ K K₀ H₀ A₀ B₀
    hK hK₀ hH₀ hA₀ hB₀
  have hregroup : (∑ u ∈ artificialDivisors s C D hD.1,
      (UniqueFactorizationMonoid.moebius u : ℂ)*phase*
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*
          rawMatrix s ha ω₁ ω₂ C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
            (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀) =
      phase*∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*mat χ ξ := by
    have h1 := artificial_sum_squarefree s C D hD.1 (fun u => phase*
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*
        rawMatrix s ha ω₁ ω₂ C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
          (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀)
    simp only [← mul_assoc] at h1
    rw [← h1, summed_projector_regroup]
    rfl
  rw [hexp]
  have hsum := hregroup
  simp only [mul_assoc] at hsum ⊢
  rw [show (∑ u ∈ artificialDivisors s C D hD.1,
      (UniqueFactorizationMonoid.moebius u : ℂ)*(phase*
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*
          rawMatrix s ha ω₁ ω₂ C D hC hD E u (fixedPair η C D hC E χ (ξ⁻¹)).left
            (fixedPair η C D hC E χ (ξ⁻¹)).right t rows Φ K K₀ H₀ A₀ B₀)) =
      phase*∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*mat χ ξ from hsum]
  set T := ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff firstPhaseTable χ ξ*mat χ ξ with hT
  have hstep : ‖commonHeight s η t C D*(scalar C D hC E K A₀ B₀*(phase*T))‖/sourceVolume s ≤
      r*‖T‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    have hb : ‖commonHeight s η t C D‖*(‖scalar C D hC E K A₀ B₀‖*(‖phase‖*‖T‖)) ≤
        ‖scalar C D hC E K A₀ B₀‖*‖T‖ := by
      have h1 : ‖phase‖*‖T‖ ≤ ‖T‖ := mul_le_of_le_one_left (norm_nonneg _) hphase
      have h2 : ‖scalar C D hC E K A₀ B₀‖*(‖phase‖*‖T‖) ≤ ‖scalar C D hC E K A₀ B₀‖*‖T‖ :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      exact (mul_le_of_le_one_left (by positivity) hheight).trans h2
    calc _ ≤ ‖scalar C D hC E K A₀ B₀‖*‖T‖/sourceVolume s :=
          div_le_div_of_nonneg_right hb (sourceVolume_pos s).le
      _ = r*‖T‖ := by dsimp only [r]; ring
  refine hstep.trans (hproj.trans_eq ?_)
  dsimp only [H, pref]
  rw [unit_prefactor s hunit η C D E K]
  simp only [map_one, Nat.cast_one, div_one]
  ring

#print axioms source_coefficient_lower
#print axioms actual_source_reference_pair
#print axioms balanced_kernel
#print axioms block_of_summed_raw_sides
end
end QRH.Cycle092.TwistedRawBall
