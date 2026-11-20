import Candidate.C092.transport.ReferenceArmRadialAbsolute
import Candidate.C092.transport.OriginalLargeHeight
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
One early P.3 envelope for every retained original whole-slot subproduct. -/
import Candidate.C092.transport.ReferenceArmRadial
import Candidate.C092.transport.ReferenceShortP3

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ReferenceArmRadial
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge
open HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open QRH.Cycle092.ReferenceShortP3 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair QRH.Cycle092.WholeSlot
local notation "O" => HeckeFamily.O

theorem actual_large_height_subsets (τ:ℝ) (hτ:0<τ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr)
    (W : ℝ→ℂ) (hW : Continuous W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) (hΦs : Function.support (radialMajorant : ℝ→ℂ) ⊆ Set.Iic bΦ)
    (η₁ η₂ ηshort₀ ηlong₀ : Character)
    (Q1 Q : Ideal O) (hQ1r : Q1≤ rayM)
    (hQ10 : internalQ Q1 ηshort₀≠0) (hQ1t : internalQ Q1 ηshort₀≠⊤)
    (hQ172 : internalQ Q1 ηshort₀≤ Ideal.span {(72:O)}) (hQr : Q ≤ rayM)
    (hQ0 : internalQ Q ηlong₀ ≠ 0) (hQt : internalQ Q ηlong₀ ≠ ⊤)
    (hQ72 : internalQ Q ηlong₀ ≤ Ideal.span {(72:O)}) :
    ∃ d : ℕ, ∃ S : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ V : ℝ, 0≤ V → V≤2 →
    ∀ (T : Finset ι) (θ : ι → RayQuotient.Characters rayM Hr) (w σ v : ι→ℝ),
    (∀ i∈T, (33/50:ℝ) ≤ σ i) → (∀ i∈T, σ i ≤ (33/50:ℝ)) → (∑ i∈T,w i) ≤ widthCap →
    ∀ (p : Profiles (1/4) (9/4)) (t₁ t₂ height X₁ X₂ : ℝ),
    0 ≤ height → 0 < X₁ → 0 < X₂ → X₁ ≤ U → X₂ ≤ U → U^τ ≤ 1+|t₁|+|t₂|+height →
    ∀ (s : Finset FreeRow) (mark : ι → FreeRow → ℂ),
    (∀ u∈s,initialKeep η₁ (internalQ Q1 ηshort₀) u.val) →
    (∀ u∈s,initialKeep η₂ (internalQ Q ηlong₀) u.val) →
    (∀ u∈s,rowNorm u ≤ U^V) →
    (∀ u∈s, ∀ i∈T, ‖mark i u‖ =
      ‖normalizedSlot η₁ (fixedBadMask*idealGenerator 1) 1 u.val
        (originalPools rayM Hr 2 U w i)
        (originalCoefficients rayM Hr hHr ηshort₀ θ W U w σ v i) t₁ (U^(w i))‖) →
    finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark ≤
      C*(p.control S)^2*(1+|t₁|+|t₂|+height)^d*U^V := by
  obtain ⟨dheight,hdheight⟩:=QRH.Cycle092.LargeHeight.height_absorbs_base τ hτ
  choose d S C hC hsource using fun T : Finset ι => actual_absolute_reference T hβ rayM Hr hHr W hW hWs
    (1/4) bΦ (by norm_num) hbΦ hΦs η₁ η₂ ηshort₀ ηlong₀ Q1 Q hQ1r hQ10 hQ1t hQ172 hQr hQ0 hQt hQ72
  let D := ∑ T : Finset ι,d T
  let controls := (Finset.univ : Finset (Finset ι)).biUnion S
  let Cmax := 1+∑ T : Finset ι,C T
  have hCmax : 0 < Cmax := by
    have hh := Finset.sum_nonneg (fun T (_ : T∈(Finset.univ : Finset (Finset ι))) => (hC T).le)
    dsimp [Cmax]
    linarith
  have hD (T : Finset ι) : d T ≤ D := Finset.single_le_sum
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ T)
  have hcontrol (T : Finset ι) : S T ⊆ controls :=
    Finset.subset_biUnion_of_mem S (Finset.mem_univ T)
  have hCbound (T : Finset ι) : C T ≤ Cmax := by
    have hh := Finset.single_le_sum (s:=Finset.univ) (f:=C)
      (fun T _ => (hC T).le) (Finset.mem_univ T)
    dsimp [Cmax]
    linarith
  refine ⟨D+dheight,controls,Cmax,hCmax,?_⟩
  have he : ∀ᶠ U : ℝ in atTop, ∀ T : Finset ι, _ := Filter.eventually_all.mpr hsource
  filter_upwards [he,eventually_gt_atTop (1:ℝ)] with U hU hU1
  refine ⟨hU1,?_⟩
  intro V hV hV2 T θ w σ v hσlo hσhi hsum p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hshort hlong hlarge s mark hk1 hk2 hy hm
  have ht := (hU T).2 V hV hV2 (fun i : T => θ i.val) (fun i : T => w i.val)
    (fun i : T => σ i.val) (fun i : T => v i.val)
    (fun i => hσlo i.val i.property) (fun i => hσhi i.val i.property)
    (by simpa only [Finset.sum_coe_sort] using hsum)
    p t₁ t₂ height X₁ X₂ hh hX₁ hX₂ hshort hlong s (fun i : T => mark i.val) hk1 hk2 hy
    (fun u hu i => hm u hu i.val i.property)
  have heq : finiteEnergy s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
      (fun i : T => mark i.val) = finiteEnergyOn T s η₁ η₂ (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ mark := by
    unfold finiteEnergy finiteEnergyOn
    apply Finset.sum_congr rfl
    intro u hu
    exact congrArg (fun x : ℝ =>
      ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 0) t₁ X₁‖^2 *
      ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val (p.profile 1) t₂ X₂‖^2*x)
      (Finset.prod_coe_sort T (fun i => ‖mark i u‖^2))
  rw [heq] at ht
  have hp : p.control (S T) ≤ p.control controls := by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono (hcontrol T)) _)
      (Seminorm.le_def.mp (Finset.sup_mono (hcontrol T)) _)
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hh1 : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hdeg := pow_le_pow_right₀ hh1 (hD T)
  have hpn := p.control_nonneg (S T)
  let Ht:=1+|t₁|+|t₂|+height
  have hg : U^(widthCap+(1/4:ℝ)) ≤ Ht^dheight := by
    apply le_trans _ (hdheight U Ht hU1.le hlarge)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU1.le (by norm_num [widthCap] : widthCap+(1/4:ℝ) ≤ 1)
  have heU: U^(V+widthCap+(1/4:ℝ))=U^V*U^(widthCap+(1/4:ℝ)) := by
    rw [←Real.rpow_add (zero_lt_one.trans hU1)];ring_nf
  rw [heU] at ht
  apply ht.trans
  calc
    _ ≤ Cmax*(p.control controls)^2*Ht^D*(U^V*Ht^dheight) := by
      apply mul_le_mul
      · apply mul_le_mul _ hdeg (by positivity) (by positivity)
        exact mul_le_mul (hCbound T) (pow_le_pow_left₀ hpn hp 2) (sq_nonneg _) hCmax.le
      · exact mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (zero_lt_one.trans hU1).le _)
      · positivity
      · positivity
    _ = _ := by rw [pow_add];dsimp [Ht];ring

#print axioms actual_large_height_subsets
end
end QRH.Cycle092.ReferenceArmRadial
