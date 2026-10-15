/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.gao_cycle61_plane_20261013.Bundles.B084
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow

/- BEGIN ORIGINAL Cycle61.Physical.ClippedProjectorShell; sha256 2b53ae3ac67208008b4c2d90099bc0d3426a970bd2a1e9e5ad405a941678170f -/
section
                                          

namespace Cycle61.Physical

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentActiveDivisorShell
local notation "O" => ActualEisensteinCubic.O

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

def sourcePlainScales (s : Source ι) (second : Bool) : Fin 2 → ℝ :=
  if second then ![s.Y₁,s.Y₂] else ![s.X₁,s.X₂]

def sourcePositiveRow (s : Source ι) (second : Bool) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) : ℂ :=
  allocatedPositiveRow s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((Ideal.absNorm I : ℝ)/s.P i)) s.P D a s.W₁ s.W₂
    (sourcePlainScales s second 0) (sourcePlainScales s second 1)

def plainClipAllowance (Z : ℝ) (b : Fin 2 → ℝ) : ℝ :=
  ∑ j, Real.logb Z (max 1 (b j))

def sourcePostClip (s : Source ι) (second : Bool) (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  negativeTotal (fun j => Real.logb Z (sourcePlainScales s second j)-
    actualPlainReduction Z D a j)

theorem source_post_clip_bound (s : Source ι) (second : Bool) (Z : ℝ) (hZ : 1 < Z)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (z : O) (b : Fin 2 → ℝ) (hX : ∀ j, 0 < sourcePlainScales s second j)
    (hs₁ : Function.support s.W₁ ⊆ Set.Iic (b 0))
    (hs₂ : Function.support s.W₂ ⊆ Set.Iic (b 1))
    (hn : sourcePositiveRow s second D a z ≠ 0) :
    sourcePostClip s second Z D a ≤ plainClipAllowance Z b :=
  actual_post_clipping_bound Z hZ s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((Ideal.absNorm I : ℝ)/s.P i)) s.P D a s.W₁ s.W₂
    (sourcePlainScales s second) b hX hs₁ hs₂ hn

/-- The retained two-row scalar includes both actual changes of normalizer. -/
def sourceClippedPairWeight (s : Source ι) (v : Source κ) (secondS secondV : Bool)
    (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) : ℝ :=
  (1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*
    Z^((sourcePostClip s secondS Z D a+sourcePostClip v secondV Z D b)/2)

theorem source_clipped_pair_exponent (s : Source ι) (v : Source κ)
    (secondS secondV : Bool) (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) :
    sourceClippedPairWeight s v secondS secondV Z D a b =
      Z^((-clippedReduction (Real.logb Z (formalReductionFactor D a s.P))
          (fun j => Real.logb Z (sourcePlainScales s secondS j)) (actualPlainReduction Z D a)+
        negativeTotal (fun j => Real.logb Z (sourcePlainScales s secondS j))-
        clippedReduction (Real.logb Z (formalReductionFactor D b v.P))
          (fun j => Real.logb Z (sourcePlainScales v secondV j)) (actualPlainReduction Z D b)+
        negativeTotal (fun j => Real.logb Z (sourcePlainScales v secondV j)))/2) := by
  have hs : 0 < formalReductionFactor D a s.P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _ => s.P_pos i))
  have hv : 0 < formalReductionFactor D b v.P :=
    mul_pos (selectedNorm_pos D b) (Finset.prod_pos (fun i _ => v.P_pos i))
  unfold sourceClippedPairWeight
  rw [reciprocal_sqrt_log Z _ _ hZ hs hv, ← Real.rpow_add (zero_lt_one.trans hZ)]
  congr 1
  unfold clippedReduction sourcePostClip
  ring

/-- Zero positive pairs contribute zero. The clipping cap is derived separately
for every surviving pair, after both signed rectangles have been split. -/
def nonzeroClippedPairWeight (s : Source ι) (v : Source κ) (secondS secondV : Bool)
    (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O) : ℝ :=
  if sourcePositiveRow s secondS D a zs ≠ 0 ∧ sourcePositiveRow v secondV D b zv ≠ 0
    then sourceClippedPairWeight s v secondS secondV Z D a b else 0

theorem nonzero_clipped_pair_le_raw (s : Source ι) (v : Source κ)
    (secondS secondV : Bool) (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O)
    (bs bv : Fin 2 → ℝ)
    (hXs : ∀ j, 0 < sourcePlainScales s secondS j)
    (hXv : ∀ j, 0 < sourcePlainScales v secondV j)
    (hs₁ : Function.support s.W₁ ⊆ Set.Iic (bs 0))
    (hs₂ : Function.support s.W₂ ⊆ Set.Iic (bs 1))
    (hv₁ : Function.support v.W₁ ⊆ Set.Iic (bv 0))
    (hv₂ : Function.support v.W₂ ⊆ Set.Iic (bv 1)) :
    nonzeroClippedPairWeight s v secondS secondV Z D a b zs zv ≤
      (1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*
        Z^((plainClipAllowance Z bs+plainClipAllowance Z bv)/2) := by
  unfold nonzeroClippedPairWeight
  split_ifs with hn
  · have hh₁ := source_post_clip_bound s secondS Z hZ D a zs bs hXs hs₁ hs₂ hn.1
    have hh₂ := source_post_clip_bound v secondV Z hZ D b zv bv hXv hv₁ hv₂ hn.2
    unfold sourceClippedPairWeight
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity)
  · positivity

/-- This is the residual divisor-dyad payment for the actual retained scalars.
The constant precedes every moving source, frequency and allocation. The
projector is not encoded as a divisor of the reconstructed frequency. -/
theorem paired_all_clipped_active_shell
    (N : ℕ) (hι : Fintype.card ι ≤ N) (hκ : Fintype.card κ ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Source ι) (v : Source κ) (secondS secondV : Bool)
      (bs bv : Fin 2 → ℝ),
      (∀ j, 0 < sourcePlainScales s secondS j) →
      (∀ j, 0 < sourcePlainScales v secondV j) →
      Function.support s.W₁ ⊆ Set.Iic (bs 0) →
      Function.support s.W₂ ⊆ Set.Iic (bs 1) →
      Function.support v.W₁ ⊆ Set.Iic (bv 0) →
      Function.support v.W₂ ⊆ Set.Iic (bv 1) →
      ∀ (Ds : Finset (Ideal O)), (∀ D∈Ds, Squarefree D) →
      ∀ (zs zv : ∀ D : Ideal O,
        Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) →
        Allocation D (Finset.univ : Finset (κ ⊕ Fin 2)) → O)
      (T Z : ℝ), 1 ≤ T → 1 < Z →
      (∀ D∈Ds, T ≤ (Ideal.absNorm D : ℝ)) →
      (∀ D∈Ds, (Ideal.absNorm D : ℝ) < 2*T) →
      (∑ D∈Ds, ∑ a∈s.active D, ∑ b∈v.active D,
        nonzeroClippedPairWeight s v secondS secondV Z D a b (zs D a b) (zv D a b)) ≤
        C*(2*T)^(2*ε)*
          Z^((s.allowance Z+v.allowance Z+plainClipAllowance Z bs+plainClipAllowance Z bv)/2) := by
  obtain ⟨C,hC,hbound⟩ := paired_all_active_shell N hι hκ ε hε
  refine ⟨C,hC,?_⟩
  intro s v secondS secondV bs bv hXs hXv hs₁ hs₂ hv₁ hv₂ Ds hD zs zv T Z hT hZ hlo hhi
  let K : ℝ := Z^((plainClipAllowance Z bs+plainClipAllowance Z bv)/2)
  have hK : 0 ≤ K := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hh := hbound s v Ds hD T Z hT hZ hlo hhi
  calc
    _ ≤ ∑ D∈Ds, ∑ a∈s.active D, ∑ b∈v.active D,
        (1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*K :=
      Finset.sum_le_sum (fun D _ => Finset.sum_le_sum (fun a _ =>
        Finset.sum_le_sum (fun b _ => nonzero_clipped_pair_le_raw s v secondS secondV Z hZ
          D a b (zs D a b) (zv D a b) bs bv hXs hXv hs₁ hs₂ hv₁ hv₂)))
    _ = (∑ D∈Ds, ∑ a∈s.active D, ∑ b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*K := by
      simp only [Finset.sum_mul]
    _ ≤ (C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2))*K :=
      mul_le_mul_of_nonneg_right hh hK
    _ = _ := by
      unfold K
      rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans hZ)]
      congr 2
      ring

end
end Cycle61.Physical

#print axioms Cycle61.Physical.source_clipped_pair_exponent
#print axioms Cycle61.Physical.paired_all_clipped_active_shell

end
/- END ORIGINAL Cycle61.Physical.ClippedProjectorShell -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.Child; sha256 d8a06d3fa4e5248fb4630f9968e1e4e7541e8d66518518625c6f8afc3315778b -/
section
                                                           

namespace OAI

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle61FirstChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

def unitBudgetState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hB:0≤ Bmask):
    NaturalState Z Bmask bΦ:=
  {unpuncturedState s with
    puncture_bound:=by simpa only [unpuncturedState,map_one,Nat.cast_one] using Real.one_le_rpow s.base_ge_one hB}

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem reflected_child_from_positive
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:PositiveAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (hB:0≤ Bmask)(ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)
    (F:Finset α)(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤ w i)(hwL:∀i,w i≤ Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤ hi)
    (hheight:0≤ height)(hfreq:∀i,|freq i|≤ height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤ Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hc₁:X₁≤ Z^L)(hc₂:X₂≤ Z^L)
    (hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
:
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε):=by
  have hZ:0< Z:=zero_lt_one.trans_le s.base_ge_one
  have hh:=hlow F (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>t+freq i)
    0 (|t|+height) (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
    (add_nonneg (abs_nonneg t) hheight)
    (fun i=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i)))
    (unitBudgetState s hB) hQ hs (reflectionProfiles ha hlo hhi Wshort hsW j k v t)
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hcapacity)

  rw [reflected_child_ray_energy s ha hlo hhi Wshort hsW F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>relativeCharacter M H hH η₀ (θ i)) (fun _=>Wslot)
    (fun i=>Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ _) j k v t X₁ X₂ hX₁ hX₂]
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    NaturalState.mask,effectiveState,effectiveRadial,abs_zero,add_zero,add_assoc] using hh

end SevenEighths.Cycle61FirstChild

end

end OAI

/- Adapted from OpenAI/math family003 Energy/ReferenceLowChild.lean, Apache-2.0.
The terminal is applied only to daughters satisfying their own old capacity. -/

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.Child -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.Direct; sha256 4dba608fa625424b3dbef05a8cb095188194c7af5825032ab7d0b0bbfc03c0d2 -/
section
                                           

namespace OAI

noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.Cycle61FirstDirect
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceLowBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

open Cycle61FirstChild

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem direct_child_from_positive
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:PositiveAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (hB:0≤ Bmask)(ha:0< a)
    (F:Finset α)(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ℝ)(u t height:ℝ)
    (hw:∀i,0≤ w i)(hwL:∀i,w i≤ Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤ hi)
    (hheight:0≤ height)(hfreq:∀i,|freq i|≤ height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤ Mcap)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)(hc₁:X₁≤ Z^L)(hc₂:X₂≤ Z^L)
    (hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤ s.width)
:
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      W₁ X₁ 0 u*
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((independentProfiles ha W₁ W₂ hs₁ hs₂ u t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε):=by
  have hZ:0< Z:=zero_lt_one.trans_le s.base_ge_one
  have hh:=hlow F (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>t+freq i)
    0 (|t|+height) (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
    (add_nonneg (abs_nonneg t) hheight)
    (fun i=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i)))
    (unitBudgetState s hB) hQ hs (independentProfiles ha W₁ W₂ hs₁ hs₂ u t)
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hcapacity)

  rw [independent_child_ray_energy s ha W₁ W₂ hs₁ hs₂ F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>relativeCharacter M H hH η₀ (θ i)) (fun _=>Wslot)
    (fun i=>Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ _) t u t X₁ X₂ hX₁ hX₂]
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    NaturalState.mask,effectiveState,effectiveRadial,abs_zero,add_zero,add_assoc] using hh

end SevenEighths.Cycle61FirstDirect

end

end OAI

/- Adapted from OpenAI/math family003 Energy/ReferenceLowDirect.lean, Apache-2.0.
The terminal is applied only to daughters satisfying their own old capacity. -/

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.Direct -/

/- BEGIN ORIGINAL Cycle61.Physical.FirstBranches.Geometry; sha256 97a6ab17ce8863692ebdff22a06f3bf1b9832a9703e1c3fd4f5dc87e77cc4abc -/
section
                                          
                                                            

namespace OAI.SevenEighths.Cycle61FirstGeometry
noncomputable section
set_option autoImplicit false
open HeckeFamily CenteredMomentEnergyBands CenteredMomentRetainedProfile
open CenteredMomentEnergyReferenceLowWindow

/-- Subunit raw lengths are clipped by the actual old moment definition. -/
theorem length_rpow (Z r : ℝ) (hZ : 1< Z) : length Z (Z^r)=max 0 r := by
  have hh := Cycle61.Physical.logb_clipped_scale Z (Z^r) hZ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) r)
  simpa only [length,clippedScale,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

/-- The new parent's daughter has old capacity. No old capacity is imposed on
that parent: only the .25/.5/.04 comparison geometry is used. -/
theorem reflected_daughter_capacity (Z M width along bshort slots xi : ℝ)
    (hZ : 1< Z) (hM : 0≤ M) (hwidth : M≤ width)
    (hlong : M/2≤ along) (hshort : bshort≤ M/4)
    (hslots : slots≤ M/25) (hxi : 0≤ xi) (hpadding : xi≤7*M/100) :
    max 0 (width-along+xi)+length Z (Z^bshort)+(9/2)*slots≤ width := by
  rw [length_rpow Z bshort hZ]
  have hs : max 0 bshort≤ M/4 := max_le (by linarith) hshort
  have hbound : max 0 (width-along+xi)≤ width-M/2+xi :=
    max_le (by linarith) (by linarith)
  linarith

/-- Every retained annulus has the same actual old-capacity gate, including both
plain derivative choices; no individual annulus bound is assumed. -/
theorem reflected_window_capacity (Z M width along bshort slots xi v : ℝ)
    (hZ : 1< Z) (hM : 0≤ M) (hwidth : M≤ width)
    (hlong : M/2≤ along) (hshort : bshort≤ M/4)
    (hslots : slots≤ M/25) (hxi : 0≤ xi) (hpadding : xi≤7*M/100)
    (hv : v∈Set.Icc 0 (max 0 (width-along+xi)*Real.log Z)) :
    length Z (Real.exp v)+length Z (Z^bshort)+(9/2)*slots≤ width := by
  have hh := (reflection_window_length Z (max 0 (width-along+xi)) v hZ
    (le_max_left _ _) hv).1
  have hc := reflected_daughter_capacity Z M width along bshort slots xi hZ hM hwidth
    hlong hshort hslots hxi hpadding
  linarith

theorem length_le_of_scale_le (Z X R : ℝ) (hZ : 1< Z) (hR : 0≤ R)
    (hX : X≤ Z^R) : length Z X≤ R := by
  have hh := Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (le_max_left 1 X))
    (max_le (Real.one_le_rpow hZ.le hR) hX)
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh

theorem direct_daughter_capacity (Z M width X₁ X₂ slots : ℝ)
    (hZ : 1< Z) (hM : 0≤ M) (hwidth : M≤ width)
    (hX₁ : X₁≤ Z^(M/4)) (hX₂ : X₂≤ Z^(M/2)) (hslots : slots≤ M/25) :
    length Z X₁+length Z X₂+(9/2)*slots≤ width := by
  have h₁ := length_le_of_scale_le Z X₁ (M/4) hZ (by linarith) hX₁
  have h₂ := length_le_of_scale_le Z X₂ (M/2) hZ (by linarith) hX₂
  linarith

/-- The literal equal-product comparison of the manuscript has second length
between .57M and .63M, hence belongs to the reflected public branch. -/
theorem actual_comparison_powers (Z M n₁ n₂ : ℝ) (hZ : 1< Z) (hM : 0≤ M)
    (hn₁ : (41/100)*M≤ n₁) (hn₂ : (41/100)*M≤ n₂)
    (hn₁' : n₁≤(44/100)*M) (hn₂' : n₂≤(44/100)*M) :
    CenteredMomentEnergyReferenceState.comparisonSecond Z M (Z^n₁) (Z^n₂) =
      Z^(n₁+n₂-M/4) ∧ M/2≤ n₁+n₂-M/4 ∧ n₁+n₂-M/4≤(63/100)*M := by
  refine ⟨?_,by linarith,by linarith⟩
  unfold CenteredMomentEnergyReferenceState.comparisonSecond
    CenteredMomentEnergyReferenceState.comparisonFirst
  rw [←Real.rpow_add (zero_lt_one.trans hZ),
    Real.rpow_sub (zero_lt_one.trans hZ)]

end
end OAI.SevenEighths.Cycle61FirstGeometry

end
/- END ORIGINAL Cycle61.Physical.FirstBranches.Geometry -/
