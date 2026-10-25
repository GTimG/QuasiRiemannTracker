/- Copyright (c) 2026 Sil. Apache-2.0.
Aggregate the exact four Poisson components BEFORE taking their norms.
The older sum-of-individual-norms interface cannot consume a bound for
the norm of the selected sum. This file establishes the correct bridge.

-/
import Candidate.SilPrior.FourthPower.OuterFreshNonexceptionalBlock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.RepairedGroupedConsumer
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSecondLocalization
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock
open CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstColumns CenteredMomentOriginalChildEnergy CenteredMomentSupportedTailAggregate
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedPoissonCompletion MixedPoissonLocalization MixedLocalizedDictionary
open OuterFreshRows OuterFreshWindowPair OuterFreshConsumer OuterFreshNonexceptionalBlock
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {ι:Type u}[Fintype ι]{a b:ℝ}

def selectedSum (q:Data ι)(x:Frozen q)(τ:Character)(f:Selected q→ℂ) : ℂ :=
  ∑y∈activeSelected q,(selectedPositiveWeight q x y τ:ℂ)*f y

def groupedFourCost (q:Data ι)(x:Frozen q)(s:Source (RestIndex q) a b)
    (seed:Id)(τ:Character)(ξ χ:RayCharacter)(Q:Id)(t K T Z ζ H:ℝ) : ℝ :=
  ‖selectedSum q x τ (fun y=>outerZero q x y s seed τ ξ t K)‖+
    ‖selectedSum q x τ (fun y=>fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H)‖+
    ‖selectedSum q x τ (fun y=>fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H)‖+
    ‖selectedSum q x τ (fun y=>secondDiscardedEnergy τ t (sourceColumns s)
      (outerColumn q x y seed ξ) ballProfile K T Z ζ)‖

/-- Exact complex identity, at the original scale and with the original
natural-zero coefficient. No triangle inequality has yet been used. -/
theorem original_four_identity (q:Data ι)(x:Frozen q)(y:Selected q)
    (s:Source (RestIndex q) a b)(seed:Id)(τ:Character)(ξ χ:RayCharacter)
    (Q:Id)(t K T Z ζ H:ℝ)(hK:0<K)
    (hH:∀I∈fixedPool q x s seed,(I.absNorm:ℝ)≤H) :
    sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) ballProfile K=
      outerZero q x y s seed τ ξ t K+
        fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H+
        fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H+
        secondDiscardedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) ballProfile K T Z ζ := by
  have hscale:16*(K/16)*(1:ℝ)^4=K:=by ring
  have he:=density_normalized_poisson Finset.univ
    (sourceGenerator (sourceColumns s)) (sourceGenerator_supported (sourceColumns s))
    (fun I:supportedColumns (sourceColumns s)=>outerColumn q x y seed ξ I*heightCoeff τ t I)
    (K/16) 1 (by positivity) (by norm_num)
  rw [hscale,Complex.ofReal_one,div_one,density_split _ _ _ _ (K/16) 1
    (frequencyRadius T Z ζ) (by positivity) (by norm_num)] at he
  rw [MixedLocalizedDictionary.source_retained τ t _ _ (K/16) 1 T Z ζ (by norm_num),
    MixedLocalizedDictionary.source_discarded τ t _ _ (K/16) 1 T Z ζ (by norm_num),
    hscale,Complex.ofReal_one,div_one,div_one] at he
  rw [fixed_retained_split q x y s seed τ ξ χ Q t ballProfile K T Z ζ H hK hH] at he
  change gaussEnergy _ _ _ _ _ _=_
  rw [he]
  unfold outerZero
  ring

/-- The selected sum is taken before the four norms. This uses the
real part of the genuine source energies, exactly as supplied by
uniform_supplier_energies, not an unjustified norm/real-part equality. -/
theorem actual_grouped_four_components (q:Data ι)(x:Frozen q)
    (s:Source (RestIndex q) a b)(seed:Id)(τ:Character)(ξ χ:RayCharacter)
    (Q:Id)(t K T Z ζ H:ℝ)(hK:0<K)
    (hH:∀I∈fixedPool q x s seed,(I.absNorm:ℝ)≤H) :
    (∑y∈activeSelected q,selectedPositiveWeight q x y τ*
      (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) ballProfile K).re)≤
      groupedFourCost q x s seed τ ξ χ Q t K T Z ζ H := by
  let energy:=fun y:Selected q=>sourceGaussEnergy (sourceColumns s)
    (outerColumn q x y seed ξ) (heightCoeff τ t) ballProfile K
  have hreal:(∑y∈activeSelected q,selectedPositiveWeight q x y τ*(energy y).re)=
      (selectedSum q x τ energy).re := by
    simp only [selectedSum,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero]
  have hid:selectedSum q x τ energy=
      selectedSum q x τ (fun y=>outerZero q x y s seed τ ξ t K)+
        selectedSum q x τ (fun y=>fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H)+
        selectedSum q x τ (fun y=>fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H)+
        selectedSum q x τ (fun y=>secondDiscardedEnergy τ t (sourceColumns s)
          (outerColumn q x y seed ξ) ballProfile K T Z ζ) := by
    have hf (y:Selected q):energy y=
        outerZero q x y s seed τ ξ t K+
          fixedPart false q x y s seed τ ξ χ Q t ballProfile K T Z ζ H+
          fixedPart true q x y s seed τ ξ χ Q t ballProfile K T Z ζ H+
          secondDiscardedEnergy τ t (sourceColumns s) (outerColumn q x y seed ξ) ballProfile K T Z ζ :=
      original_four_identity q x y s seed τ ξ χ Q t K T Z ζ H hK hH
    simp only [selectedSum,hf,
      mul_add,Finset.sum_add_distrib]
  change (∑y∈activeSelected q,selectedPositiveWeight q x y τ*(energy y).re)≤_
  rw [hreal,hid]
  unfold groupedFourCost
  simp only [Complex.add_re]
  exact add_le_add (add_le_add (add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _))
    (Complex.re_le_norm _)) (Complex.re_le_norm _)

/-- Existing bounds for individual zero/fixed/tail companions remain
usable through this honest triangle inequality. The nonexceptional part
need not pass through it and keeps its grouped cancellation. -/
theorem selected_norm_le (q:Data ι)(x:Frozen q)(τ:Character)(f:Selected q→ℂ) :
    ‖selectedSum q x τ f‖≤∑y∈activeSelected q,selectedPositiveWeight q x y τ*‖f y‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro y hy
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (selected_positive_nonneg q x y τ)]

private theorem ray_energy_reorder (q:Data ι)(x:Frozen q)(τ:Character)
    (E:RayCharacter→Selected q→ℝ) :
    (∑y∈activeSelected q,∑χ:RayCharacter,∑ξ:RayCharacter,
      ‖pairCoeff firstPhaseTable χ ξ‖*selectedPositiveWeight q x y τ*E ξ y)=
      ∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
        ∑y∈activeSelected q,selectedPositiveWeight q x y τ*E ξ y := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Actual finite original supplier energy with the correct grouped
four-component consumer. Positivity is used only at the earlier finite
ball-profile energy comparison, where ballProfile_nonneg supplies it. -/
theorem uniform_supplier_grouped_four (q:Data ι)(x:Frozen q)(hx:Function.Injective x)
    (s:Source (RestIndex q) a b)(ha:0<a)(hm:Matches q x s ha) :
    ∃seed:Id,(frozenWeight q x≠0→q.u=frozenProduct q x*seed) ∧
      ∀(τ:Character)(t:ℝ)(Ks:Finset O)(K T Z ζ H:ℝ),0<K→
      (∀I∈fixedPool q x s seed,(I.absNorm:ℝ)≤H)→∀(χ₀:RayCharacter)(Q:Id),
      (∑k∈Ks,(ballProfile (‖eisEmbedding k‖^2/K)).re*
        ‖frozenWeight q x*originalFamily q x τ t k‖^2)≤
      ‖frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)*
        ∑χ:RayCharacter,∑ξ:RayCharacter,‖pairCoeff firstPhaseTable χ ξ‖*
          groupedFourCost q x s seed τ ξ χ₀ Q t K T Z ζ H) := by
  obtain ⟨seed,hseed,henergy⟩:=uniform_supplier_energies q x hx s ha hm
  refine ⟨seed,hseed,?_⟩
  intro τ t Ks K T Z ζ H hK hH χ₀ Q
  have he:=henergy τ t Ks ballProfile K hK (fun z=>ballProfile_nonneg _)
  rw [ray_energy_reorder] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro χ hχ
  apply Finset.sum_le_sum
  intro ξ hξ
  exact mul_le_mul_of_nonneg_left
    (actual_grouped_four_components q x s seed τ ξ χ₀ Q t K T Z ζ H hK hH) (norm_nonneg _)

/-- Exact restoration of the selected scale used by physicalAverage.
This scale includes its padding; it is not replaced by selectedVolume. -/
theorem scale_mul_physical_average (q:Data ι)(x:Frozen q)(hqP:∀i,0<q.P i)
    (r:Source (RestIndex q) a b)(seed:Id)(τ:Character)(ξ χ₀:RayCharacter)(Q C E:Id)
    (hC:Supported C)(hE:Supported E)(U:Finset (CommonIndex C E))
    (t R:ℝ)(Φ:𝓢(ℝ,ℂ))(K:ℝ)(n:Fin 4→ℤ) :
    (MixedSelectedVolume.scale q:ℂ)*
      physicalAverage q x r seed τ ξ χ₀ Q C E hC hE U t R Φ K n=
      ∑y∈activeSelected q,(selectedPositiveWeight q x y τ:ℂ)*
        physicalBlock τ t (fixedPool q x r seed) (outerColumn q x y seed ξ) C E hC hE U R
          (outerRows false q x y τ ξ χ₀ Q C E U R) Φ K n := by
  have hs:MixedSelectedVolume.scale q≠0:=(MixedSelectedVolume.scale_pos q hqP).ne'
  unfold physicalAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr hs]
  <;> ring

end
end Candidate.SilPrior.FourthPower.RepairedGroupedConsumer
