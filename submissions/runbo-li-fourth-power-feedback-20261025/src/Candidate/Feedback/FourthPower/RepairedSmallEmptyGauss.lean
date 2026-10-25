/- Copyright (c) 2026 Sil. Apache-2.0.
Empty selection reaches the WHOLE actual Gauss energy of its constructed
linear-conductor character. No identification of differently indexed
partEnergy label domains is needed. The original coprimality gate is retained.

-/
import Candidate.Feedback.FourthPower.RepairedSmallCharacter
import Candidate.Feedback.FourthPower.OuterFreshConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.RepairedSmallEmptyGauss
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open CompletedGauss ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentLiveDomain CenteredMomentSourceMass
open CenteredMomentFirstSectors CenteredMomentAddedZeroUniform
open CenteredMomentSmoothedWindowEnergy MixedSupplierPositive
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedInnerExceptionalBlock
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierOuterActive MixedSupplierOriginalFrequency
open OuterFreshWindowPair OuterFreshConsumer RepairedSmallCharacter
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

theorem empty_selected_weight (q : Data ι) (hJ : q.J=∅) (y : Selected q) :
    selectedWeight q y=1 := by
  unfold selectedWeight
  apply Finset.prod_eq_one
  intro j hj
  exact False.elim (by simpa only [hJ,Finset.notMem_empty] using j.property)

theorem empty_selected_positive_le (q : Data ι) (hJ : q.J=∅)
    (x : Frozen q) (y : Selected q) (τ : Character) :
    selectedPositiveWeight q x y τ≤1 := by
  rw [selected_weight_gate,empty_selected_weight q hJ y]
  split_ifs <;> simp only [norm_one,one_pow,le_refl,zero_le_one]

theorem empty_active_card (q : Data ι) (hJ : q.J=∅) : (activeSelected q).card≤1 := by
  apply Finset.card_le_one.mpr
  intro y hy y' hy'
  funext j
  exact False.elim (by simpa only [hJ,Finset.notMem_empty] using j.property)

theorem source_gauss_nonneg (S : Finset Id) (c f : Id → ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤(sourceGaussEnergy S c f Φ K).re := by
  have hs := gaussEnergy_hasSum_re Finset.univ (sourceGenerator S)
    (sourceGenerator_supported S) (fun I : supportedColumns S => c I*f I) Φ K hK
  change 0≤(gaussEnergy _ _ _ _ Φ K).re
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hΦ z))

/-- Literal coefficient identity on the source's supported ideal columns. -/
theorem empty_column_height (q : Data ι) (x : Frozen q) (y : Selected q)
    (hy : selectedProduct q y=1) (s : Source (RestIndex q) a b) (ha : 0<a)
    (hm : Matches q x s ha) (seed : Id) (τ σ : Character) (ξ : RayCharacter)
    (hσ : ∀I : Id,Supported I → ∀t : ℝ,
      heightCoeff σ t I=heightCoeff τ t I*(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
        rayCharacter ξ (primaryGenerator I)) (I : Id) (hI : Supported I) (t : ℝ) :
    outerColumn q x y seed ξ I*heightCoeff τ t I=
      gate q x*(sourceCoefficient s ha seed I*heightCoeff σ t I) := by
  rw [outerColumn,common_coefficient q x s ha hm seed I,hy,primaryGenerator_one,
    idealRowHom_one_supported I hI,one_pow,mul_one,hσ I hI t]
  ring

theorem empty_gauss_eq_on_gate (q : Data ι) (x : Frozen q) (y : Selected q)
    (hy : selectedProduct q y=1) (s : Source (RestIndex q) a b) (ha : 0<a)
    (hm : Matches q x s ha) (seed : Id) (τ σ : Character) (ξ : RayCharacter)
    (hσ : ∀I : Id,Supported I → ∀t : ℝ,
      heightCoeff σ t I=heightCoeff τ t I*(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
        rayCharacter ξ (primaryGenerator I)) (hg : gate q x=1)
    (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K=
      sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha seed) (heightCoeff σ t) Φ K := by
  unfold sourceGaussEnergy
  apply congrArg (fun c : supportedColumns (sourceColumns s) → ℂ =>
    gaussEnergy Finset.univ (sourceGenerator (sourceColumns s))
      (sourceGenerator_supported (sourceColumns s)) c Φ K)
  funext I
  simpa only [hg,one_mul] using empty_column_height q x y hy s ha hm seed τ σ ξ hσ
    I.val (Finset.mem_filter.mp I.property).2 t

theorem empty_gauss_zero_off_gate (q : Data ι) (x : Frozen q) (y : Selected q)
    (hy : selectedProduct q y=1) (s : Source (RestIndex q) a b) (ha : 0<a)
    (hm : Matches q x s ha) (seed : Id) (τ σ : Character) (ξ : RayCharacter)
    (hσ : ∀I : Id,Supported I → ∀t : ℝ,
      heightCoeff σ t I=heightCoeff τ t I*(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
        rayCharacter ξ (primaryGenerator I)) (hg : gate q x=0)
    (t : ℝ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K=0 := by
  have hc : (fun I : supportedColumns (sourceColumns s) =>
      outerColumn q x y seed ξ I*heightCoeff τ t I)=(fun _ => 0) := by
    funext I
    simpa only [hg,zero_mul] using empty_column_height q x y hy s ha hm seed τ σ ξ hσ
      I.val (Finset.mem_filter.mp I.property).2 t
  unfold sourceGaussEnergy
  rw [hc]
  simp only [gaussEnergy,gaussPolynomial,zero_mul,Finset.sum_const_zero,norm_zero,
    zero_pow (by decide : (2:ℕ)≠0),Complex.ofReal_zero,tsum_zero]

theorem empty_gauss_re_le (q : Data ι) (x : Frozen q) (y : Selected q)
    (hy : selectedProduct q y=1) (s : Source (RestIndex q) a b) (ha : 0<a)
    (hm : Matches q x s ha) (seed : Id) (τ σ : Character) (ξ : RayCharacter)
    (hσ : ∀I : Id,Supported I → ∀t : ℝ,
      heightCoeff σ t I=heightCoeff τ t I*(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
        rayCharacter ξ (primaryGenerator I)) (t : ℝ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K).re≤
      (sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha seed) (heightCoeff σ t) Φ K).re := by
  by_cases hg : IsCoprime (frozenProduct q x) q.R
  · rw [empty_gauss_eq_on_gate q x y hy s ha hm seed τ σ ξ hσ (if_pos hg) t Φ K]
  · rw [empty_gauss_zero_off_gate q x y hy s ha hm seed τ σ ξ hσ (if_neg hg) t Φ K,
      Complex.zero_re]
    exact source_gauss_nonneg _ _ _ Φ K hK hΦ

/-- Empty selection has at most one term and positive weight at most one.
The positive whole energy is bounded before any signed second splitting. -/
theorem empty_selected_energy_le (q : Data ι) (hJ : q.J=∅) (x : Frozen q)
    (s : Source (RestIndex q) a b) (ha : 0<a) (hm : Matches q x s ha)
    (seed : Id) (τ σ : Character) (ξ : RayCharacter)
    (hσ : ∀I : Id,Supported I → ∀t : ℝ,
      heightCoeff σ t I=heightCoeff τ t I*(idealRowHom (primaryGenerator (frozenProduct q x)) I)^2*
        rayCharacter ξ (primaryGenerator I)) (t : ℝ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (hΦ : ∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑y∈activeSelected q,selectedPositiveWeight q x y τ*
      (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K).re)≤
      (sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha seed) (heightCoeff σ t) Φ K).re := by
  let E:=(sourceGaussEnergy (sourceColumns s) (sourceCoefficient s ha seed) (heightCoeff σ t) Φ K).re
  have hE : 0≤E := source_gauss_nonneg _ _ _ Φ K hK hΦ
  have hpoint (y : Selected q) : selectedPositiveWeight q x y τ*
      (sourceGaussEnergy (sourceColumns s) (outerColumn q x y seed ξ) (heightCoeff τ t) Φ K).re≤E := by
    apply (mul_le_mul_of_nonneg_left
      (empty_gauss_re_le q x y (empty_selected_product q hJ y) s ha hm seed τ σ ξ hσ t Φ K hK hΦ)
      (selected_positive_nonneg q x y τ)).trans
    exact (mul_le_mul_of_nonneg_right (empty_selected_positive_le q hJ x y τ) hE).trans_eq (one_mul _)
  calc
    _≤∑_y∈activeSelected q,E := Finset.sum_le_sum (fun y _ => hpoint y)
    _=((activeSelected q).card:ℝ)*E := by simp only [Finset.sum_const,nsmul_eq_mul]
    _≤1*E := mul_le_mul_of_nonneg_right (by exact_mod_cast empty_active_card q hJ) hE
    _=E := one_mul _

end
end Candidate.Feedback.FourthPower.RepairedSmallEmptyGauss
