import Candidate.Cycle63.Marked.WholeBufferedMax
import Candidate.Cycle63.Marked.DeletionFiniteExceptions
import Candidate.Cycle63.Marked.NaturalSlotPhase

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle63MarkedPlain
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily LocalMoment
open Cycle63Moment CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The exceptional free cores are one fixed finite set, chosen before
the scale, every root ideal, and every moving amplitude or zero label. -/
theorem whole_core_exception_set (η η₀ : Character) (bad : WholeSourceIndex M H→Ideal O)
    (hbad0 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠0)
    (hbadTop : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≠⊤)
    (hbad72 : ∀j,internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)≤ Ideal.span {(72:O)}) :
    ∃E : Finset FreeRow,∀u : FreeRow,u∉E ↔ ∀j,initialKeep (cleanWholeBase M H hH η η₀ j)
      (internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) u.val :=
  Deletion26.fixed_initial_exception_union (cleanWholeBase M H hH η η₀)
    (fun j=>internalQ (bad j) (wholeSourceAnchor M H hH η₀ j)) hbad0 hbadTop hbad72

/-- A fixed positive padding absorbs all natural conductor constants.
The original row norm alone supplies the embedding and clean modulus caps. -/
theorem eventually_whole_core_norm_caps (η η₀ : Character) (pad : ℝ) (hpad : 0< pad) :
    ∀ᶠ U : ℝ in atTop,1< U ∧ ∀(Y : ℝ)(u : FreeRow),rowNorm u≤ Y →
      ((Ideal.span {u.val}).absNorm:ℝ)≤ Y*U^pad ∧
      ‖ConcreteTraceCRT.eisEmbedding u.val‖^2≤ Y*U^pad ∧
      ∀j,(wholeCleanFamily M H hH η η₀ u j).modulus.absNorm≤ Y*U^pad := by
  let D := FixedUnmarkedDictionary.ofBases (cleanWholeBase M H hH η η₀)
  obtain ⟨K,hK,hmod⟩ := D.natural_conductor_bound
  have hlarge : ∀ᶠU : ℝ in atTop,K≤ U^pad :=
    (tendsto_rpow_atTop hpad).eventually (eventually_ge_atTop K)
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hKU hU
  refine ⟨hU,?_⟩
  intro Y u hu
  have hY : 0≤ Y := (zero_le_one.trans (rowNorm_ge_one u)).trans hu
  have hnorm : rowNorm u≤ Y*U^pad :=
    hu.trans (le_mul_of_one_le_right hY (hK.trans hKU))
  refine ⟨hnorm,?_,?_⟩
  · simpa only [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,rowNorm] using hnorm
  · intro j
    apply (hmod u j).trans
    calc
      K*rowNorm u ≤ K*Y := mul_le_mul_of_nonneg_left hu (zero_le_one.trans hK)
      _ ≤ _ := by nlinarith

/-- A positive lower physical width eventually puts every slot beyond
all fixed deleted detector conductors, uniformly over the whole dictionary. -/
theorem eventually_whole_core_inverse_large (η η₀ : Character) (wmin : ℝ) (hwmin : 0< wmin) :
    ∀ᶠU : ℝ in atTop,1< U ∧ ∀w : ℝ,wmin≤ w → ∀j : WholeSourceIndex M H,
      ((DetectorDictionaryInverseRawInitialGates.deletedBase
        (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)< U^w := by
  let K : ℝ := ∑j : WholeSourceIndex M H,
    ((DetectorDictionaryInverseRawInitialGates.deletedBase
      (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)
  have hlarge : ∀ᶠU : ℝ in atTop,K< U^wmin :=
    (tendsto_rpow_atTop hwmin).eventually (eventually_gt_atTop K)
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with U hlarge hU
  refine ⟨hU,?_⟩
  intro w hw j
  have hj : ((DetectorDictionaryInverseRawInitialGates.deletedBase
      (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ)≤ K :=
    by
      dsimp only [K]
      exact Finset.single_le_sum (f := fun j : WholeSourceIndex M H=>
        ((DetectorDictionaryInverseRawInitialGates.deletedBase
          (momentData (cleanWholeBase M H hH η η₀ j))).modulus.absNorm:ℝ))
        (fun _ _=>by positivity) (Finset.mem_univ j)
  exact (hj.trans_lt hlarge).trans_le (Real.rpow_le_rpow_of_exponent_le hU.le hw)

/-- Physical and normalized heights have exactly the same slot norm. -/
theorem wholeCleanSlot_height_norm {Slot : Type} (η η₀ : Character) (W : ℝ→ℂ) (U : ℝ)
    (hU : 0< U) (w σ v : Slot→ℝ) (t : FreeRow→ℝ) (θ : Slot→RayQuotient.Characters M H)
    (u : FreeRow) (s : Slot) :
    ‖naturalSlot (naturalRow (excluded η (wholeAnchorMask M H hH η₀)) u.val u.property.1).character
      (primePool M H 2 (U^(w s)))
      (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) I*
        HeckePrimeAnnular.annularWeight W (U^(w s)) (σ s) (v s) I) (t u)) (U^(w s))‖=
      ‖wholeCleanSlot M H hH η η₀ W U w σ v t θ u s‖ := by
  apply naturalSlot_height_norm _ _ _ _ _ _ _ _ (Real.rpow_pos_of_pos hU _)
  intro I hI
  exact (Finset.mem_filter.mp hI).2.1.ne_zero

/-- Rescaling the count window does not change the physical slot at all. -/
theorem wholeCleanSlot_rescale {Slot : Type} (η η₀ : Character) (W : ℝ→ℂ) (U d : ℝ)
    (hU : 0< U) (hd : d≠0) (w σ v : Slot→ℝ) (t : FreeRow→ℝ)
    (θ : Slot→RayQuotient.Characters M H) (u : FreeRow) (s : Slot) :
    wholeCleanSlot M H hH η η₀ W (U^d) (fun s=>w s/d) σ v t θ u s=
      wholeCleanSlot M H hH η η₀ W U w σ v t θ u s := by
  have he : (U^d)^(w s/d)=U^(w s) := by
    rw [←Real.rpow_mul hU.le,mul_div_cancel₀ _ hd]
  simp only [wholeCleanSlot,he]

end
end OAI.SevenEighths.Cycle63MarkedPlain
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.eventually_whole_core_norm_caps
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.eventually_whole_core_inverse_large
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.wholeCleanSlot_height_norm
#print axioms OAI.SevenEighths.Cycle63MarkedPlain.wholeCleanSlot_rescale
