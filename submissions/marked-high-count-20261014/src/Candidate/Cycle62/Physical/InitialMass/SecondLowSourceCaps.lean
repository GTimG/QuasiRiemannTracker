/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle62.Physical.InitialMass.SecondSourceControls
import Candidate.Cycle62.Moment.LowBranch.SideGeometry

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle62InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily Cycle62Moment.LowBranch
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentSlotRatios
open CenteredMomentCommonProfile CenteredMomentCommonHeightEnvelope
open CenteredMomentAmplificationChildInput CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw
local notation "O" => HeckeFamily.O

/-- Taking a residual plain divisor and clipping at one cannot exceed
the corresponding original plain scale clipped at one. -/
theorem final_plain_le_original_max {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Data ι) (second : Bool) (D : Ideal O)
    (alloc : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (j : Fin 2) :
    finalPlain s second D alloc j≤max 1 (Cycle62.Physical.sourcePlainScales s.toSource second j) := by
  have hn : (1:ℝ)≤(Ideal.absNorm (selectedPlain D alloc j):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ alloc (Sum.inr j)))
  have hx := source_plain_positive s second j
  change max 1 (Cycle62.Physical.sourcePlainScales s.toSource second j/
    (Ideal.absNorm (selectedPlain D alloc j):ℝ))≤_
  exact max_le_max_left 1 (div_le_self hx.le hn)

/-- Both common allocations and the residual projector only shrink plain
scales. This cap holds simultaneously for every supported allocation. -/
theorem actual_two_common_final_plain_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (bound : ℝ) (hbound : 1≤bound)
    (hplain : ∀side j,Cycle62.Physical.sourcePlainScales s.toData.toSource side j≤bound)
    (C₁ R₁ : Ideal O) (B₁ : actualAllocations s.pools C₁) (χ₁ : Character) (t₁ : ℝ)
    (C₂ R₂ : Ideal O) (B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
    (χ₂ : Character) (t₂ : ℝ)
    (D : Ideal O)
    (alloc : Allocation D (Finset.univ : Finset ((liveIndices B₂.val)⊕Fin 2)))
    (side : Bool) (j : Fin 2) :
    finalPlain (commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂)
      side D alloc j≤bound := by
  apply (final_plain_le_original_max _ side D alloc j).trans
  apply max_le hbound
  have hsecond := actual_child_plain_scale_le
    (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂ χ₂ t₂ side j
  have hfirst := actual_child_plain_scale_le s C₁ R₁ B₁ χ₁ t₁ side j
  exact hsecond.trans (hfirst.trans (hplain side j))

/-- The two universal input gates of the low column theorem follow from
fixed original window and plain-scale bounds, uniformly in both allocations. -/
theorem eventual_two_common_low_source_caps (N : ℕ) (window bs pad L : ℝ)
    (hwindow : 0≤window) (hbs : 1≤bs) (hpad : 0<pad) (hL : 0≤L) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤N → (∀i,logWindow (s.lo i) (s.hi i)≤window) →
      s.b₁≤bs → s.b₂≤bs →
      (∀side j,Cycle62.Physical.sourcePlainScales s.toData.toSource side j≤Z^L) →
      ∀(C₁ R₁ : Ideal O)(B₁ : actualAllocations s.pools C₁)(χ₁ : Character)(t₁ : ℝ)
        (C₂ R₂ : Ideal O)(B₂ : actualAllocations (child s C₁ R₁ B₁ χ₁ t₁).pools C₂)
        (χ₂ : Character)(t₂ : ℝ),
      let src := commonData (withHeight (child s C₁ R₁ B₁ χ₁ t₁) χ₂ t₂) C₂ R₂ B₂
      src.toSource.allowance Z≤pad ∧
        ∀(D : Ideal O)(alloc : Allocation D (Finset.univ : Finset ((liveIndices B₂.val)⊕Fin 2)))
          (side : Bool)(j : Fin 2),finalPlain src side D alloc j≤Z^L := by
  filter_upwards [eventual_two_common_allowance N window bs pad hwindow hbs hpad] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s hcard hw hb₁ hb₂ hplain C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂ src
  have ha := hz.2 s hcard hw hb₁ hb₂ C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂
  have hc : 0≤Cycle62.Physical.plainClipAllowance Z ![src.b₁,src.b₂] := by
    unfold Cycle62.Physical.plainClipAllowance
    exact Finset.sum_nonneg (fun j _=>Real.logb_nonneg hz.1 (le_max_left _ _))
  refine ⟨by linarith,?_⟩
  intro D alloc side j
  exact actual_two_common_final_plain_cap s (Z^L) (Real.one_le_rpow hz.1.le hL) hplain
    C₁ R₁ B₁ χ₁ t₁ C₂ R₂ B₂ χ₂ t₂ D alloc side j

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.final_plain_le_original_max
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_two_common_final_plain_cap

#print axioms OAI.SevenEighths.Cycle62InitialMass.eventual_two_common_low_source_caps
