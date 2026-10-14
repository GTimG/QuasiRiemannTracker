/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B084
import Candidate.Bundles.B085
import Candidate.Bundles.B094
import OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.ChildDictionary; sha256 f9f17bd70cca06b0c1afa2fb76984ca7287cf176dadb15344233e2c16efd3b99 -/
section
                                             
                                                                  
                                                                 

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentAmplificationChildInput CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α]
local instance {ι : Type*} : DecidableEq ι := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual allocated child is the literal relative prime-ray family on
its surviving labels. Both plain norm cutoffs and the puncture remain exact. -/
theorem child_ray_energy
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ v W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (χ : Character) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := child s C R B χ t
    energy c.η c.m 1 t c.W₁ c.W₂ c.slots c.toData.coefficient c.P
      c.X₁ c.X₂ keep Φ K =
    energy χ (fixedBadMask*idealGenerator (R*C)) 1 t s.W₁ s.W₂
      (fun j : liveIndices B.val => primePool M H bslot (Z^(w j)))
      (fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I)
      (fun j : liveIndices B.val => Z^(w j))
      (s.X₁/(B.val (Sum.inr 0)).absNorm) (s.X₂/(B.val (Sum.inr 1)).absNorm)
      keep Φ K := by
  dsimp only
  have hpool : (child s C R B χ t).slots =
      fun j : liveIndices B.val => primePool M H bslot (Z^(w j)) := by
    funext j
    exact hm.pool j
  have hscale : (child s C R B χ t).P =
      fun j : liveIndices B.val => Z^(w j) := by
    funext j
    exact hm.scale j
  have hcoeff : (child s C R B χ t).toData.coefficient =
      fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I := by
    funext j I
    change s.ν j.val I*s.W j.val ((I.absNorm:ℝ)/s.P j.val) = _
    rw [hm.character,hm.profile,hm.scale]
    rfl
  rw [hpool,hscale,hcoeff]
  rfl

/-- The same dictionary covers the second rectangle without equating its
individual scales to the first rectangle. -/
theorem child_reference_ray_energy
    (s : Input α) (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ v : α → ℝ) (W : ℝ → ℂ) (bslot Z : ℝ)
    (hm : Matches M H hH s η₀ θ w σ v W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (χ : Character) (t : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := child s C R B χ t
    energy c.η c.m 1 t c.W₁ c.W₂ c.slots c.toData.coefficient c.P
      c.Y₁ c.Y₂ keep Φ K =
    energy χ (fixedBadMask*idealGenerator (R*C)) 1 t s.W₁ s.W₂
      (fun j : liveIndices B.val => primePool M H bslot (Z^(w j)))
      (fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I)
      (fun j : liveIndices B.val => Z^(w j))
      (s.Y₁/(B.val (Sum.inr 0)).absNorm) (s.Y₂/(B.val (Sum.inr 1)).absNorm)
      keep Φ K := by
  dsimp only
  have hpool : (child s C R B χ t).slots =
      fun j : liveIndices B.val => primePool M H bslot (Z^(w j)) := by
    funext j; exact hm.pool j
  have hscale : (child s C R B χ t).P =
      fun j : liveIndices B.val => Z^(w j) := by
    funext j; exact hm.scale j
  have hcoeff : (child s C R B χ t).toData.coefficient =
      fun (j : liveIndices B.val) I => idealCoeff (relativeCharacter M H hH η₀ (θ j)) I*
        annularWeight W (Z^(w j)) (σ j) (v j) I := by
    funext j I
    change s.ν j.val I*s.W j.val ((I.absNorm:ℝ)/s.P j.val) = _
    rw [hm.character,hm.profile,hm.scale]; rfl
  rw [hpool,hscale,hcoeff]
  rfl

#print axioms child_ray_energy
#print axioms child_reference_ray_energy
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.ChildDictionary -/

/- BEGIN ORIGINAL Cycle61.Moment.LowBranch.FinalDictionary; sha256 846b736af2d7e1602a94e83cadc351c6bbf7846f95dd7fd9ecd6977d7332d5a3 -/
section
                                               
                                             

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment.LowBranch
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcreteTraceCRT CenteredMomentCommonRadialData
open CenteredMomentEligibleEnergy CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The literal final positive daughter aggregate, after the second common
allocation and residual squarefree allocation. No radial or row supremum. -/
def finalPositiveEnergy (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then
    ‖Cycle61.Physical.sourcePositiveRow s.toSource second L a z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0

/-- Exact identification of the final aggregate with the old moment energy.
Only the two retained plain cutoffs are clipped; the puncture and slot widths
are unchanged. The two rectangles are addressed independently. -/
theorem final_positive_energy_eq (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2)))
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let X := Cycle61.Physical.sourcePlainScales s.toSource second
    let X₁ := X 0/(Ideal.absNorm (selectedPlain L a 0):ℝ)
    let X₂ := X 1/(Ideal.absNorm (selectedPlain L a 1):ℝ)
    finalPositiveEnergy s second L a keep Φ K =
      energy s.η s.m s.A s.t (dilated s.W₁ (clipDilation X₁))
        (dilated s.W₂ (clipDilation X₂))
        (fun i : liveIndices L a => s.slots i)
        (fun i : liveIndices L a => s.coefficient i)
        (fun i : liveIndices L a => s.P i)
        (clippedScale X₁) (clippedScale X₂) keep Φ K := by
  rfl

/-- Exact final daughter scales, including the independent rectangle. -/
def finalPlain (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (j : Fin 2) : ℝ :=
  clippedScale (Cycle61.Physical.sourcePlainScales s.toSource second j/
    (Ideal.absNorm (selectedPlain L a j):ℝ))

/-- Literal dictionary transport to a natural state. These are coefficient,
mask and scale identities, rather than an assumed analytic estimate. -/
theorem final_energy_eq_natural
    {Z Bmask bΦ ap bp : ℝ} (st : CenteredMomentEnergyState.NaturalState Z Bmask bΦ)
    (p : CenteredMomentFiniteProfileExceptional.Profiles ap bp) (s : Data α) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (α ⊕ Fin 2))) (J : Finset α)
    (pool : α → Finset (Ideal O)) (coeff : α → Ideal O → ℂ) (P : α → ℝ)
    (t X₁ X₂ : ℝ) (low : O → Prop)
    (hJ : liveIndices L a = J) (hchar : s.η = st.character)
    (hmask : s.m = st.mask) (hA : s.A = 1) (ht : s.t = t)
    (hpool : ∀ j, s.slots j = pool j) (hcoeff : ∀ j I, s.coefficient j I = coeff j I)
    (hP : ∀ j, s.P j = P j)
    (hp₁ : dilated s.W₁ (clipDilation
      (Cycle61.Physical.sourcePlainScales s.toSource second 0/(Ideal.absNorm (selectedPlain L a 0):ℝ))) = p.profile 0)
    (hp₂ : dilated s.W₂ (clipDilation
      (Cycle61.Physical.sourcePlainScales s.toSource second 1/(Ideal.absNorm (selectedPlain L a 1):ℝ))) = p.profile 1)
    (hX₁ : finalPlain s second L a 0 = X₁) (hX₂ : finalPlain s second L a 1 = X₂) :
    finalPositiveEnergy s second L a (fun z => st.radial.keep z ∧ low z)
      st.radial.profile st.radial.scale =
    energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
      (fun j : J => pool j) (fun j : J => coeff j) (fun j : J => P j)
      X₁ X₂ (fun z => st.radial.keep z ∧ low z) st.radial.profile st.radial.scale := by
  rw [final_positive_energy_eq]
  rw [hchar,hmask,hA,ht,hp₁,hp₂]
  change energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
    (fun j : liveIndices L a => s.slots j) (fun j : liveIndices L a => s.coefficient j)
    (fun j : liveIndices L a => s.P j) (finalPlain s second L a 0) (finalPlain s second L a 1)
    (fun z => st.radial.keep z ∧ low z) st.radial.profile st.radial.scale = _
  simp_rw [hpool, funext (hcoeff _), hP]
  rw [hJ,hX₁,hX₂]

#print axioms final_energy_eq_natural
#print axioms final_positive_energy_eq
end
end OAI.SevenEighths.Cycle61Moment.LowBranch

end
/- END ORIGINAL Cycle61.Moment.LowBranch.FinalDictionary -/

/- BEGIN ORIGINAL Cycle61.Moment.FinalRowDictionary; sha256 9c51ae587f27f739c7f92a24e0ad9a87976cd61238e97535b8d9e725bf35fee6 -/
section
                                      
                                               

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentEnergyState CenteredMomentEligibleEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual residual allocation changes its two raw plain scales and
restricts the live slot index. It does not change the row mask or frequency. -/
theorem final_source_row_eq
    {Z Bmask bΦ : ℝ} (st : NaturalState Z Bmask bΦ)
    (src : Data ι) (second : Bool) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (pool : ι → Finset (Ideal O)) (coeff : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t : ℝ) (z : O)
    (hchar : src.η = st.character) (hmask : src.m = st.mask)
    (hA : src.A = 1) (ht : src.t = t)
    (hpool : ∀ j, src.slots j = pool j)
    (hcoeff : ∀ j I, src.coefficient j I = coeff j I)
    (hP : ∀ j, src.P j = P j) :
    Cycle61.Physical.sourcePositiveRow src.toSource second L a z =
      retainedPositiveRow st.character st.mask 1 z src.W₁ src.W₂
        (fun j : liveIndices L a => pool j)
        (fun j : liveIndices L a => coeff j)
        (fun j : liveIndices L a => P j) t
        (Cycle61.Physical.postPlainScale L a
          (Cycle61.Physical.sourcePlainScales src.toSource second) 0)
        (Cycle61.Physical.postPlainScale L a
          (Cycle61.Physical.sourcePlainScales src.toSource second) 1) := by
  change retainedPositiveRow src.η src.m src.A z src.W₁ src.W₂
    (fun j : liveIndices L a => src.slots j)
    (fun j : liveIndices L a => src.coefficient j)
    (fun j : liveIndices L a => src.P j) src.t _ _ = _
  rw [hchar,hmask,hA,ht]
  simp_rw [hpool, funext (hcoeff _), hP]
  rfl

#print axioms final_source_row_eq
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.FinalRowDictionary -/

/- BEGIN ORIGINAL Cycle61.Moment.HighAllocationLedger; sha256 0eb9e4073d2f464bfe08d563abfb3261f4fed89375e96db24edbf91abf733efe -/
section
                                          
                                                                 

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile
open CenteredMomentAllocatedChildCapacity CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact total width of the final positive row, with the two clipped plains
and only live slots. Both pre- and post-clipping losses remain in the actual
reduction; frozen original slots are charged exactly once. -/
theorem actual_high_allocation_total
    (Z : ℝ) (hZ : 1 < Z) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (P : ι → ℝ) (hP : ∀ i, 0 < P i) :
    (∑ j, Real.logb Z (clippedScale (Cycle61.Physical.postPlainScale L a X j)))+
      (∑ i ∈ liveIndices L a, Real.logb Z (P i)) =
    (∑ j, Real.logb Z (clippedScale (X j)))+(∑ i, Real.logb Z (P i))-
      Cycle61.Physical.clippedReduction (Real.logb Z (formalReductionFactor L a P))
        (fun j => Real.logb Z (X j)) (Cycle61.Physical.actualPlainReduction Z L a) := by
  have hraw := raw_log_volume L a Z (X 0) (X 1) (hX 0) (hX 1) P hP
  have hpre : Real.logb Z (X 0*X 1*∏ i,P i) =
      Real.logb Z (X 0)+Real.logb Z (X 1)+(∑ i, Real.logb Z (P i)) := by
    rw [Real.logb_mul (mul_pos (hX 0) (hX 1)).ne'
      (Finset.prod_pos (fun i _ => hP i)).ne',
      Real.logb_mul (hX 0).ne' (hX 1).ne',Real.logb_prod _ _ (fun i _ => (hP i).ne')]
  rw [hpre] at hraw
  have hc (j : Fin 2) := clipped_log Z (X j) hZ (hX j)
  have hp (j : Fin 2) := clipped_log Z (Cycle61.Physical.postPlainScale L a X j)
    hZ (Cycle61.Physical.postPlainScale_pos L a X hX j)
  simp only [Cycle61.Physical.postPlainScale_log Z L a X hX] at hp
  simp only [Fin.sum_univ_two]
  rw [hp 0,hp 1,hc 0,hc 1]
  unfold Cycle61.Physical.clippedReduction Cycle61.Physical.negativeTotal
  simp only [Fin.sum_univ_two,max_comm (0 : ℝ)]
  change Real.logb Z (rawScale L a (X 0) 0)+
    Real.logb Z (rawScale L a (X 1) 1)+remainingLogs L a Z P = _ at hraw
  change Real.logb Z (X 0)-Cycle61.Physical.actualPlainReduction Z L a 0+
    max (-(Real.logb Z (X 0)-Cycle61.Physical.actualPlainReduction Z L a 0)) 0+
    (Real.logb Z (X 1)-Cycle61.Physical.actualPlainReduction Z L a 1+
      max (-(Real.logb Z (X 1)-Cycle61.Physical.actualPlainReduction Z L a 1)) 0)+
    remainingLogs L a Z P = _
  have hr (j : Fin 2) : Real.logb Z (rawScale L a (X j) j) =
      Real.logb Z (X j)-Cycle61.Physical.actualPlainReduction Z L a j :=
    Cycle61.Physical.postPlainScale_log Z L a X hX j
  rw [hr 0,hr 1] at hraw
  linarith

theorem actual_high_allocation_total_le
    (Z : ℝ) (hZ : 1 < Z) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (P : ι → ℝ) (hP : ∀ i, 1 ≤ P i) :
    (∑ j, Real.logb Z (clippedScale (Cycle61.Physical.postPlainScale L a X j)))+
      (∑ i ∈ liveIndices L a, Real.logb Z (P i)) ≤
    (∑ j, Real.logb Z (clippedScale (X j)))+(∑ i, Real.logb Z (P i)) := by
  rw [actual_high_allocation_total Z hZ L a X hX P
    (fun i => zero_lt_one.trans_le (hP i))]
  exact sub_le_self _ (Cycle61.Physical.actual_clipped_reduction_nonneg Z hZ L a P hP _)

/-- The high-bin pointwise exponent is the literal pre-allocation total minus
its actual clipped reduction. No bound on residual projector divisibility is
used in this identity. -/
theorem actual_high_allocation_exponent
    (Z : ℝ) (hZ : 1 < Z) (L : Ideal O)
    (a : Allocation L (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (w : ι → ℝ) (d : ℝ) (r : Fin 2 → ℝ)
    (hscale : ∀ j, clippedScale (Cycle61.Physical.postPlainScale L a X j) = (Z^d)^(r j)) :
    d*(r 0+r 1)+(∑ i ∈ liveIndices L a, w i) =
      (∑ j, Real.logb Z (clippedScale (X j)))+(∑ i, w i)-
        Cycle61.Physical.clippedReduction
          (Real.logb Z (formalReductionFactor L a (fun i => Z^(w i))))
          (fun j => Real.logb Z (X j)) (Cycle61.Physical.actualPlainReduction Z L a) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hh := actual_high_allocation_total Z hZ L a X hX (fun i => Z^(w i))
    (fun _ => Real.rpow_pos_of_pos hZp _)
  have hr (j : Fin 2) :
      Real.logb Z (clippedScale (Cycle61.Physical.postPlainScale L a X j)) = d*r j := by
    rw [hscale j,←Real.rpow_mul hZp.le,Real.logb_rpow hZp hZ.ne']
  simp_rw [Real.logb_rpow hZp hZ.ne',hr] at hh
  simpa only [Fin.sum_univ_two,mul_add] using hh

#print axioms actual_high_allocation_exponent
#print axioms actual_high_allocation_total
#print axioms actual_high_allocation_total_le
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.HighAllocationLedger -/
