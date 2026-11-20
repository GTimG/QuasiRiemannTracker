/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite authentic two-anchor energies. A common physical mark is represented
at each anchor by an exact norm equality, not by a new analytic bound. -/
import Candidate.C092.transport.StrongPairBase

set_option autoImplicit false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily CenteredMomentNaturalFixedRaySource
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorEnergyInitialState
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

/-- Both ordinary factors are the literal original columns, with separate
fixed characters, tests and heights. The single physical mark is unchanged. -/
def finiteEnergy {Slot : Type} [Fintype Slot]
    (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ → ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ) : ℝ :=
  ∑ u ∈ s, ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
    ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
    ∏ i, ‖mark i u‖^2

/-- Ordering permutes the complete ordinary tuples; it changes neither the
physical marks nor the finite retained rows. -/
theorem finiteEnergy_swap {Slot : Type} [Fintype Slot]
    (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ → ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ) :
    finiteEnergy s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark =
    finiteEnergy s η₂ η₁ W₂ W₁ t₂ t₁ X₂ X₁ mark := by
  apply Finset.sum_congr rfl
  intro u hu
  ring

/-- Exact finite Cauchy on a partition of the original whole slots. -/
theorem finite_split_cauchy {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (F : Finset Slot) (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ → ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ) :
    finiteEnergy s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      Real.sqrt (∑ u ∈ s, (‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
        ∏ i ∈ F, ‖mark i u‖^2)^2)*
      Real.sqrt (∑ u ∈ s, (‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
        ∏ i ∈ Finset.univ\F, ‖mark i u‖^2)^2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun u => ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
      ∏ i ∈ F, ‖mark i u‖^2)
    (fun u => ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
      ∏ i ∈ Finset.univ\F, ‖mark i u‖^2)
  apply le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro u hu
  have hp := Finset.prod_sdiff (f:=fun i => ‖mark i u‖^2) (Finset.subset_univ F)
  dsimp
  rw [←hp]
  ring

/-- The same original finite energy restricted to an actual whole-slot subproduct. -/
def finiteEnergyOn {Slot : Type} [Fintype Slot]
    (T : Finset Slot) (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ → ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ) : ℝ :=
  ∑ u ∈ s, ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
    ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
    ∏ i∈T, ‖mark i u‖^2

/-- Exact finite Cauchy on a partition of the original whole slots. -/
theorem finite_split_cauchy_on {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (T F : Finset Slot) (hFT : F⊆T) (s : Finset FreeRow) (η₁ η₂ : Character) (W₁ W₂ : ℝ → ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (mark : Slot → FreeRow → ℂ) :
    finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ mark ≤
      Real.sqrt (∑ u ∈ s, (‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
        ∏ i ∈ F, ‖mark i u‖^2)^2)*
      Real.sqrt (∑ u ∈ s, (‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
        ∏ i ∈ T\F, ‖mark i u‖^2)^2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun u => ‖original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ t₁ X₁‖^2*
      ∏ i ∈ F, ‖mark i u‖^2)
    (fun u => ‖original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ t₂ X₂‖^2*
      ∏ i ∈ T\F, ‖mark i u‖^2)
  apply le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro u hu
  have hp := Finset.prod_sdiff (f:=fun i => ‖mark i u‖^2) hFT
  dsimp
  rw [←hp]
  ring

/-- Each Cauchy arm is a genuine native marked fourth on the SAME rows.
Only equality of its slot norms to the actual common mark is required. -/
theorem finite_arm {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (F : Finset Slot) (s : Finset FreeRow) (η : Character) (W : ℝ → ℂ)
    (pool : Slot → Finset (Ideal O)) (coeff : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (t X b Y : ℝ) (mark : Slot → FreeRow → ℂ)
    (hs : Function.support W ⊆ Set.Iic b) (hX : 0 < X)
    (hP : ∀ i, 0 < P i) (hY : 0 < Y) (keep : O → Prop)
    (hk : ∀ u ∈ s, keep u.val) (hy : ∀ u ∈ s, rowNorm u ≤ Y)
    (hmark : ∀ u ∈ s, ∀ i ∈ F, ‖mark i u‖ =
      ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val (pool i) (coeff i) t (P i)‖) :
    (∑ u ∈ s, (‖original η (fixedBadMask*idealGenerator 1) 1 u.val W t X‖^2*
      ∏ i ∈ F, ‖mark i u‖^2)^2) ≤
    subsetEnergy (duplicated F) η (fixedBadMask*idealGenerator 1) 1 t W W
      (fun j : Fin 2×Slot=>pool j.2) (fun j : Fin 2×Slot=>coeff j.2) (fun j : Fin 2×Slot=>P j.2) X X keep radialMajorant Y := by
  have h := finite_selected_energy (duplicated F) η (fixedBadMask*idealGenerator 1) 1 W W
    (fun j : Fin 2×Slot=>pool j.2) (fun j : Fin 2×Slot=>coeff j.2) (fun j : Fin 2×Slot=>P j.2) t X X b b Y
    hs hs hX hX (fun j : Fin 2×Slot=>hP j.2) hY s keep hk hy
  apply le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro u hu
  have hp : (∏ i ∈ F, ‖mark i u‖^2) =
      ∏ i ∈ F, ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val (pool i) (coeff i) t (P i)‖^2 := by
    exact Finset.prod_congr rfl (fun i hi => congrArg (fun x:ℝ=>x^2) (hmark u hu i hi))
  rw [hp]
  simp only [duplicated,Finset.prod_product,Fin.prod_univ_two,norm_mul]
  ring

#print axioms finite_split_cauchy
#print axioms finite_arm
end
end QRH.Cycle092.StrongPair
