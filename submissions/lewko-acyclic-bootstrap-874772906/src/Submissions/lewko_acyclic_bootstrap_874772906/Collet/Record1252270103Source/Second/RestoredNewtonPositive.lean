/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Normalized Newton cofactors and actual finite absolute mass. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredZeroRows
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.FrozenCentered
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Coefficient.NewtonWeightedMass
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredPositive
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Collision.CorrectedRows

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentCommonRadialData
open CenteredMomentSourceRectangleMask ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered Record1252270103Source
local notation "O" => ActualEisensteinCubic.O

/-- The ideal row identity needs no nonzero-character cancellation. -/
theorem frozen_centered_row_excluded (η : Character) (m A z : O)
    (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (A₁ A₂ : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (b t X₁ X₂ Y₁ Y₂ T : ℝ) (hb : 0≤b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Iic b)
    (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Iic b) :
    frozenCenteredRow (rowWeight η m A z t) W₁ W₂ A₁ A₂ b X₁ X₂ Y₁ Y₂ T=
      ((squarefreeIndicator (A₁*A₂):ℂ)*ordinaryHoleIndicator A₁ A₂)*
        centeredSquarefreeRow η (m*idealGenerator (A₁*A₂)) A z W₁ W₂ b t X₁ X₂ Y₁ Y₂ T := by
  rw [centeredSquarefreeRow_common_pool η (m*idealGenerator (A₁*A₂)) A z W₁ W₂
    b t X₁ X₂ Y₁ Y₂ T hb hX₁ hX₂ hY₁ hY₂ hs₁ hs₂]
  unfold frozenCenteredRow
  rw [mul_left_comm _ ((Real.sqrt T:ℂ)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hg := holePairPool_good hn
  have hh := (ordinarySmallHole_iff_good hg.1 hg.2.1).mpr hg
  unfold frozenProfile
  rw [ordinaryHoleIndicator_frozen A₁ A₂ n.1 n.2 hA₁ hA₂ hg.1 hg.2.1 hh,
    squarefree_frozen_mask,←rowWeight_ideal_mask η m A z t hml hm2]
  ring

theorem rowWeight_puncture_product (η : Character) (R Q : Ideal O)
    (A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η ((fixedBadMask*idealGenerator R)*idealGenerator Q) A z t I=
      rowWeight η (fixedBadMask*idealGenerator (R*Q)) A z t I := by
  rw [←rowWeight_ideal_mask η (fixedBadMask*idealGenerator R) A z t
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)),
    ←rowWeight_ideal_mask η fixedBadMask A z t (dvd_mul_right _ _) (dvd_mul_left _ _) R,
    ←rowWeight_ideal_mask η fixedBadMask A z t (dvd_mul_right _ _) (dvd_mul_left _ _) (R*Q)]
  simp only [IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

/-- Frozen ordinary factors already divide R; only the assigned Newton pair
adds a puncture. This equality holds on all ideals, including character zeros. -/
theorem rowWeight_newton_puncture (η : Character) (R A₁ A₂ d₁ d₂ : Ideal O)
    (hAR : A₁*A₂∣R) (A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η ((fixedBadMask*idealGenerator R)*idealGenerator ((A₁*d₁)*(A₂*d₂))) A z t I=
      rowWeight η (fixedBadMask*idealGenerator (R*(d₁*d₂))) A z t I := by
  rw [rowWeight_puncture_product,
    ←rowWeight_ideal_mask η fixedBadMask A z t (dvd_mul_right _ _) (dvd_mul_left _ _),
    ←rowWeight_ideal_mask η fixedBadMask A z t (dvd_mul_right _ _) (dvd_mul_left _ _)]
  have he : IsCoprime I (R*((A₁*d₁)*(A₂*d₂))) ↔ IsCoprime I (R*(d₁*d₂)) := by
    rw [show (A₁*d₁)*(A₂*d₂)=(A₁*A₂)*(d₁*d₂) by ring]
    simp only [IsCoprime.mul_right_iff]
    constructor
    · rintro ⟨hR,hA,hd⟩;exact ⟨hR,hd⟩
    · rintro ⟨hR,hd⟩;exact ⟨hR,IsCoprime.mul_right_iff.mp (hR.of_isCoprime_of_dvd_right hAR),hd⟩
  rw [he]

theorem rowSlot_newton_puncture (η : Character) (R d : Ideal O)
    (A z : O) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O→ℂ)
    (havoid : ∀I∈S,IsCoprime I d) :
    rowSlot η (fixedBadMask*idealGenerator (R*d)) A z S β t=
      rowSlot η (fixedBadMask*idealGenerator R) A z S β t := by
  rw [rowSlot_eq_weight,rowSlot_eq_weight]
  apply Finset.sum_congr rfl
  intro I hI
  rw [←rowWeight_puncture_product,←rowWeight_ideal_mask η (fixedBadMask*idealGenerator R) A z t
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)),if_pos (havoid I hI),one_mul]

theorem sum_powerset_le_by_card {α : Type*} (P : Finset α) (depth : ℕ) (f : Finset α→ℝ) :
    (∑S∈P.powerset.filter (fun S=>S.card≤depth),f S)=
      ∑j∈Finset.range (depth+1),∑S∈P.powersetCard j,f S := by
  simp only [Finset.powersetCard_eq_filter,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [eq_comm,Finset.sum_ite_eq',Finset.mem_range,Nat.lt_succ_iff]

def positiveNewtonWeight (P : Finset (Ideal O)) (D : Ideal O) (S A : Finset (Ideal O)) : ℝ :=
  ‖(newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)‖/
    Real.sqrt (pairNorm (newtonDivisorPair S A))

theorem positive_newton_mass (P : Finset (Ideal O)) (D : Ideal O) (depth : ℕ)
    (hP : 0<P.card) (hnz : ∀p∈P,p≠0)
    (hbudget : 2*((idealDividingPool P D).card+(depth:ℝ)+1)≤P.card) :
    (∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
      positiveNewtonWeight P D S A)≤newtonMassBound depth := by
  rw [sum_powerset_le_by_card]
  have hh := newton_assignment_weighted_mass P hP hnz (idealDividingPool P D).card
    (1/2) depth (by norm_num) hbudget (fun _=>1) (fun _=>by norm_num)
  simpa only [positiveNewtonWeight,newtonDivisorPair,pairNorm,mul_one,Real.sqrt_eq_rpow] using hh

/-- Same-height normalized cofactor expansion. The scalar retains its actual
row character, while each child has the literal divided X and Y scales. -/
theorem corrected_newton_rows_with_slots (P : Finset (Ideal O)) (D M A₁ A₂ : Ideal O)
    (depth : ℕ) (ψ : Ideal O→*₀ℂ) (W₁ W₂ : ℝ→ℂ)
    (b X₁ X₂ Y₁ Y₂ T : ℝ) (hT : 0<T)
    (hp : ∀p∈P,Prime p) (hN : ∀p∈P,16≤p.absNorm) (havoid : ∀p∈P,¬p∣M)
    (hsupport : ∀n∈commonPool b X₁ X₂ Y₁ Y₂,Squarefree ((A₁*n.1)*(A₂*n.2))→
      frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n≠0→
      IsCoprime D (M*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*(M*n.1*n.2))).card<P.card)
    (slots : ℂ) :
    correctedCenteredRow P D M A₁ A₂ ψ W₁ W₂ b X₁ X₂ Y₁ Y₂ T*slots=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        ((newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
          ψ ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)/
          (Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*
        (frozenCenteredRow ψ W₁ W₂ (A₁*(newtonDivisorPair S A).1)
          (A₂*(newtonDivisorPair S A).2) b
          (X₁/(newtonDivisorPair S A).1.absNorm) (X₂/(newtonDivisorPair S A).2.absNorm)
          (Y₁/(newtonDivisorPair S A).1.absNorm) (Y₂/(newtonDivisorPair S A).2.absNorm)
          (T/pairNorm (newtonDivisorPair S A))*slots) := by
  rw [normalized_centered_newton P D M A₁ A₂ depth ψ W₁ W₂ b X₁ X₂ Y₁ Y₂ T hT hp hN havoid hsupport]
  simp only [Finset.sum_mul,mul_assoc]



variable {ι : Type*} [Fintype ι]

def markedNewtonCoefficient (s : Input ι) (K R : Ideal O) (τ : Character) (t : ℝ) (z : O)
    (v : ∀i,s.slots i) : ℂ :=
  QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*∏i,(v i:Ideal O))*
    (∏i,restoredSlotCoeff s i (v i))*rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,(v i:Ideal O))

def markedNewtonSlots (s : Input ι) (K R : Ideal O) (τ : Character) (t : ℝ) (z : O) : ℂ :=
  (Real.sqrt (∏i,s.P i):ℂ)⁻¹*
    ∑v : (∀i,s.slots i),QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*∏i,(v i:Ideal O))*
      (∏i,restoredSlotCoeff s i (v i))*rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,(v i:Ideal O))

/-- Exact whole-source Newton transport after the marked dictionary. The
marked projector and its frozen K remain inside the same finite slot sum;
no divisibility indicator or altered energy is left in the ordinary child. -/
theorem actual_corrected_newton_row (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D K R : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (depth : ℕ) (τ : Character) (t : ℝ) (z : O) (b : ℝ)
    (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b) (hp : ∀p∈P,Prime p) (hN : ∀p∈P,16≤p.absNorm)
    (havoid : ∀v : (∀i,s.slots i),∀p∈P,¬p∣∏i,(v i:Ideal O))
    (hsupport : ∀v : (∀i,s.slots i),markedNewtonCoefficient s K R τ t z v≠0→∀n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂,
      Squarefree ((A₁*n.1)*(A₂*n.2))→frozenProfile s.W₁ s.W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0→
      rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (n.1*n.2)≠0→
      IsCoprime D ((∏i,(v i:Ideal O))*n.1*n.2) ∧ (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P (D*((∏i,(v i:Ideal O))*n.1*n.2))).card<P.card) :
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P)) R 1 τ t z=
      ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
        ((newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
          rowWeight τ (fixedBadMask*idealGenerator R) 1 z t
            ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)/
          (Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*
        (frozenCenteredRow (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂
          (A₁*(newtonDivisorPair S A).1) (A₂*(newtonDivisorPair S A).2) b
          (s.X₁/(newtonDivisorPair S A).1.absNorm) (s.X₂/(newtonDivisorPair S A).2.absNorm)
          (s.Y₁/(newtonDivisorPair S A).1.absNorm) (s.Y₂/(newtonDivisorPair S A).2.absNorm)
          ((s.X₁*s.X₂)/pairNorm (newtonDivisorPair S A))*markedNewtonSlots s K R τ t z) := by
  have hn : (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P)) R 1 τ t z=
      (Real.sqrt (∏i,s.P i):ℂ)⁻¹*((Real.sqrt (s.X₁*s.X₂):ℂ)⁻¹*
        modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (poolCorrection P)) R 1 τ t z) := by
    rw [Real.sqrt_mul (mul_pos s.X₁_pos s.X₂_pos).le]
    simp only [Complex.ofReal_mul,mul_inv_rev,mul_assoc]
  rw [hn,Collision.corrected_marked_seed_one_row s P A₁ A₂ D K R hA₁ hA₂ τ t z b hb₁ hb₂]
  have he (v : ∀i,s.slots i) :
      markedNewtonCoefficient s K R τ t z v*
        correctedCenteredRow P D (∏i,(v i:Ideal O)) A₁ A₂
          (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂ b
          s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂)=
      markedNewtonCoefficient s K R τ t z v*
        ∑S∈P.powerset.filter (fun S=>S.card≤depth),∑A∈S.powerset,
          ((newtonCoefficient P.card (idealDividingPool P D).card S.card:ℂ)*
            rowWeight τ (fixedBadMask*idealGenerator R) 1 z t
              ((newtonDivisorPair S A).1*(newtonDivisorPair S A).2)/
            (Real.sqrt (pairNorm (newtonDivisorPair S A)):ℂ))*
          frozenCenteredRow (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂
            (A₁*(newtonDivisorPair S A).1) (A₂*(newtonDivisorPair S A).2) b
            (s.X₁/(newtonDivisorPair S A).1.absNorm) (s.X₂/(newtonDivisorPair S A).2.absNorm)
            (s.Y₁/(newtonDivisorPair S A).1.absNorm) (s.Y₂/(newtonDivisorPair S A).2.absNorm)
            ((s.X₁*s.X₂)/pairNorm (newtonDivisorPair S A)) := by
    by_cases hz : markedNewtonCoefficient s K R τ t z v=0
    · simp only [hz,zero_mul]
    · rw [normalized_centered_newton_nonzero P D (∏i,(v i:Ideal O)) A₁ A₂ depth
        (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂ b
        s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) (mul_pos s.X₁_pos s.X₂_pos) hp hN (havoid v) (hsupport v hz)]
  change (Real.sqrt (∏i,s.P i):ℂ)⁻¹*(∑v : (∀i,s.slots i),
    markedNewtonCoefficient s K R τ t z v*correctedCenteredRow P D (∏i,(v i:Ideal O)) A₁ A₂
      (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t) s.W₁ s.W₂ b
      s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂))=_
  simp_rw [he,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  unfold markedNewtonSlots
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  unfold markedNewtonCoefficient
  ring

end
end OAI.SevenEighths.Record1252270103Second
#print axioms OAI.SevenEighths.Record1252270103Second.frozen_centered_row_excluded
#print axioms OAI.SevenEighths.Record1252270103Second.rowWeight_newton_puncture
#print axioms OAI.SevenEighths.Record1252270103Second.positive_newton_mass
#print axioms OAI.SevenEighths.Record1252270103Second.corrected_newton_rows_with_slots

#print axioms OAI.SevenEighths.Record1252270103Second.actual_corrected_newton_row
