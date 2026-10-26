/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Joint exact Newton and collision extraction to full original singleton families. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.JointNewtonFamily
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalSupportedCollision
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open HeckeFamily ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion QRH.Record1252270103Source.Collision
open CenteredMomentAbsoluteEnergy Record1252270103Source Record1252270103Second
open QRH.Record1252270103Low QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered High.GlobalPhysical
local notation "O"=>ActualEisensteinCubic.O

theorem actual_joint_corrected_newton_supported_subsets {α Row : Type*} [Fintype α]
    (rows : Finset Row) (ι : Row→Type*) [∀u,Fintype (ι u)]
    (s : ∀u,Input (ι u)) (embedding : ∀u,ι u↪α)
    (S₀ : α→Finset (Ideal O)) (β₀ : α→Ideal O→ℂ) (P₀ : α→ℝ)
    (hslots : ∀u i,(s u).slots i=S₀ (embedding u i))
    (hcoeff : ∀u i,restoredSlotCoeff (s u) i=β₀ (embedding u i))
    (hscale : ∀u i,(s u).P i=P₀ (embedding u i))
    (P : Finset (Ideal O)) (A₁ A₂ D K R : Row→Ideal O)
    (hA₁ : ∀u∈rows,A₁ u≠0) (hA₂ : ∀u∈rows,A₂ u≠0) (depth : ℕ)
    (τ : Row→Character) (t : Row→ℝ) (z : Row→O) (weight : Row→ℝ)
    (hw : ∀u∈rows,0≤weight u) (b : Row→ℝ)
    (hb₁ : ∀u∈rows,(s u).b₁≤b u) (hb₂ : ∀u∈rows,(s u).b₂≤b u)
    (hp : ∀p∈P,Prime p) (hN : ∀p∈P,16≤p.absNorm)
    (havoid : ∀u∈rows,∀v : (∀i,(s u).slots i),∀p∈P,¬p∣∏i,(v i:Ideal O))
    (hsupport : ∀u∈rows,∀v : (∀i,(s u).slots i),
      markedNewtonCoefficient (s u) (K u) (R u) (τ u) (t u) (z u) v≠0→
      ∀n∈commonPool (b u) (s u).X₁ (s u).X₂ (s u).Y₁ (s u).Y₂,
      Squarefree (((A₁ u)*n.1)*((A₂ u)*n.2))→
      frozenProfile (s u).W₁ (s u).W₂ (A₁ u) (A₂ u) (s u).X₁ (s u).X₂ (s u).Y₁ (s u).Y₂ n≠0→
      rowWeight (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u) (t u) (n.1*n.2)≠0→
      IsCoprime (D u) ((∏i,(v i:Ideal O))*n.1*n.2) ∧
        (idealDividingPool P (n.1*n.2)).card≤depth ∧
        (idealDividingPool P ((D u)*((∏i,(v i:Ideal O))*n.1*n.2))).card<P.card)
    (hP : 0<P.card)
    (hbudget : ∀u∈rows,2*((idealDividingPool P (D u)).card+(depth:ℝ)+1)≤P.card)
    (E : ℝ) (hE : 0≤E) (hKR : ∀u,K u∣R u)
    (Bslot : ℝ) (hBslot : 1≤Bslot) (hP₀ : ∀i,1≤P₀ i)
    (hβ₀ : ∀i,∀p∈S₀ i,‖β₀ i p‖≤Bslot) (hprime₀ : ∀i,∀p∈S₀ i,Prime p)
    (hnorm₀ : ∀i,∀p∈S₀ i,(p.absNorm:ℝ)≤2*P₀ i)
    (N : ℕ) (hcard : Fintype.card α≤N)
    (hchild : ∀S∈P.powerset.filter (fun S=>S.card≤depth),∀A∈S.powerset,∀T : Finset α,
      (∑u∈rows.filter (fun u=>T⊆Finset.univ.map (embedding u)),‖newtonCofactorPlain (s u) (A₁ u) (A₂ u) (R u) (b u) S A (τ u) (t u) (z u)*
        (∏j:T,normalizedSlot (τ u) (fixedBadMask*idealGenerator (R u)) 1 (z u)
          (S₀ j) (β₀ j) (t u) (P₀ j))‖^2*weight u)≤E) :
    (∑u∈rows,‖(Real.sqrt ((s u).X₁*(s u).X₂*∏i,(s u).P i):ℂ)⁻¹*
      modifiedSourceRow (s u)
        (Collision.markedSourceModifier (A₁ u) (A₂ u) (D u) (K u) (poolCorrection P))
        (R u) 1 (τ u) (t u) (z u)‖^2*weight u)≤newtonMassBound depth^2*(collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E)) := by
  have hc : 0≤collisionProjectionCost Bslot 256 N := by unfold collisionProjectionCost;positivity
  apply Admission.JointNewton.actual_joint_corrected_newton_finite rows ι s P A₁ A₂ D K R
    hA₁ hA₂ depth τ t z weight hw b hb₁ hb₂ hp hN havoid hsupport hP hbudget
    (collisionProjectionCost Bslot 256 N*((2:ℝ)^N*E)) (mul_nonneg hc (mul_nonneg (by positivity) hE))
  intro S hS A hA
  exact marked_subfamily_supported_joint_energy ι s embedding S₀ β₀ P₀ hslots hcoeff hscale
    K R hKR τ t z
    (fun u=>newtonCofactorPlain (s u) (A₁ u) (A₂ u) (R u) (b u) S A (τ u) (t u) (z u))
    rows weight hw Bslot E hBslot hE hP₀ hβ₀ hprime₀ hnorm₀ N hcard (hchild S hS A hA)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_joint_corrected_newton_supported_subsets
