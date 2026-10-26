/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An actual ordinary lower-parent family supplies the squarefree projected subsets
through checked divisor/hole restoration and collision inclusion-exclusion. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalInitialSubsets
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.ForwardFull
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentInductionEnergy
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.Collision
local notation "O"=>HeckeFamily.O
variable {ι : Type*} [Fintype ι]

/-- This premise is the literal smaller-parent ordinary energy on every
surviving subset and shortened pair. It is not a bound for a modified row. -/
theorem projected_subsets_of_ordinary_parent
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (atoms : Finset (Ideal O)) (hS : ∀i,S i⊆atoms)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,1≤P i) (hK : 0<K)
    (hΦ : ∀x,0≤(Φ x).re) (Bcoeff E : ℝ) (hBcoeff : 1≤Bcoeff) (hE : 0≤E)
    (hβ : ∀i I,I∈S i → ‖β i I‖≤Bcoeff)
    (hp : ∀i I,I∈S i → I≠0) (hN : ∀i I,I∈S i → (I.absNorm:ℝ)≤2*P i)
    (δ B U : ℝ) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U) (hcut : b^2*X₁*X₂≤U^B)
    (hparent : ∀F : Finset ι,∀Y₁ Y₂ : ℝ,0<Y₁ → 0<Y₂ → Y₁≤X₁ → Y₂≤X₂ →
      energy η m A t W₁ W₂ (fun i:F=>S i) (fun i:F=>β i) (fun i:F=>P i)
        Y₁ Y₂ keep Φ K≤E)
    (rows : Finset O) :
    projectedSubsetBound rows
      (fun z i (p : atoms)=>normalizedRowCoeff η m A z t (S i) (β i) (P i) p)
      (weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ K)
      (collisionProjectionCost Bcoeff 256 (Fintype.card ι)*
        (holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
          eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E) := by
  let mass:=holeDeletionMass*((eulerBound 5 (1/2+δ/(B+1))+
    eulerBound 432 (1/2+δ/(B+1)))*U^δ)
  have hP0 (i : ι) : 0<P i:=zero_lt_one.trans_le (hP i)
  have hsf (F : Finset ι) : squarefreeEnergy η m A t W₁ W₂ b
      (fun i:F=>S i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ keep Φ K≤mass^2*E :=
    forward_energy_transfer η m A W₁ W₂ b hs₁ hs₂ (fun i:F=>S i)
      (fun i:F=>β i) (fun i:F=>P i) (fun i=>hP0 i) t X₁ X₂ hX₁ hX₂ keep Φ K hK
      hΦ E hE δ B U hδ hB hU hcut (hparent F)
  have hfull:=fullSubsetBound_of_squarefree_subsets η m A t W₁ W₂ b X₁ X₂ keep Φ K
    S β P atoms hS hX₁ hX₂ hP0 hK hΦ (mass^2*E) hsf rows
  have hh:=normalized_projectedSubsetBound_of_fullSubsetBound η m A t rows
    (weightedPlain η m A t W₁ W₂ b X₁ X₂ keep Φ K) S β P atoms Bcoeff (mass^2*E)
    hBcoeff (mul_nonneg (sq_nonneg _) hE) hP hβ hp hN (Fintype.card ι) le_rfl hfull
  simpa only [mass,mul_assoc] using hh

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.projected_subsets_of_ordinary_parent
