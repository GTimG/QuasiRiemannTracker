/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Canonical full-subset ordinary parent supplier at every positive shortening. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.Canonical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Reference.SlotBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentEnergyBands
open QRH.Record12518109Source QRH.Record1252270103Reference
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

/-- The literal ordinary parent premise used by forward restoration, uniformly
over every full marked subset and every positive shortening. The moving
puncture is chosen only after the constant. Canonical coefficient bounds and
support are discharged from the actual annular weight. -/
theorem canonical_parent_shortened
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hW : ContDiff ℝ ∞ W) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧
    ∀(B lam cap a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ),
      0≤lam → 0<a → 0≤b → 1<Z → σlo≤33/50 → (33/50:ℝ)≤σhi →
    ∀(η η₀ : Character)(Q : Ideal O)(degree : ℕ)(SP : Finset (ℕ×ℕ))(CP : ℝ),0≤CP →
      InitialAffineAt (α:=α) rayModulus Hray hH (SourceFace.mk B lam 0 B 0 cap) W
        2 a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree SP CP →
    ∀(θ : α→RayQuotient.Characters rayModulus Hray)(w freq : α→ℝ)(t height : ℝ),
      (∀i,0≤w i) → (∀i,w i≤mesh) → 0≤height → (∀i,|freq i|≤height) →
    ∀(M : ℝ),Mmin≤M → M≤Mmax → (∑i,w i)≤cap*M →
    ∀(p : Profiles a b)(X₁ X₂ : ℝ),0<X₁ → 0<X₂ →
      length Z X₁+length Z X₂+lam*(∑i,w i)≤B*M →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀R : Ideal O,R≠0 → ∀F : Finset α,∀Y₁ Y₂ : ℝ,
      0<Y₁ → 0<Y₂ → Y₁≤X₁ → Y₂≤X₂ →
      energy η (fixedBadMask*idealGenerator R) 1 t (p.profile 0) (p.profile 1)
        (fun i:F=>primePool rayModulus Hray 2 (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (33/50) (freq i) I)
        (fun i:F=>Z^(w i)) Y₁ Y₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*(R.radical.absNorm:ℝ)^δ*
        (CP*QuadraticInitialBound.diagonalControl Φ*(p.control SP)^2*
          (1+|t|+height)^degree*Z^(M+ε)) := by
  obtain ⟨D,hD,hcoeff⟩:=actual_marked_coefficient_bound W hWs hW
  obtain ⟨C,hC,hbound⟩:=canonical_masked_energy_all_slots (α:=α)
    rayModulus Hray hH (fun _=>D) (fun _=>hD) 2 δ hδ
  refine ⟨C,hC,?_⟩
  intro B lam cap a b bΦ mesh σlo σhi Mmin Mmax ε Z hlam ha hb hZ hσlo hσhi
    η η₀ Q degree SP CP hCP hsource θ w freq t height hw hmesh hh hv
    M hMlo hMhi hcap p X₁ X₂ hX₁ hX₂ hbudget Φ hΦs hΦ R hR F Y₁ Y₂ hY₁ hY₂ hYX₁ hYX₂
  have hZ0 : 0<Z:=zero_lt_one.trans hZ
  apply hbound F B lam cap hlam W a b bΦ mesh σlo σhi Mmin Mmax ε Z ha hb hZ
    η η₀ Q degree SP CP hCP hsource θ w (fun _=>33/50) freq t height
    (fun i _=>hw i) (fun i _=>hmesh i) (fun i _=>hσlo) (fun i _=>hσhi) hh (fun i _=>hv i)
  · intro i hi I hI
    exact hcoeff _ _ _ (Real.rpow_pos_of_pos hZ0 _) I (Finset.mem_filter.mp hI).2.1
  · intro i hi I hI hn
    exact actual_marked_support W hWs _ _ _ (Real.rpow_pos_of_pos hZ0 _) I hn
  · exact hMlo
  · exact hMhi
  · exact hcap
  · exact hbudget
  · exact Finset.sum_le_univ_sum_of_nonneg (fun i=>hw i)
  · exact hY₁
  · exact hY₂
  · exact clipped_length_mono Z Y₁ X₁ hZ hYX₁
  · exact clipped_length_mono Z Y₂ X₂ hZ hYX₂
  · exact hΦs
  · exact hΦ
  · exact hR

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.canonical_parent_shortened
