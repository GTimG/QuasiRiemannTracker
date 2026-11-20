/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Improved inverse count for the actual arbitrary-ray regular-source union.
No BaselineData, substitute detector family or assumed moment occurs. -/
import Candidate.C092.transport.SourceInverseP6Count

namespace QRH.Cycle092.SourceInverseP6
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion HeckeDetectorRowwisePolynomial
open HeckeDetectorInverseFiberCount HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily
open Qrh.MarkedAnchor.Interface QRH.Cycle092.MediumReplace.Source
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_SourceInverseP6ActualCount_bba39427e03e8549_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def annularMark (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M  ≤  H) (η η₀ : Character) (W : ℝ→ℂ)
    (U : ℝ) (θ : RayQuotient.Characters M H) (w v : ℝ) (t : FreeRow→ℝ) (u : FreeRow) : ℂ :=
  normalizedSlot η fixedBadMask 1 u.val (primePool M H 2 (U^w))
    (fun I => idealCoeff (relativeCharacter M H hH η₀ θ) I*
      HeckePrimeAnnular.annularWeight W (U^w) (33/50) v I) (t u) (U^w)

theorem actual_source_inverse_count (ρ : Contract.AnchorRect)
    (hsource : Contract.UniformInverseRectSource Contract.canonicalFamily ρ)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ mesh : ℝ,0 < mesh ∧ ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M  ≤  H)
      (W : ℝ→ℂ), Function.support W ⊆ Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∀ (η η₀ : Character) (K : ℕ) (wrmin : ℝ),0 < wrmin →
    ∃ J : ℕ,∃ C : ℝ,0 < C ∧ ∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ (Z B bΦ : ℝ) (s : NaturalState Z B bΦ),s.character=η → s.puncture=1 →
    ∀ F : ∀ u : FreeRow,NaturalRow s.character u.val,
    ∀ rows : Finset FreeRow,(∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
    ∀ (a ε cutoff T allowance : ℝ) (i : ℕ),1/2 ≤ a →
    ∀ ws : ∀ u : rows,SupportedWitness (family M H hH s η₀ (F u.val)) U a ε cutoff T allowance i,
    ∀ (label : Option (RayQuotient.Characters M H × RayQuotient.Characters M H)) (r : ℝ),
      (∀ u,(ws u).label=label) → (∀ u,(ws u).r=r) →
    ∀ (θ : RayQuotient.Characters M H) (w v : ℝ) (t : FreeRow→ℝ) (height e buffer : ℝ),
      wrmin ≤ w → w ≤ mesh → 0 ≤ height → (∀ u∈rows,|t u| ≤ height) → |v| ≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T ≤ height → ρ.Admissible r ((K:ℝ)*w) 1 →
      (∀ u∈rows,U^(e*w-buffer) ≤ ‖annularMark M H hH η η₀ W U θ w v t u‖^2) →
    (rows.card : ℝ) ≤ (12*(1+height)*(C*(1+height)^J))*
      U^(1-(2*a-1)*r-e*((K:ℝ)*w)+2*ε+(K:ℝ)*buffer+εm) := by
  obtain ⟨mesh,hm,hs⟩ := hsource εm hεm
  refine ⟨mesh,hm,?_⟩
  intro M _ H hH W hWs hW η η₀ K wrmin hwrmin
  obtain ⟨J,C,hC,hev⟩ := actual_union_inverse_of_rect hs M H hH W hWs hW η η₀ (Fin K) wrmin hwrmin
  refine ⟨J,C,hC,hev.mono ?_⟩
  intro U hU
  refine ⟨hU.1,?_⟩
  intro Z B bΦ s hη hpuncture F rows hrows a ε cutoff T allowance i ha ws label r hlabel hr
    θ w v t height e buffer hw hmesh hh ht hv hfreq hadm hlower
  apply same_zero_inverse_count rows (fun u => family M H hH s η₀ (F u)) U a ε cutoff T allowance i
    ws label r hlabel hr (annularMark M H hH η η₀ W U θ w v t) K w e buffer εm
    (C*(1+height)^J) height hU.1 ha (by positivity) hh hfreq hlower
  intro n hn σ' hσ' freq hfreq'
  have hadm' : ρ.Admissible r (∑ _j : Fin K,w) 1 := by simpa using hadm
  have hmom := hU.2 Z B bΦ s hη hpuncture F label rows hrows Finset.univ
    (fun _ : Fin K => θ) (fun _ : Fin K => w) (fun _ : Fin K => (33/50:ℝ)) (fun _ : Fin K => v)
    t height (fun _ _ => hw) (fun _ _ => hmesh) (fun _ _ => rfl) hh ht (fun _ _ => hv)
    r hadm' cutoff n hn σ' hσ' freq hfreq'
  simpa only [originalSlot,annularMark,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hmom

#print axioms actual_source_inverse_count
end
end QRH.Cycle092.SourceInverseP6
