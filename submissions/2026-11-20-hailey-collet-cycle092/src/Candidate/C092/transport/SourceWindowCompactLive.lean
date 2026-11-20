/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Analytic join of the existing finite upper reference bank to moving actual
ordinary caps and whole-slot quotas. RawTicket owns the bank and metadata;
this file only specializes their native sources componentwise. -/
import Candidate.C092.transport.SourceWindowCompactShortening
import Candidate.C092.transport.RawTicketMiddleSourceMetadata
set_option autoImplicit false
namespace QRH.Cycle092.SourceWindowCompact
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyBands
open CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.StrongPair QRH.Cycle092.RawTicket QRH.Cycle092.Mixed
local notation "O" => ActualEisensteinCubic.O

/-- The source mesh precedes the fixed dictionary. Its common control set,
degree, constant and threshold precede every live U, radius V, reference pair
(n,z), and selected whole-slot quota. Both actual ordinary scales may be
componentwise shorter than n,z; PairAt retains their independent pitches.

The finite bank is supplied by RawTicket's already proved directed width
net. No continuity of pointwise existential source metadata is assumed. -/
theorem uniform_live_reference_source (hP1 : EarlierP1)
    {decrement epsilon : ℝ} (hd : 0<decrement ∧ decrement≤1/1000)
    (hepsilon : 0<epsilon) :
    ∃ mesh : ℝ,0 < mesh ∧
    ∀ (Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀ (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H),
    ∀ (W : ℝ→ℂ),ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
    ∀ (bPhi : ℝ),2≤bPhi → Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bPhi →
    ∀ {Label : Type*} [Fintype Label]
      (eta1 eta2 base1 base2 : Label→Character) (Q1 Q2 : Label→Ideal O),
      (∀j,Q1 j≤M) → (∀j,internalQ (Q1 j) (base1 j)≠0) →
      (∀j,internalQ (Q1 j) (base1 j)≠⊤) →
      (∀j,internalQ (Q1 j) (base1 j)≤Ideal.span {(72:O)}) →
      (∀j,Q2 j≤M) → (∀j,internalQ (Q2 j) (base2 j)≠0) →
      (∀j,internalQ (Q2 j) (base2 j)≠⊤) →
      (∀j,internalQ (Q2 j) (base2 j)≤Ideal.span {(72:O)}) →
    ∀ (Vmin : ℝ),0<Vmin →
    ∃ degree : ℕ,∃ controls : Finset (ℕ×ℕ),∃ C : ℝ,0<C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,Vmin≤V →
    ∀ (n z : ℝ),nLo≤n → n≤nHi → widthLo≤z → z≤widthHi →
    ∀ (live : ℝ),live ≤ max 0 (QRH.Cycle090.sourceWidth n z-decrement) →
    ∀ j : Label,
      PairAt (Slot:=Slot) M H hH n z live W bPhi mesh epsilon (U^V)
        (eta1 j) (eta2 j) (base1 j) (base2 j) (Q1 j) (Q2 j) degree controls C := by
  obtain ⟨bank,quota,mesh,hm,hsource,hnet⟩ := actual_reference_bank_mesh hP1 hd hepsilon
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ M _ H hH W hW hWs bPhi hbPhi hPhi Label _ eta1 eta2 base1 base2 Q1 Q2
    hQ1ray hQ10 hQ1top hQ172 hQ2ray hQ20 hQ2top hQ272 Vmin hVmin
  obtain ⟨degree,controls,C,hC,hbank⟩ := cap_bank_metadata_all_labels bank Prod.fst Prod.snd
    quota (fun B hB => (hsource B hB).2.2.2) hVmin Slot M H hH W hW hWs bPhi hbPhi hPhi
    eta1 eta2 base1 base2 Q1 Q2 hQ1ray hQ10 hQ1top hQ172 hQ2ray hQ20 hQ2top hQ272
  refine ⟨degree,controls,C,hC,?_⟩
  filter_upwards [hbank] with U hbank
  intro V hV n z hn0 hn1 hz0 hz1 live hl j
  obtain ⟨B,hB,hn,hz,hquota⟩ := hnet n z hn0 hn1 hz0 hz1
  have hlive : live≤quota B := hl.trans (max_le (hsource B hB).1 hquota)
  exact pairAt_componentwise_shorter M H hH hn hz hlive (hbank V hV B hB j)

end
end QRH.Cycle092.SourceWindowCompact
#print axioms QRH.Cycle092.SourceWindowCompact.uniform_live_reference_source
