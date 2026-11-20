/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual regular-core P4 and authentic rowwise witness source on one finite family. -/
import Candidate.C092.transport.RegularColoredTerminalLeafUnit
import Candidate.C092.transport.RegularColoredTerminalLeafNative
import Candidate.C092.transport.RegularColoredTerminalLeafReindex
import Candidate.C092.transport.StrongPairRegularTerminalOrdinaryApprox
import Candidate.C092.transport.StrongPairRegularTerminalWindowFinishApprox
import Candidate.C092.transport.StrongPairOrdinaryNearIndependent
import Candidate.C092.transport.StrongPairOrdinaryNearErrors

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorSupportedWitness ConcretePrimeRowBridge ConcreteTraceCRT HeckeDetectorZeros
open HeckeRowClosure ProbeHighRowFamily CanonicalRowCompletion
open CenteredMomentEnergyBands QRH.Cycle092.WholeSlot
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.LowActual
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.WitnessRowSup.Actual
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafNormalized_2f3acbb440b208e2_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Unit-bound native constants are selected before the normalization
bank; its actual original profiles and Fourier parameters follow one
uniform eventual threshold. -/
theorem terminal_ordinary_normalized_call
    (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ) (bΦ : ℝ) (ηLong baseLong ηShort baseShort : Character) (QLong Qfix : Ideal O)
    (n y dmin εsource mesh : ℝ) (bank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ)→ℝ)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (Csource : ℝ) (J : ℕ) (Crow : ℝ)
    (hCsource : 0≤Csource) (hCrow : 0≤Crow)
    (hphysical : TerminalOrdinaryPhysical Slot M H hH W bΦ ηLong baseLong ηShort baseShort QLong Qfix
      n y dmin εsource mesh bank dec degree controls Csource J Crow) :
∀ (bstate Mcap Bmask margin R dmax τ ε e κ heightCost : ℝ)
    (hbstate : 0 ≤ bstate) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hheight : 4*τ < dmin*heightCost) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hcost : 0 ≤ heightCost) (hbudget : 12*e*(R+2)+8*κ+2*heightCost ≤ ε),
    ∃ order : ℕ,∃ C4 : ℝ,0 < C4 ∧
    ∃ S : Finset (ℕ×ℕ),(0,0)∈S ∧ ∃ C : ℝ,1≤C ∧
    ∀ (I : ℕ),∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ (p : Profiles (1/4) (9/4)),
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState U Bmask bstate,s.width ≤ Mcap → s.character=ηShort →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ baseShort.modulus),
      s.mask=fixedBadMask*idealGenerator 1 →
      (∀ z : O,s.radial.keep z ↔ initialKeep s.character (internalQ Qfix baseShort) z) →
    ∀ rows : Finset FreeRow,∀ hrows : ∀ u∈rows,s.radial.keep u.val,
      (∀ u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
    let F := fun u : FreeRow => naturalRow s.character u.val u.property.1
    ∀ (a r m : ℝ) (c : Cutoff) (i : ℕ),51/100 ≤ a → a ≤ 1 → i ≤ I → 0 ≤ r → r ≤ R →
    ∀ ws : ∀ z : rows,SupportedWitness (family M H hH s baseShort (F z.val)) (U^d) a ε (totalCutoff c)
      (U^τ) ((U^d)^(τ/(2*dmax))) i,
      (∀ z : rows,(ws z).m=m) →
      (∀ z : rows,zeroMaximum (family M H hH s baseShort (F z.val))
        (family_nonprincipal M H hH s baseShort hQM hQη (z:=z.val.val) (hrows z.val z.property) (F z.val))
        (3*(i+1 : ℕ)*U^τ) < a+2*e) →
    ∀ (tShort : ℝ), |tShort|+U^τ/2≤(3*i+2:ℕ)*U^τ →
    ∀ B∈bank,∀ j : Option (RayQuotient.Characters M H × RayQuotient.Characters M H),
    let N := n/B.1;
    let Y := nearOrdinaryCap n B.2 B.1;
    let l := nearOrdinaryQuota n B.2 B.1-dec B;
    let radius := B.1;
    let capB := B.2;
    let decrement := dec B;
      (∀ z : rows,(ws z).label=j) →
    ∀ (Tslots : Finset Slot) (θ : Slot→RayQuotient.Characters M H)
      (w σslot v : Slot→ℝ) (θLong : Slot→RayQuotient.Characters M H) (σLong vLong : Slot→ℝ)
      (tMark tLong slotHeight heightLong XL : ℝ),
      (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) →
      (∀ k,(33/50:ℝ) ≤ σslot k) → (∀ k,σslot k ≤ (33/50:ℝ)) →
      0 ≤ slotHeight → (∀ k,|v k| ≤ slotHeight) →
      (∀ k,(33/50:ℝ) ≤ σLong k) → (∀ k,σLong k ≤ (33/50:ℝ)) →
      0 ≤ heightLong → (∀ k,|vLong k| ≤ heightLong) → (∑ k∈Tslots,w k) ≤ l →
      0 < XL → length (U^d) XL ≤ N →
      (∀ u∈rows,initialKeep ηLong (internalQ QLong baseLong) u.val) →
      (∀ u∈rows,∀ k∈Tslots,
        ‖normalizedSlot s.character (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖ =
        ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseLong θLong W (U^d) w σLong vLong k) tLong ((U^d)^(w k))‖) →
      (∀ u∈rows,rowNorm u ≤ U^d) →
      length (U^d) ((U^d)^m) ≤ Y →
    ∀ (eResp eLower νLower step price V rounding collar Cslot buffer : ℝ) (b : ℚ),
      sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      0 ≤ eResp → 0 ≤ eLower → eLower ≤ (responseUpper:ℝ) → eLower ≤ νLower → νLower ≤ 3/4 →
      νLower ≤ 2*a-1+price → 2*a-1 ≤ νLower+step → eResp ≤ eLower+step → 0 ≤ step → 0 ≤ price →
      CutoffGuard b c → y/(QRH.SourceCertificate.H:ℝ) ≤ (c.ordinary:ℝ) →
      sourceY0 ≤ (c.ordinary:ℝ) → PaidWithBand y eLower νLower c →
      (∀ z : rows,(ws z).r < (c.inverse:ℝ)) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+collar →
      (98/100:ℝ) ≤ radius → radius ≤ min d (QRH.SourceCertificate.H:ℝ) →
      collaredOrdinaryCap c m ≤ capB → 0 ≤ decrement → 0 ≤ rounding →
      sourceWidth n y-(u:ℝ) ≤ 1 →
      0 ≤ nearOrdinaryQuota n capB radius-decrement → rounding ≤ 1 →
      0 ≤ Cslot → 0 ≤ buffer → d*r ≤ y →
      (∑ k,d*w k) ≤ sourceWidth n y-(u:ℝ) →
      (∑ k∈Finset.univ\Tslots,d*w k) ≤ max 0 ((∑ k,d*w k)-d*l+rounding) →
      (∀ u : rows,∀ k∈Finset.univ\Tslots,
        ‖normalizedSlot s.character s.mask 1 u.val.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖^2 ≤
            (Cslot*U^buffer)*U^(eResp*(d*w k))) →
      |tMark|+|tLong|+slotHeight+heightLong ≤ U^τ →
      collar+(15/4)*d*ε+
        eLower*(d*((5/4:ℝ)*(min d (QRH.SourceCertificate.H:ℝ)-radius)+(3/4:ℝ)*(capB-collaredOrdinaryCap c m))+d*decrement+rounding)+
          (d*εsource+buffer*(Fintype.card Slot:ℝ)+τ*((degree+2*J+1:ℕ):ℝ))+3*step+price*d*m ≤ (3/4)*(rho:ℝ) →
      StrongPair.finiteEnergyOn Finset.univ rows ηLong s.character
        ((TerminalProfileUniform.unitPair S C p).profile 0) ((TerminalProfileUniform.unitPair S C p).profile 1) tLong tShort XL ((U^d)^r)
        (fun k u=>normalizedSlot s.character s.mask 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))) ≤
        (Cslot^(Finset.univ\Tslots).card*
          (C4*12*Csource*QuadraticInitialBound.diagonalControl radialMajorant*Crow^2)*(4:ℝ)^degree*
              (1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
  intro bstate Mcap Bmask margin R dmax τ ε e κ heightCost hbstate hmargin hR hdmax hτ hheight hε he he' hκ hκ' hcost hbudget
  obtain ⟨order,C4,hC4,hsource⟩ := terminal_ordinary_unit_call Slot M H hH W bΦ ηLong baseLong ηShort baseShort QLong Qfix
    n y dmin εsource mesh bank dec degree controls Csource J Crow hCsource hCrow hphysical
    bstate Mcap Bmask margin R dmax τ ε e κ heightCost hbstate hmargin hR hdmax hτ hheight hε he he' hκ hκ' hcost hbudget
  obtain ⟨S,hS,hex,C,hC,hnorm⟩ := TerminalProfileUniform.actual_pair_unit_bank (fun _=>0)
    contDiff_const (1/4) (9/4) (by norm_num) (-1) 2 {2,order+2} controls
  refine ⟨order,C4,hC4,S,hS,C,hC,?_⟩
  intro I
  filter_upwards [hsource I] with U hU
  exact ⟨hU.1,fun p=>hU.2 (TerminalProfileUniform.unitPair S C p) (hnorm p).1⟩

#print axioms terminal_ordinary_normalized_call
end
end QRH.Cycle092.RegularColoredForward
