/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual regular-core P4 and authentic rowwise witness source on one finite family. -/
import Candidate.C092.transport.RegularColoredTerminalLeafMetadata
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafUnit_e8f9995a99c3252e_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- A genuine ordinary source function is applied to the fixed unit-profile
bank. All Mellin tests and the long source controls are discharged here. -/
theorem terminal_ordinary_unit_call
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
    ∀ (I : ℕ),∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ (p : Profiles (1/4) (9/4)),
      TerminalProfileUniform.UnitGates (fun _=>0) (-1) 2 {2,order+2} controls p →
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
        (p.profile 0) (p.profile 1) tLong tShort XL ((U^d)^r)
        (fun k u=>normalizedSlot s.character s.mask 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))) ≤
        (Cslot^(Finset.univ\Tslots).card*
          (C4*12*Csource*QuadraticInitialBound.diagonalControl radialMajorant*Crow^2)*(4:ℝ)^degree*
              (1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
  intro bstate Mcap Bmask margin R dmax τ ε e κ heightCost hbstate hmargin hR hdmax hτ hheight hε he he' hκ hκ' hcost hbudget
  obtain ⟨order,C4,hC4,hsource⟩ := hphysical bstate Mcap Bmask margin R dmax τ ε e κ heightCost
    hbstate hmargin hR hdmax hτ hheight hε he he' hκ hκ' hcost hbudget (fun _=>1) (fun _=>zero_le_one)
  refine ⟨order,C4,hC4,?_⟩
  intro I
  filter_upwards [hsource I] with U hU
  refine ⟨hU.1,?_⟩
  intro p hgates d hd hd' hds s hs hschar hQM hQη hmask hkeep rows hrows hΦrows
  dsimp only
  intro a r m c i ha ha' hi hr hr' wc hm hnext tShort hfreq B hB j hlabel Tslots θ w σslot v θLong σLong vLong tMark tLong slotHeight heightLong XL
    hw hwm hσlo hσhi hh hv hσLonglo hσLonghi hhLong hvLong hsum hXL hXN hkLong hmLong hy hXY
    eResp eLower νLower step price V rounding collar Cslot buffer b hy0' hycap hyn' hn'
    he0 hel0 hel1 hνlo hνhi hνactual0 hνactual1 heu hstep hprice hg hc hc0 hp
    hescape hV hdV hdc hradius hradiusd hcap hdec hround hL hq hround1 hCslot hbuffer hshort hwidth hdelete hlow hsmall hfees
  have hmellin (k : ℕ) (hk : k∈({2,order+2}:Finset ℕ))
      (x : ℝ) (hx : x∈Icc (1-a-6*e-(0:ℝ)) (2-(0:ℝ))) (t : ℝ) :
      (1+|t|)^k*‖mellin (p.profile 1) ((x:ℂ)+t*Complex.I)‖≤1 := by
    exact (hgates.2 1 k hk x (TerminalProfileUniform.actual_zero_band_strip ha ha' he he' (by simpa using hx)) t).1
  have hsource := hU.2 d hd hd' hds s hs hschar hQM hQη hmask hkeep rows hrows hΦrows
    a r m c i ha ha' hi hr hr' wc hm hnext
    (fun _=>p.profile 1) (fun _=>1/4) (fun _=>9/4) (fun _=>0) (fun _=>tShort)
    (fun _=>by norm_num) (fun _=>p.support 1) (fun _=>(p.profile 1).smooth ⊤) (fun _=>hfreq)
    (fun _ x hx t=>hmellin 2 (by simp) x hx t)
    (fun _ x hx t=>hmellin (order+2) (by simp) x hx t)
    B hB j hlabel Tslots θ w σslot v θLong σLong vLong tMark tLong slotHeight heightLong XL
    hw hwm hσlo hσhi hh hv hσLonglo hσLonghi hhLong hvLong hsum hXL hXN hkLong hmLong hy hXY
    (p.profile 0) (p.support 0) (fun _=>1) 1 zero_le_one (fun _=>zero_le_one) (fun _=>le_rfl)
    eResp eLower νLower step price V rounding collar Cslot buffer b
    hy0' hycap hyn' hn' he0 hel0 hel1 hνlo hνhi hνactual0 hνactual1 heu hstep hprice hg hc hc0 hp
    hescape hV hdV hdc hradius hradiusd hcap hdec hround hL hq hround1 hCslot hbuffer hshort hwidth hdelete hlow hsmall hfees
  have henergy : StrongPair.finiteEnergyOn Finset.univ rows ηLong s.character
      (p.profile 0) (p.profile 1) tLong tShort XL ((U^d)^r)
      (fun k u=>normalizedSlot s.character s.mask 1 u.val (originalPools M H 2 (U^d) w k)
        (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k))) =
      ∑u : rows,(1:ℝ)*‖original ηLong s.mask 1 u.val.val (p.profile 0) tLong XL*
        original s.character s.mask 1 u.val.val (twistProfile (p.profile 1) 0 tShort) 0 ((U^d)^r)*
        (∏k,normalizedSlot s.character s.mask 1 u.val.val (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseShort θ W (U^d) w σslot v k) tMark ((U^d)^(w k)))‖^2 := by
    unfold StrongPair.finiteEnergyOn
    rw [←Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro u hu
    have hn:=terminal_original_short_twist s u.val (hrows u.val u.property) (p.profile 1)
      (1/4) (9/4) (by norm_num) (p.support 1) ((p.profile 1).smooth ⊤) tShort ((U^d)^r)
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hU.1) _) _)
    rw [hmask] at hn
    simp only [norm_mul,norm_prod,mul_pow,Finset.prod_pow,one_mul,hmask]
    rw [hn]
  rw [henergy]
  apply hsource.trans
  have hctl := hgates.1 0
  have hctl0 := sourceControl_nonneg controls (p.profile 0)
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  have hUp := zero_lt_one.trans hU.1
  have hctl2 : (sourceControl controls (p.profile 0))^2≤(1:ℝ) := by
    simpa only [one_pow] using pow_le_pow_left₀ hctl0 hctl 2
  calc
    _ ≤ (Cslot^(Finset.univ\Tslots).card*
          (C4*12*1*Csource*QuadraticInitialBound.diagonalControl radialMajorant*(1:ℝ)*Crow^2)*(4:ℝ)^degree*
              (1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
      gcongr
    _ = _ := by ring

#print axioms terminal_ordinary_unit_call
end
end QRH.Cycle092.RegularColoredForward
