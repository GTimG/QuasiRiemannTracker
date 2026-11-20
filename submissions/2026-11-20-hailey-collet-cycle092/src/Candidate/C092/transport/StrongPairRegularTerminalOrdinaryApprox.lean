/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual regular-core P4 and authentic rowwise witness source on one finite family. -/
import Candidate.C092.transport.WitnessP4HeteroEarly
import Candidate.C092.transport.StrongPairRegularTerminalWindowFinishApprox
import Candidate.C092.transport.StrongPairOrdinaryNearIndependent
import Candidate.C092.transport.StrongPairOrdinaryNearErrors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.StrongPair
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
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.WitnessRowSup.Actual
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
local notation "O" => HeckeFamily.O
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance c092LocalInst_Candidate_C092_transport_StrongPairRegularTerminalOrdinaryApprox_ffb2a6ec0df0157b_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The ordinary escape on the actual regular core: P4 is invoked here,
not postulated. The source is the authentic PairAt furnished uniformly by
ordinary_witness_bank; its true witness m and same original marks are retained. -/
theorem regular_core_ordinary_window_approx_all_radii (controls : Finset (ℕ×ℕ)) :
    ∃ J : ℕ,∃ Crow : ℝ,0 < Crow ∧
    ∀ (bstate Mcap Bmask margin R dmin dmax τ ε e κ heightCost : ℝ)
    (hbstate : 0 ≤ bstate) (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax) (hτ : 0 < τ)
    (hheight : 4*τ < dmin*heightCost) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1)
    (hcost : 0 ≤ heightCost) (hbudget : 12*e*(R+2)+8*κ+2*heightCost ≤ ε)
    (profileBound : ℕ→ℝ) (hprofile : ∀ k,0 ≤ profileBound k) ,
    ∃ order : ℕ,∃ C4 : ℝ,0 < C4 ∧
    ∀ (η₀ : Character) (I : ℕ),∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState U Bmask bstate,s.width ≤ Mcap →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ η₀.modulus)
      (Qfix : Ideal O),Qfix ≤ M →
    ∀ (ηLong baseLong : Character) (QLong : Ideal O),
      s.mask=fixedBadMask*idealGenerator 1 →
      (∀ z,s.radial.keep z ↔ initialKeep s.character (internalQ Qfix η₀) z) →
    ∀ rows : Finset FreeRow,∀ hrows : ∀ u∈rows,s.radial.keep u.val,
      (∀ u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
    let imageRows := rows.image Subtype.val
    let hk : ∀ z∈imageRows,s.radial.keep z := fun z hz => by
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
      exact hrows u hu
    let F := fun z : imageRows => naturalRow s.character z.val (s.row_ne_zero z.val (hk z.val z.property))
    ∀ (a r m : ℝ) (c : Cutoff) (i : ℕ),51/100 ≤ a → a ≤ 1 → i ≤ I → 0 ≤ r → r ≤ R →
    ∀ ws : ∀ z : imageRows,SupportedWitness (family M H hH s η₀ (F z)) (U^d) a ε (totalCutoff c)
      (U^τ) ((U^d)^(τ/(2*dmax))) i,
      (∀ z,(ws z).m=m) →
      (∀ z,zeroMaximum (family M H hH s η₀ (F z))
        (family_nonprincipal M H hH s η₀ hQM hQη (hk z.val z.property) (F z))
        (3*(i+1 : ℕ)*U^τ) < a+2*e) →
    ∀ (WS : rows→ℝ→ℂ) (AS BS σS freqS : rows→ℝ),
      (∀ u,0 < AS u) → (∀ u,Function.support (WS u) ⊆ Icc (AS u) (BS u)) →
      (∀ u,ContDiff ℝ ∞ (WS u)) →
      (∀ u,|freqS u|+U^τ/2 ≤ (3*i+2 : ℕ)*U^τ) →
      (∀ u,∀ x ∈ Icc (1-a-6*e-σS u) (2-σS u),∀ t : ℝ,
        (1+|t|)^2*‖mellin (WS u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ u,∀ x ∈ Icc (1-a-6*e-σS u) (2-σS u),∀ t : ℝ,
        (1+|t|)^(order+2)*‖mellin (WS u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order+2)) →
    ∀ (N Y l bΦ mesh εsource Csource : ℝ) (W : ℝ→ℂ)
      (j : Option (RayQuotient.Characters M H × RayQuotient.Characters M H)) (degree : ℕ),
      PairAt (Slot:=Slot) M H hH N Y l W bΦ mesh εsource (U^d)
        ηLong (witnessBase M H hH s.character η₀ j)
        baseLong (witnessBase M H hH η₀ η₀ j) QLong Qfix degree controls Csource →
      (∀ z,(ws z).label=j) →
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
          (originalCoefficients M H hH η₀ θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖ =
        ‖normalizedSlot ηLong (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M H 2 (U^d) w k)
          (originalCoefficients M H hH baseLong θLong W (U^d) w σLong vLong k) tLong ((U^d)^(w k))‖) →
      (∀ u∈rows,rowNorm u ≤ U^d) →
      0 ≤ Csource → length (U^d) ((U^d)^m) ≤ Y →
    ∀ WL : 𝓢(ℝ,ℂ),Function.support (WL:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4) →
    ∀ (weight : rows→ℝ) (Aweight : ℝ),0 ≤ Aweight →
      (∀ u,0 ≤ weight u) → (∀ u,weight u ≤ Aweight) →
    ∀ (n y eResp eLower νLower step price V capB radius decrement rounding collar Cslot buffer : ℝ) (b : ℚ),
      l=nearOrdinaryQuota n capB radius-decrement →
      sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      0 ≤ eResp → 0 ≤ eLower → eLower ≤ (responseUpper:ℝ) → eLower ≤ νLower → νLower ≤ 3/4 →
      νLower ≤ 2*a-1+price → 2*a-1 ≤ νLower+step → eResp ≤ eLower+step → 0 ≤ step → 0 ≤ price →
      CutoffGuard b c → y/(QRH.SourceCertificate.H:ℝ) ≤ (c.ordinary:ℝ) →
      sourceY0 ≤ (c.ordinary:ℝ) → PaidWithBand y eLower νLower c →
      (∀ z,(ws z).r < (c.inverse:ℝ)) →
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
          (originalCoefficients M H hH η₀ θ W (U^d) w σslot v k) tMark ((U^d)^(w k))‖^2 ≤
            (Cslot*U^buffer)*U^(eResp*(d*w k))) →
      |tMark|+|tLong|+slotHeight+heightLong ≤ U^τ →
      collar+(15/4)*d*ε+
        eLower*(d*((5/4:ℝ)*(min d (QRH.SourceCertificate.H:ℝ)-radius)+(3/4:ℝ)*(capB-collaredOrdinaryCap c m))+d*decrement+rounding)+
          (d*εsource+buffer*(Fintype.card Slot:ℝ)+τ*((degree+2*J+1:ℕ):ℝ))+3*step+price*d*m ≤ (3/4)*(rho:ℝ) →
      (∑ u : rows,weight u*‖original ηLong s.mask 1 u.val.val WL tLong XL*
        original s.character s.mask 1 u.val.val (twistProfile (WS u) (σS u) (freqS u)) 0 ((U^d)^r)*
          (∏ k,normalizedSlot s.character s.mask 1 u.val.val
            (originalPools M H 2 (U^d) w k)
            (originalCoefficients M H hH η₀ θ W (U^d) w σslot v k) tMark ((U^d)^(w k)))‖^2) ≤
        (Cslot^(Finset.univ\Tslots).card*
          (C4*12*Aweight*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
            (sourceControl controls WL)^2*Crow^2)*(4:ℝ)^degree*
              (1+2*Real.pi+(3*I:ℕ))^(2*J+1))*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V)) := by
  obtain ⟨J,Crow,hCrow,hjoin⟩ := QRH.Cycle092.WitnessRowSup.Actual.Hetero.regular_core_actual_witness_early (Slot:=Slot) M H hH controls
  refine ⟨J,Crow,hCrow,?_⟩
  intro bstate Mcap Bmask margin R dmin dmax τ ε e κ heightCost hbstate hmargin hR hdmin hdmax hτ hheight
    hε he he' hκ hκ' hcost hbudget profileBound hprofile
  obtain ⟨order,C4,hC4,hjoin⟩ := hjoin bstate Mcap Bmask margin R dmin dmax τ ε e κ heightCost
    hbstate hmargin hR hdmin hdmax hτ hheight hε he he' hκ hκ' hcost hbudget profileBound hprofile
  refine ⟨order,C4,hC4,?_⟩
  intro η₀ I
  filter_upwards [hjoin η₀ I] with U hU
  refine ⟨hU.1,?_⟩
  intro d hd hd' hds s hs hQM hQη Qfix hQfix ηLong baseLong QLong hmask hkeep rows hrows hΦ
  dsimp only
  intro a r m c i ha ha' hi hr hr' ws hm hnext WS AS BS σS freqS hAS hWS hsm hfreq hm₂ hmn
    N Y l bΦ mesh εsource Csource W j degree hpair hlabel Tslots θ w σslot v θLong σLong vLong tMark tLong slotHeight heightLong XL
    hw hwm hσlo hσhi hh hv hσLonglo hσLonghi hhLong hvLong hsum hXL hXN hkLong hmLong hy hCsrc hXY WL hWL weight Aweight hA hweight hweightA
    n y eResp eLower νLower step price V capB radius decrement rounding collar Cslot buffer b hquota hy0 hycap hyn hn
    he0 hel0 hel1 hνlo hνhi hνactual0 hνactual1 heu hstep hprice hg hc hc0 hp
    hescape hV hdV hdc hradius hradiusd hcap hdec hround hL hq hround1 hCslot hbuffer hshort hwidth hdelete hlow hsmall hfees
  have hp4 := hU.2 d hd hd' hds s hs hQM hQη Qfix hQfix ηLong baseLong QLong hmask hkeep rows hrows hΦ
    a (totalCutoff c) r m i ha ha' hi hr hr' ws hm hnext WS AS BS σS freqS
    hAS hWS hsm hfreq hm₂ hmn N Y l bΦ mesh εsource Csource W j degree hpair hlabel
    Tslots θ w σslot v θLong σLong vLong tMark tLong slotHeight heightLong XL hw hwm hσlo hσhi hh hv hσLonglo hσLonghi hhLong hvLong hsum hXL hXN hkLong hmLong hy hCsrc hXY
    WL hWL weight Aweight hA hweight hweightA
  let An : rows→ℂ := fun u=>original ηLong s.mask 1 u.val.val WL tLong XL
  let Ay : rows→ℂ := fun u=>original s.character s.mask 1 u.val.val
    (twistProfile (WS u) (σS u) (freqS u)) 0 ((U^d)^r)
  let mark : Slot → rows → ℂ := fun k u=>normalizedSlot s.character s.mask 1 u.val.val
    (originalPools M H 2 (U^d) w k)
    (originalCoefficients M H hH η₀ θ W (U^d) w σslot v k) tMark ((U^d)^(w k))
  let K : ℝ := C4*12*Aweight*Csource*QuadraticInitialBound.diagonalControl radialMajorant*
    (sourceControl controls WL)^2*Crow^2
  have hUp : 0 < U := zero_lt_one.trans hU.1
  have hK : 0 ≤ K := by
    have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    dsimp [K]
    positivity
  have hag : |tMark|+|tLong|+slotHeight+heightLong = |tMark|+|tLong|+(slotHeight+heightLong) := by ring
  rw [hag] at hp4
  have hp4' : (∑ u : rows,weight u*‖An u*Ay u*(∏ k∈Tslots,mark k u)‖^2) ≤
      K*(1+|tLong|+(|tMark|+|tLong|+(slotHeight+heightLong)))^degree*
        (1+(2*Real.pi*((U^d)^(τ/(2*dmax)))+(3*i:ℕ)*U^τ))^(2*J+1)*
          U^((2*a-1)*(d*r-d*m)+3*d*ε+d*(1+εsource)) := by
    convert hp4 using 1
    rw [Real.rpow_add hUp]
    dsimp [K]
    ring
  have hf := terminal_window_p4_finish_approx c (fun u : rows=>ws (sourceRowEquiv rows u))
    (fun u=>hm _) (fun u=>hescape _) hy0 hycap hyn hn he0 hel0 hel1 hνlo hνhi hνactual0 hνactual1 heu hstep hprice (by linarith only [ha]) hg hc hc0 hp hε.le
    hV hdV hdc hradius hradiusd hcap hdec hround hL hq hround1
    (by simpa only [Finset.sdiff_empty,Finset.card_univ] using hfees)
    Tslots weight An Ay mark (fun k=>d*w k) hU.1 hCslot hK hbuffer hweight hwidth
    (by simpa only [hquota] using hdelete) hlow hshort hd'
    (hdmin.trans_le hdmax) hτ.le hi (add_nonneg hh hhLong) (by simpa only [add_assoc] using hsmall) hp4'
  exact hf

#print axioms regular_core_ordinary_window_approx_all_radii
end
end QRH.Cycle092.StrongPair
