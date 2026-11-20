/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataEarly
import Candidate.C092.transport.RegularColoredTerminalLeafOrdinarySelected
import Candidate.C092.transport.TerminalActualInverseApplyProfiles
import Candidate.C092.transport.TerminalProfileUniformPair
import Candidate.C092.transport.P2CommonSourceMetadataInverse
import Candidate.C092.transport.P2CommonSourceMetadataTableBank
import Candidate.C092.transport.P2CommonSourceMetadataTypes
import Candidate.C092.transport.RegularColoredTerminalLeafTable
import Candidate.C092.transport.RegularColoredTerminalLeafLowHigh
import Candidate.C092.transport.RegularColoredTerminalLeafSmallActual
import Candidate.C092.transport.RegularColoredTerminalLeafOrdinaryBank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.P2CommonSourceMetadata
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros HeckeDetectorRowwisePolynomial
open ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentHeckeSlots HeckePrimeAnnular
open QRH.Cycle092.WholeSlot
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.TinyCore QRH.Cycle092.MediumReplace.Source
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.StrongPair QRH.Cycle092.LowActual QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.SourceInverseP6 QRH.Cycle092.MediumInversePrice
open QRH.Cycle092.OrdinaryColumn Qrh.MarkedAnchor.Interface
local notation "O" =>  HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataReady_67abede14731acea_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

structure LateGeometry (dmin dmax : ℝ) (dBank : Finset ℝ) where
  Mcap : dBank → ℝ
  Bmask : ℝ
  margin : ℝ
  hmargin : 0 < margin
  R : ℝ
  hR : 0 ≤ R
  τ : ℝ
  hτ : 0 < τ
  ε : ℝ
  hε : 0 < ε
  ez : ℝ
  hez : 0 < ez
  hez_small : ez < 1/1000
  κ : ℝ
  hκ : 0 < κ
  hκ_small : κ ≤ 1
  heightCost : ℝ
  heightCost_nonneg : 0 ≤ heightCost
  height : 4*τ < dmin*heightCost
  budget : 12*ez*(R+2)+8*κ+2*heightCost ≤ ε
  hdmax : dmin ≤ dmax

def MarkedAt (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (ρ : Contract.AnchorRect) (εm nativeError N quota dmin dmax price im nm buffer : ℝ)
    (P : MarkedPacket Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      ρ εm nativeError N quota dmin dmax price im nm buffer) (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (Bshort : ℝ)
    (order : Fin (nativeK buffer dmax+1) → Fin (nativeK buffer dmax+1) → ℕ) (Cy : Fin (nativeK buffer dmax+1) → Fin (nativeK buffer dmax+1) → ℝ) (I : ℕ) (Cslot Z : ℝ) : Prop :=
    let b := buffer/2;
    let Kbig := nativeK buffer dmax;
    1 < Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → G.Mcap db+G.Bmask+G.margin ≤ d →
    ∀ s : NaturalState Z G.Bmask A.bΦ,s.width ≤ G.Mcap db → s.character=A.ηShort → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ A.baseShort.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+G.ez*(band u).val) ε (cutoffTable (window u))
        (Z^G.τ) ((Z^d)^(G.τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
        Fin (dyadicLength (Z^d))×Fin (dyadicLength (Z^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+G.ez*tag.2.1.val;
    let i := tag.1.val;
    let cutoff := cutoffTable tag.2.2.1;
    let T := Z^G.τ;
    let allowance := (Z^d)^(G.τ/(2*dmax));
    let label := tag.2.2.2.1;
    let left := tag.2.2.2.2.1;
    let right := tag.2.2.2.2.2;
    let r := Real.logb (Z^d) ((2:ℝ)^left.val);
    let rows := classRows parentRows (terminalWitnessKey level band window cutoffTable parentWS) tag;
      a ≤ 1 →
      (∀ u : parentRows,HeckeDetectorZeros.zeroMaximum
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M A.Hr A.hHr s A.baseShort hsM hsη (hkeep u.val u.property)
          (naturalRow s.character u.val.val u.val.property.1))
        (3*((level u).val+1 : ℕ)*Z^G.τ) < ((51/100:ℝ)+G.ez*(band u).val)+2*G.ez) →
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ) (Y : ℝ),
      0 ≤ yCell → yCell/d ≤ G.R → 0 < Y → Y ≤ Z^yCell →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,Function.support (twistProfile (Wi u) (σi u) (fi u)) ⊆ Iic (9/4:ℝ)) →
      (∀ u∈rows,∀ x,‖twistProfile (Wi u) (σi u) (fi u) x‖ ≤ Bshort) →
      (∀ u∈rows,|fi u|+Z^G.τ/2 ≤ (3*i+2 : ℕ)*Z^G.τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*G.ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ (fun _ : ℕ => (1:ℝ)) 2) →
      (∀ ki kl : Fin (Kbig+1),∀ u∈rows,∀ x∈Icc (1-a-6*G.ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order ki kl+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ (fun _ : ℕ => (1:ℝ)) (order ki kl+2)) →
    ∀ (θ θLong : Slot→RayQuotient.Characters M A.Hr) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L ζ X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ min im nm) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) → (∀ j,|vLong j| ≤ slotHeight) →
      (∀ u∈rows,∀ j,‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W Z θ w v tMark u j‖=
        ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M A.Hr 2 (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter M A.Hr A.hHr A.baseLong (θLong j)) I*
            HeckePrimeAnnular.annularWeight A.W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖) →
      0 ≤ eu →
      (∑ j,w j) ≤ L → 0 ≤ ζ → 367/500 ≤ r →
      0 ≤ QRH.Cycle092.Source.inverseQuota r-ζ →
      ρ.Admissible r (QRH.Cycle092.Source.inverseQuota r-ζ) 1 →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep A.ηLong (internalQ A.QLong A.baseLong) u.val) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      nu0 ≤ 2*a-1+price → 2*a-1 ≤ nu0+step → eu ≤ e0+step →
      (c.inverse:ℝ) ≤ r → r ≤ 1 → 0 ≤ ε → ε ≤ fee →
      0 ≤ L → L ≤ 1 → L ≤ sourceWidth n yCell-(u:ℝ) →
      2*NativeFourthEffective.credit n d-d*quota ≤ fee/2 →
      ζ ≤ fee/2 →
      d*G.ε+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
      |tMark|+|tLong|+slotHeight ≤ Z^G.τ →
    ∀ (jd : Slot) (p : Profiles (1/4) (9/4)) (jprofile : Fin 2),
    let selectedRows := descriptorRows M A.Hr A.hHr rows A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) b θ w v tMark jd;
      selectedRows.Nonempty →
      (∀ u∈selectedRows,e0 ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) θ w v tMark u) →
      (∀ u∈selectedRows,measured M A.Hr A.hHr A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) θ w v tMark u ≤ eu) →
    let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T);
    let hl := |tMark|+|tLong|+slotHeight;
    ∃ ki kl : Fin (Kbig+1),
    (∑ u∈selectedRows,‖original A.ηLong (fixedBadMask*idealGenerator 1) 1 u.val
      (p.profile jprofile) tLong X*
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 Y*
      (∏ j,descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W Z θ w v tMark u j)‖^2) ≤
      (Cslot^(Fintype.card Slot)*Cy ki kl*(12*P.Cc ki kl+1)*
        (P.Cl ki kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (P.controls ki kl) (p.profile jprofile))^4+1)*
        (2+2*Real.pi+(3*I:ℕ))^(P.Jc ki kl+1)*(3:ℝ)^(P.degree ki kl))*
      Z^(V+radialAllowance V+loss+heightLoss)

structure ReadyMarked (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (ρ : Contract.AnchorRect) (εm nativeError N quota dmin dmax price im nm buffer : ℝ)
    (P : MarkedPacket Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      ρ εm nativeError N quota dmin dmax price im nm buffer) (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (Bshort : ℝ) where
  order : Fin (nativeK buffer dmax+1) → Fin (nativeK buffer dmax+1) → ℕ
  Cy : Fin (nativeK buffer dmax+1) → Fin (nativeK buffer dmax+1) → ℝ
  positive : ∀ki kl,0 < Cy ki kl
  event : ∀(I : ℕ) (Cslot : ℝ),0 < Cslot → ∀ᶠ Z : ℝ in atTop,
    MarkedAt Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      ρ εm nativeError N quota dmin dmax price im nm buffer P dBank G db Bshort order Cy I Cslot Z

theorem ready_marked (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (ρ : Contract.AnchorRect) (εm nativeError N quota dmin dmax price im nm buffer : ℝ)
    (P : MarkedPacket Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      ρ εm nativeError N quota dmin dmax price im nm buffer) (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (Bshort : ℝ)
    (hBshort : 0 ≤ Bshort) (hτD : G.τ*(P.D:ℝ) ≤ heightLoss) :
    Nonempty (ReadyMarked Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      ρ εm nativeError N quota dmin dmax price im nm buffer P dBank G db Bshort) := by
  obtain ⟨order,Cy,hCy,hevent⟩ := P.late (G.Mcap db) G.Bmask G.margin G.R G.τ G.ε G.ez G.κ G.heightCost
    G.hmargin G.hR G.hτ hτD G.height G.hε G.hez G.hez_small G.hκ G.hκ_small G.heightCost_nonneg G.budget
    Bshort hBshort (fun _=>1) (fun _=>zero_le_one)
  exact ⟨⟨order,Cy,hCy,hevent⟩⟩

def UnmarkedAt (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nm buffer : ℝ)
    (P : UnmarkedPacket Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer) (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (Bshort : ℝ)
    (order : Fin (nativeK buffer dmax+1) → ℕ) (Cy : Fin (nativeK buffer dmax+1) → ℝ) (I : ℕ) (Cslot Z : ℝ) : Prop :=
    let b := buffer/2;
    let Kbig := nativeK buffer dmax;
    1 < Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → G.Mcap db+G.Bmask+G.margin ≤ d →
    ∀ s : NaturalState Z G.Bmask A.bΦ,s.width ≤ G.Mcap db → s.character=A.ηShort → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ A.baseShort.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+G.ez*(band u).val) ε (cutoffTable (window u))
        (Z^G.τ) ((Z^d)^(G.τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
        Fin (dyadicLength (Z^d))×Fin (dyadicLength (Z^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+G.ez*tag.2.1.val;
    let i := tag.1.val;
    let cutoff := cutoffTable tag.2.2.1;
    let T := Z^G.τ;
    let allowance := (Z^d)^(G.τ/(2*dmax));
    let label := tag.2.2.2.1;
    let left := tag.2.2.2.2.1;
    let right := tag.2.2.2.2.2;
    let r := Real.logb (Z^d) ((2:ℝ)^left.val);
    let rows := classRows parentRows (terminalWitnessKey level band window cutoffTable parentWS) tag;
      a ≤ 1 →
      (∀ u : parentRows,HeckeDetectorZeros.zeroMaximum
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M A.Hr A.hHr s A.baseShort hsM hsη (hkeep u.val u.property)
          (naturalRow s.character u.val.val u.val.property.1))
        (3*((level u).val+1 : ℕ)*Z^G.τ) < ((51/100:ℝ)+G.ez*(band u).val)+2*G.ez) →
      0 ≤ ε → ε ≤ 1/1000 → 1 ≤ cutoff → cutoff ≤ 3/2 →
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ) (Y : ℝ),
      0 ≤ yCell → yCell/d ≤ G.R → 0 < Y → Y ≤ Z^yCell →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,Function.support (twistProfile (Wi u) (σi u) (fi u)) ⊆ Iic (9/4:ℝ)) →
      (∀ u∈rows,∀ x,‖twistProfile (Wi u) (σi u) (fi u) x‖ ≤ Bshort) →
      (∀ u∈rows,|fi u|+Z^G.τ/2 ≤ (3*i+2 : ℕ)*Z^G.τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*G.ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ (fun _ : ℕ => (1:ℝ)) 2) →
      (∀ kl : Fin (Kbig+1),∀ u∈rows,∀ x∈Icc (1-a-6*G.ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order kl+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ (fun _ : ℕ => (1:ℝ)) (order kl+2)) →
    ∀ (θ θLong : Slot→RayQuotient.Characters M A.Hr) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ nm) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) → (∀ j,|vLong j| ≤ slotHeight) →
      (∀ u∈rows,∀ j,‖descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W Z θ w v tMark u j‖=
        ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M A.Hr 2 (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter M A.Hr A.hHr A.baseLong (θLong j)) I*
            HeckePrimeAnnular.annularWeight A.W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖) →
      0 ≤ eu →
      (∑ j,w j) ≤ L →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep A.ηLong (internalQ A.QLong A.baseLong) u.val) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      nu0 ≤ 2*a-1+price → 2*a-1 ≤ nu0+step → eu ≤ e0+step →
      (c.inverse:ℝ) ≤ r → cutoff=totalCutoff c → ε ≤ fee →
      0 ≤ L → L ≤ 1 → L ≤ sourceWidth n yCell-(u:ℝ) →
      2*NativeFourthEffective.credit n d-d*quota ≤ fee/2 →
      (r ≤ 1 → inverseQuota r ≤ fee) →
      d*G.ε+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
      |tMark|+|tLong|+slotHeight ≤ Z^G.τ →
    ∀ (jd : Slot) (p : Profiles (1/4) (9/4)) (jprofile : Fin 2),
    let selectedRows := descriptorRows M A.Hr A.hHr rows A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) b θ w v tMark jd;
      selectedRows.Nonempty →
      (∀ u∈selectedRows,e0 ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) θ w v tMark u) →
      (∀ u∈selectedRows,measured M A.Hr A.hHr A.ηShort A.baseShort A.W Z (Cslot*Z^buffer) θ w v tMark u ≤ eu) →
    let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T);
    let hl := |tMark|+|tLong|+slotHeight;
    ∃ kl : Fin (Kbig+1),
    (∑ u∈selectedRows,‖original A.ηLong (fixedBadMask*idealGenerator 1) 1 u.val
      (p.profile jprofile) tLong X*
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 Y*
      (∏ j,descriptor M A.Hr A.hHr A.ηShort A.baseShort A.W Z θ w v tMark u j)‖^2) ≤
      (Cslot^(Fintype.card Slot)*Cy kl*(192*P.Cc kl+1)*
        (P.Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (P.controls kl) (p.profile jprofile))^4+1)*
        (2+2*Real.pi+(3*I:ℕ))^(P.Jc kl+1)*(3:ℝ)^(P.degree kl))*
      Z^(V+radialAllowance V+loss+heightLoss)

structure ReadyUnmarked (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nm buffer : ℝ)
    (P : UnmarkedPacket Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer) (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (Bshort : ℝ) where
  order : Fin (nativeK buffer dmax+1) → ℕ
  Cy : Fin (nativeK buffer dmax+1) → ℝ
  positive : ∀kl,0 < Cy kl
  event : ∀(I : ℕ) (Cslot : ℝ),0 < Cslot → ∀ᶠ Z : ℝ in atTop,
    UnmarkedAt Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer P dBank G db Bshort order Cy I Cslot Z

theorem ready_unmarked (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nm buffer : ℝ)
    (P : UnmarkedPacket Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer) (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (Bshort : ℝ)
    (hBshort : 0 ≤ Bshort) (hτD : G.τ*(P.D:ℝ) ≤ heightLoss) :
    Nonempty (ReadyUnmarked Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer P dBank G db Bshort) := by
  obtain ⟨order,Cy,hCy,hevent⟩ := P.late (G.Mcap db) G.Bmask G.margin G.R G.τ G.ε G.ez G.κ G.heightCost
    G.hmargin G.hR G.hτ hτD G.height G.hε G.hez G.hez_small G.hκ G.hκ_small G.heightCost_nonneg G.budget
    Bshort hBshort (fun _=>1) (fun _=>zero_le_one)
  exact ⟨⟨order,Cy,hCy,hevent⟩⟩

def OrdinaryAt (Slot : Type) [Fintype Slot] [DecidableEq Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y dmin dmax εsource mesh : ℝ) (bank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ) → ℝ)
    (P : OrdinaryPacket Slot M A n y dmin εsource mesh bank dec) (T : Finset Slot)
    (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (m0 gap : ℝ) (order : ℕ) (C4 : ℝ)
    (S : Finset (ℕ×ℕ)) (C : ℝ) (I : ℕ) (U : ℝ) : Prop :=
    1 < U ∧
    ∀ (p : Profiles (1/4) (9/4)),
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → G.Mcap db+G.Bmask+G.margin ≤ d →
    ∀ s : NaturalState U G.Bmask A.bΦ,s.width ≤ G.Mcap db → s.character=A.ηShort →
    ∀ (hQM : s.fixedModulus ≤ M) (hQη : s.fixedModulus ≤ A.baseShort.modulus),
      s.mask=fixedBadMask*idealGenerator 1 →
      (∀ z : O,s.radial.keep z ↔ initialKeep s.character (internalQ A.QShort A.baseShort) z) →
    ∀ rows : Finset FreeRow,∀ hrows : ∀ u∈rows,s.radial.keep u.val,
      (∀ u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
    ∀ (K Je Jν : ℕ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀u : rows,SupportedWitness
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (U^d) ((51/100:ℝ)+G.ez*(band u).val) G.ε (cutoffTable (window u))
        (U^G.τ) ((U^d)^(G.τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
        Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+G.ez*tag.2.1.val;
    let i := tag.1.val;
    let m := Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val);
    let j := tag.2.2.2.1;
    let inverseLength := Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.1.val);
    let rows := TerminalActualRow.classRows parentRows
      (terminalWitnessKey level band window cutoffTable parentWS) tag;
    ∀ (r : ℝ) (c : Cutoff),0≤r → r≤G.R → a≤1 →
      cutoffTable tag.2.2.1=totalCutoff c → rows.Nonempty →
      (∀u : parentRows,zeroMaximum
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M A.Hr A.hHr s A.baseShort hQM hQη (hrows u.val u.property)
          (naturalRow s.character u.val.val u.val.property.1))
        (3*((level u).val+1:ℕ)*U^G.τ)<((51/100:ℝ)+G.ez*(band u).val)+2*G.ez) →
    ∀ (tShort : ℝ), |tShort|+U^G.τ/2≤(3*i+2:ℕ)*U^G.τ →
    ∀ (θ : T→RayQuotient.Characters M A.Hr)
      (w σslot v : T→ℝ) (θLong : T→RayQuotient.Characters M A.Hr) (σLong vLong : T→ℝ)
      (tMark tLong slotHeight heightLong XL : ℝ),
      (∀ k,0 ≤ w k) → (∀ k,w k ≤ mesh) →
      (∀ k,(33/50:ℝ) ≤ σslot k) → (∀ k,σslot k ≤ (33/50:ℝ)) →
      0 ≤ slotHeight → (∀ k,|v k| ≤ slotHeight) →
      (∀ k,(33/50:ℝ) ≤ σLong k) → (∀ k,σLong k ≤ (33/50:ℝ)) →
      0 ≤ heightLong → (∀ k,|vLong k| ≤ heightLong) →
      0 < XL → length U XL ≤ n →
      (∀ u∈rows,initialKeep A.ηLong (internalQ A.QLong A.baseLong) u.val) →
      (∀ u∈rows,∀ k,
        ‖normalizedSlot s.character (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M A.Hr 2 (U^d) w k)
          (originalCoefficients M A.Hr A.hHr A.baseShort θ A.W (U^d) w σslot v k) tMark ((U^d)^(w k))‖ =
        ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M A.Hr 2 (U^d) w k)
          (originalCoefficients M A.Hr A.hHr A.baseLong θLong A.W (U^d) w σLong vLong k) tLong ((U^d)^(w k))‖) →
      (∀ u∈rows,rowNorm u ≤ U^d) →
    ∀ (eResp eLower νLower step price V rounding collar Cslot buffer conductor : ℝ) (b : ℚ),
      sourceY0 ≤ y → y ≤ sourceY → y ≤ n → n ≤ sourceRatio*y →
      0 ≤ eResp → 0 ≤ eLower → eLower ≤ (responseUpper:ℝ) → eLower ≤ νLower → νLower ≤ 3/4 →
      νLower ≤ 2*a-1+price → 2*a-1 ≤ νLower+step → eResp ≤ eLower+step → 0 ≤ step → 0 ≤ price →
      CutoffGuard b c → y/(QRH.SourceCertificate.H:ℝ) ≤ (c.ordinary:ℝ) →
      sourceY0 ≤ (c.ordinary:ℝ) → PaidWithBand y eLower νLower c →
      inverseLength < (c.inverse:ℝ) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+collar →
      m0 ≤ (c.ordinary:ℝ) → G.ε ≤ 1/7500 →
      0 ≤ gap → gap ≤ 1 → 0 ≤ rounding → rounding ≤ gap → (∀ k,d*w k ≤ rounding) →
      sourceWidth n y-(u:ℝ) ≤ 1 →
      0 < Cslot → 0 ≤ buffer → d*r ≤ y →
      (∑ k,d*w k) ≤ sourceWidth n y-(u:ℝ) →
      (∀ u : rows,∀ k,w k=0 →
        ‖normalizedSlot s.character s.mask 1 u.val.val
          (originalPools M A.Hr 2 (U^d) w k)
          (originalCoefficients M A.Hr A.hHr A.baseShort θ A.W (U^d) w σslot v k) tMark ((U^d)^(w k))‖^2 ≤ Cslot*U^buffer) →
      (∀ u : rows,response U (Cslot*U^buffer) (fun k=>d*w k)
        (fun k=>‖normalizedSlot s.character s.mask 1 u.val.val
          (originalPools M A.Hr 2 (U^d) w k)
          (originalCoefficients M A.Hr A.hHr A.baseShort θ A.W (U^d) w σslot v k) tMark ((U^d)^(w k))‖^2) ≤ eResp) →
      |tMark|+|tLong|+slotHeight+heightLong ≤ U^G.τ →
      collar ≤ 3*conductor → 3*conductor ≤ (rho:ℝ)/128 →
      (responseUpper:ℝ)*(dmax*(2*gap)+dmax*gap+gap) ≤ (rho:ℝ)/128 →
      (15/4:ℝ)*dmax*G.ε ≤ (rho:ℝ)/128 → dmax*εsource ≤ (rho:ℝ)/128 →
      buffer*(Fintype.card T:ℝ) ≤ (rho:ℝ)/128 →
      G.τ*((P.degree T+2*P.J T+1:ℕ):ℝ) ≤ (rho:ℝ)/128 →
      3*step+price*d*m ≤ (rho:ℝ)/128 →
      StrongPair.finiteEnergyOn Finset.univ rows A.ηLong s.character
        ((TerminalProfileUniform.unitPair S C p).profile 0) ((TerminalProfileUniform.unitPair S C p).profile 1) tLong tShort XL ((U^d)^r)
        (fun k u=>normalizedSlot s.character s.mask 1 u.val
          (originalPools M A.Hr 2 (U^d) w k)
          (originalCoefficients M A.Hr A.hHr A.baseShort θ A.W (U^d) w σslot v k) tMark ((U^d)^(w k))) ≤
        ((max 1 Cslot)^(Fintype.card T)*
          (C4*12*P.Csource T*QuadraticInitialBound.diagonalControl radialMajorant*P.Crow T^2)*(4:ℝ)^P.degree T*
              (1+2*Real.pi+(3*I:ℕ))^(2*P.J T+1))*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((QRH.SourceCertificate.H:ℝ)-V))

structure ReadyOrdinary (Slot : Type) [Fintype Slot] [DecidableEq Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y dmin dmax εsource mesh : ℝ) (bank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ) → ℝ)
    (P : OrdinaryPacket Slot M A n y dmin εsource mesh bank dec) (T : Finset Slot)
    (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (m0 gap : ℝ) where
  order : ℕ
  C4 : ℝ
  C4_pos : 0 < C4
  S : Finset (ℕ×ℕ)
  S_zero : (0,0) ∈ S
  C : ℝ
  C_one : 1 ≤ C
  event : ∀I : ℕ,∀ᶠ U : ℝ in atTop,
    OrdinaryAt Slot M A n y dmin dmax εsource mesh bank dec P T dBank G db m0 gap order C4 S C I U

theorem ready_ordinary (Slot : Type) [Fintype Slot] [DecidableEq Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y dmin dmax εsource mesh : ℝ) (bank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ) → ℝ)
    (P : OrdinaryPacket Slot M A n y dmin εsource mesh bank dec) (T : Finset Slot)
    (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (m0 gap : ℝ)
    (hes : 0 ≤ εsource)
    (hbank : ∀b∈bank,(98/100:ℝ) ≤ b.1 ∧ b.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ b.2 ∧ b.2 ≤ 51/100 ∧
      0 < dec b ∧ dec b ≤ gap ∧ 0 < nearOrdinaryQuota n b.2 b.1-dec b)
    (hnet : ∀d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
      ∃b∈bank,b.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-b.1 < gap ∧ m ≤ b.2 ∧ b.2-m < gap) :
    Nonempty (ReadyOrdinary Slot M A n y dmin dmax εsource mesh bank dec P T dBank G db m0 gap) := by
  have h := terminal_actual_class_ordinary_selected T M A.Hr A.hHr A.W A.bΦ
    A.ηLong A.baseLong A.ηShort A.baseShort A.QLong A.QShort n y dmin εsource mesh bank dec
    (P.degree T) (P.controls T) (P.Csource T) (P.J T) (P.Crow T) (P.positive T).1.le hes
    m0 gap hbank hnet (P.physical T)
  obtain ⟨order,C4,hC4,S,hS,C,hC,hevent⟩ := h A.bΦ (G.Mcap db) G.Bmask G.margin G.R dmax G.τ G.ε G.ez G.κ G.heightCost
    (by linarith [A.hbΦ]) G.hmargin G.hR G.hdmax G.hτ G.height G.hε G.hez G.hez_small G.hκ G.hκ_small
    G.heightCost_nonneg G.budget
  exact ⟨⟨order,C4,hC4,S,hS,C,hC,hevent⟩⟩

#print axioms ready_marked
#print axioms ready_unmarked
#print axioms ready_ordinary
end
end QRH.Cycle092.P2CommonSourceMetadata
