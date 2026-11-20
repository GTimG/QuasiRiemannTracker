/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
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
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataTypes_605f7d967350f20c_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

structure Arithmetic (M : Ideal O) [NeZero M] where
  Hr : Subgroup (O⧸M)ˣ
  hHr : RayOrthogonality.globalUnits M ≤ Hr
  W : ℝ→ℂ
  hW : ContDiff ℝ ∞ W
  hWs : Function.support W ⊆ Icc (1:ℝ) 2
  bΦ : ℝ
  hbΦ : 2 ≤ bΦ
  hΦ : Function.support (radialMajorant:ℝ→ℂ) ⊆ Iic bΦ
  old : Character
  base : Character
  Qold : Ideal O
  hQoldM : Qold ≤ M
  hQoldBase : Qold ≤ base.modulus
  ηLong : Character
  ηShort : Character
  baseLong : Character
  baseShort : Character
  QLong : Ideal O
  QShort : Ideal O
  hQLM : QLong ≤ M
  hQL0 : internalQ QLong baseLong ≠ 0
  hQLt : internalQ QLong baseLong ≠ ⊤
  hQL72 : internalQ QLong baseLong ≤ Ideal.span {(72:O)}
  hQSM : QShort ≤ M
  hQS0 : internalQ QShort baseShort ≠ 0
  hQSt : internalQ QShort baseShort ≠ ⊤
  hQS72 : internalQ QShort baseShort ≤ Ideal.span {(72:O)}

def nativeK (buffer dmax : ℝ) : ℕ := ⌈(7/37:ℝ)/((buffer/2)/dmax)⌉₊+1

def SmallPhysical (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (n y mesh : ℝ)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
    ∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀ V : ℝ,0 ≤ V  →  V ≤ 98/100  → 
    ∀ (J : Finset Slot) (θ θ₁ θ₂ : Slot → RayQuotient.Characters M A.Hr)
      (w σ σ₁ σ₂ v v₁ v₂ : Slot → ℝ) (tOld t₁ t₂ heightOld height : ℝ),
      (∀i,0 ≤ w i)  →  (∀i,w i ≤ mesh)  → 
      (∀i,σ i=33/50)  → 
      (∀i,(33/50:ℝ) ≤ σ₁ i)  →  (∀i,σ₁ i ≤ (33/50:ℝ))  → 
      (∀i,(33/50:ℝ) ≤ σ₂ i)  →  (∀i,σ₂ i ≤ (33/50:ℝ))  → 
      (∀i,|v i| ≤ heightOld)  →  |tOld|+heightOld ≤ U^(1/2:ℝ)  → 
      0 ≤ height  →  (∀i,|v₁ i| ≤ height)  →  (∀i,|v₂ i| ≤ height)  → 
      (∑i ∈ J,w i) ≤ sourceWidth n y-(u:ℝ)  → 
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁  →  0 < X₂  → 
      length U X₁ ≤ n  →  length U X₂ ≤ y  → 
    ∀ rows : Finset FreeRow,
      (∀z ∈ rows,initialKeep A.old A.Qold z.val)  → 
      (∀z ∈ rows,initialKeep A.ηLong (internalQ A.QLong A.baseLong) z.val)  → 
      (∀z ∈ rows,initialKeep A.ηShort (internalQ A.QShort A.baseShort) z.val)  → 
      (∀z ∈ rows,rowNorm z ≤ U^V)  → 
      (∀z ∈ rows,∀i ∈ J,‖originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld i z‖=
        ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 z.val
          (originalPools M A.Hr 2 U w i)
          (originalCoefficients M A.Hr A.hHr A.baseLong θ₁ A.W U w σ₁ v₁ i) t₁ (U^(w i))‖)  → 
      (∀z ∈ rows,∀i ∈ J,‖originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld i z‖=
        ‖normalizedSlot A.ηShort (fixedBadMask*idealGenerator 1) 1 z.val
          (originalPools M A.Hr 2 U w i)
          (originalCoefficients M A.Hr A.hHr A.baseShort θ₂ A.W U w σ₂ v₂ i) t₂ (U^(w i))‖)  → 
      finiteEnergyOn J rows A.ηLong A.ηShort (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂
        (originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld) ≤ 
        C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
          (1+|t₁|+|t₂|+height)^degree*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))

def LowHighPhysical (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (n y e Vmax mesh buffer : ℝ)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) : Prop :=
    ∀ Cslot : ℝ,0 < Cslot → ∃ C : ℝ,0< C ∧
    ∀ᶠ U : ℝ in atTop,∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax →
    ∀ T : Finset Slot,∀ (θ θ₁ θ₂ : Slot→RayQuotient.Characters M A.Hr) (w σ σ₁ σ₂ v v₁ v₂ : Slot→ℝ)
      (tOld t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ mesh) →
      (∀ i,(33/50:ℝ)≤σ i) → (∀ i,σ i≤(33/50:ℝ)) →
      (∀ i,(33/50:ℝ) ≤ σ₁ i) → (∀ i,σ₁ i ≤ (33/50:ℝ)) →
      (∀ i,(33/50:ℝ) ≤ σ₂ i) → (∀ i,σ₂ i ≤ (33/50:ℝ)) →
      0 ≤ height → (∀ i,|v₁ i| ≤ height) → (∀ i,|v₂ i| ≤ height) →
      (∑ i∈T,w i) ≤ sourceWidth n y-(u:ℝ) →
    ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ),0 < X₁ → 0 < X₂ →
      length U X₁ ≤ n → length U X₂ ≤ y →
    ∀ (s : Finset FreeRow),
      (∀ u∈s,initialKeep A.ηLong (internalQ A.QLong A.baseLong) u.val) →
      (∀ u∈s,initialKeep A.ηShort (internalQ A.QShort A.baseShort) u.val) →
      (∀ u∈s,rowNorm u ≤ U^V) →
      (∀ u∈s,∀ i∈T,‖(originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld) i u‖=
        ‖normalizedSlot A.ηLong (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M A.Hr 2 U w i) (originalCoefficients M A.Hr A.hHr A.baseLong θ₁ A.W U w σ₁ v₁ i) t₁ (U^(w i))‖) →
      (∀ u∈s,∀ i∈T,‖(originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld) i u‖=
        ‖normalizedSlot A.ηShort (fixedBadMask*idealGenerator 1) 1 u.val
          (originalPools M A.Hr 2 U w i) (originalCoefficients M A.Hr A.hHr A.baseShort θ₂ A.W U w σ₂ v₂ i) t₂ (U^(w i))‖) →
    finiteEnergyOn T (s.filter (fun u=> response U (Cslot*U^buffer) (fun i:T=> w i.val) (fun i=>‖(originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld) i.val u‖^2) ≤ e)) A.ηLong A.ηShort (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ (originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld)+
    finiteEnergyOn T (s.filter (fun u=> response U (Cslot*U^buffer) (fun i:T=> w i.val) (fun i=>‖(originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld) i.val u‖^2) > (5002/10000:ℝ))) A.ηLong A.ηShort (p.profile 0) (p.profile 1) t₁ t₂ X₁ X₂ (originalMark M A.Hr A.hHr A.old A.base θ A.W U w σ v tOld) ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control controls)^2*
        (1+|t₁|+|t₂|+height)^degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))

def MarkedLate (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (ρ : Contract.AnchorRect) (εm nativeError N quota dmin dmax price inverseMesh nativeMesh buffer : ℝ)
    (Jc : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℕ)
    (Cc : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℝ)
    (degree : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℕ)
    (controls : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→Finset (ℕ×ℕ))
    (Cl : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℝ) (D : ℕ) : Prop :=
    let b := buffer/2;
    let Kbig := nativeK buffer dmax;
    ∀ (Mcap Bmask margin R τ εshort ez κ heightCost : ℝ)
    (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hτ : 0 < τ) (hτD : τ*(D:ℝ) ≤ heightLoss) (hheight : 4*τ < dmin*heightCost) (hεshort : 0 < εshort)
    (hez : 0 < ez) (hez' : ez < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hcost : 0 ≤ heightCost)
    (hbudget : 12*ez*(R+2)+8*κ+2*heightCost ≤ εshort)
    (Bshort : ℝ) (hBshort : 0 ≤ Bshort)
    (profileBound : ℕ→ℝ) (hprofile : ∀ j,0 ≤ profileBound j) ,
    ∃ order : Fin (Kbig+1)→Fin (Kbig+1)→ℕ,∃ Cy : Fin (Kbig+1)→Fin (Kbig+1)→ℝ,(∀ ki kl,0 < Cy ki kl) ∧
    ∀ (I : ℕ) (Cslot : ℝ),0 < Cslot →
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState Z Bmask A.bΦ,s.width ≤ Mcap → s.character=A.ηShort → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ A.baseShort.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+ez*(band u).val) ε (cutoffTable (window u))
        (Z^τ) ((Z^d)^(τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
        Fin (dyadicLength (Z^d))×Fin (dyadicLength (Z^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+ez*tag.2.1.val;
    let i := tag.1.val;
    let cutoff := cutoffTable tag.2.2.1;
    let T := Z^τ;
    let allowance := (Z^d)^(τ/(2*dmax));
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
        (3*((level u).val+1 : ℕ)*Z^τ) < ((51/100:ℝ)+ez*(band u).val)+2*ez) →
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ) (Y : ℝ),
      0 ≤ yCell → yCell/d ≤ R → 0 < Y → Y ≤ Z^yCell →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,Function.support (twistProfile (Wi u) (σi u) (fi u)) ⊆ Iic (9/4:ℝ)) →
      (∀ u∈rows,∀ x,‖twistProfile (Wi u) (σi u) (fi u) x‖ ≤ Bshort) →
      (∀ u∈rows,|fi u|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ ki kl : Fin (Kbig+1),∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order ki kl+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order ki kl+2)) →
    ∀ (θ θLong : Slot→RayQuotient.Characters M A.Hr) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L ζ X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ min inverseMesh nativeMesh) →
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
      d*εshort+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
      |tMark|+|tLong|+slotHeight ≤ Z^τ →
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
      (Cslot^(Fintype.card Slot)*Cy ki kl*(12*Cc ki kl+1)*
        (Cl ki kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls ki kl) (p.profile jprofile))^4+1)*
        (2+2*Real.pi+(3*I:ℕ))^(Jc ki kl+1)*(3:ℝ)^(degree ki kl))*
      Z^(V+radialAllowance V+loss+heightLoss)

structure MarkedPacket (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (ρ : Contract.AnchorRect) (εm nativeError N quota dmin dmax price inverseMesh nativeMesh buffer : ℝ) where
  Fbound : ℝ
  hFbound : 0<Fbound
  Jc : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℕ
  Cc : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℝ
  degree : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℕ
  controls : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→Finset (ℕ×ℕ)
  Cl : Fin (nativeK buffer dmax+1)→Fin (nativeK buffer dmax+1)→ℝ
  D : ℕ
  hD : ∀ ki kl,Jc ki kl+degree ki kl+1≤D
  positive : ∀ ki kl,0<Cc ki kl ∧ 0<Cl ki kl
  late : MarkedLate Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
    ρ εm nativeError N quota dmin dmax price inverseMesh nativeMesh buffer Jc Cc degree controls Cl D

def UnmarkedLate (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nativeMesh buffer : ℝ)
    (Jc : Fin (nativeK buffer dmax+1)→ℕ)
    (Cc : Fin (nativeK buffer dmax+1)→ℝ)
    (degree : Fin (nativeK buffer dmax+1)→ℕ)
    (controls : Fin (nativeK buffer dmax+1)→Finset (ℕ×ℕ))
    (Cl : Fin (nativeK buffer dmax+1)→ℝ) (D : ℕ) : Prop :=
    let b := buffer/2;
    let Kbig := nativeK buffer dmax;
    ∀ (Mcap Bmask margin R τ εshort ez κ heightCost : ℝ)
    (hmargin : 0 < margin) (hR : 0 ≤ R)
    (hτ : 0 < τ) (hτD : τ*(D:ℝ) ≤ heightLoss) (hheight : 4*τ < dmin*heightCost) (hεshort : 0 < εshort)
    (hez : 0 < ez) (hez' : ez < 1/1000) (hκ : 0 < κ) (hκ' : κ ≤ 1) (hcost : 0 ≤ heightCost)
    (hbudget : 12*ez*(R+2)+8*κ+2*heightCost ≤ εshort)
    (Bshort : ℝ) (hBshort : 0 ≤ Bshort)
    (profileBound : ℕ→ℝ) (hprofile : ∀ j,0 ≤ profileBound j) ,
    ∃ order : Fin (Kbig+1)→ℕ,∃ Cy : Fin (Kbig+1)→ℝ,(∀ kl,0 < Cy kl) ∧
    ∀ (I : ℕ) (Cslot : ℝ),0 < Cslot →
    ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ d : ℝ,dmin ≤ d → d ≤ dmax → Mcap+Bmask+margin ≤ d →
    ∀ s : NaturalState Z Bmask A.bΦ,s.width ≤ Mcap → s.character=A.ηShort → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ A.baseShort.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M A.Hr A.hHr s A.baseShort (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+ez*(band u).val) ε (cutoffTable (window u))
        (Z^τ) ((Z^d)^(τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
        Fin (dyadicLength (Z^d))×Fin (dyadicLength (Z^d))),
    let parentRows := rows;
    let a := (51/100:ℝ)+ez*tag.2.1.val;
    let i := tag.1.val;
    let cutoff := cutoffTable tag.2.2.1;
    let T := Z^τ;
    let allowance := (Z^d)^(τ/(2*dmax));
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
        (3*((level u).val+1 : ℕ)*Z^τ) < ((51/100:ℝ)+ez*(band u).val)+2*ez) →
      0 ≤ ε → ε ≤ 1/1000 → 1 ≤ cutoff → cutoff ≤ 3/2 →
    ∀ (Wi : FreeRow→ℝ→ℂ) (Ai Bi σi fi : FreeRow→ℝ) (Y : ℝ),
      0 ≤ yCell → yCell/d ≤ R → 0 < Y → Y ≤ Z^yCell →
      (∀ u∈rows,0 < Ai u) → (∀ u∈rows,Function.support (Wi u) ⊆ Icc (Ai u) (Bi u)) →
      (∀ u∈rows,ContDiff ℝ ∞ (Wi u)) →
      (∀ u∈rows,Function.support (twistProfile (Wi u) (σi u) (fi u)) ⊆ Iic (9/4:ℝ)) →
      (∀ u∈rows,∀ x,‖twistProfile (Wi u) (σi u) (fi u) x‖ ≤ Bshort) →
      (∀ u∈rows,|fi u|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^2*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound 2) →
      (∀ kl : Fin (Kbig+1),∀ u∈rows,∀ x∈Icc (1-a-6*ez-σi u) (2-σi u),∀ t:ℝ,
        (1+|t|)^(order kl+2)*‖mellin (Wi u) ((x:ℂ)+t*Complex.I)‖ ≤ profileBound (order kl+2)) →
    ∀ (θ θLong : Slot→RayQuotient.Characters M A.Hr) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ nativeMesh) →
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
      d*εshort+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
      |tMark|+|tLong|+slotHeight ≤ Z^τ →
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
      (Cslot^(Fintype.card Slot)*Cy kl*(192*Cc kl+1)*
        (Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls kl) (p.profile jprofile))^4+1)*
        (2+2*Real.pi+(3*I:ℕ))^(Jc kl+1)*(3:ℝ)^(degree kl))*
      Z^(V+radialAllowance V+loss+heightLoss)



structure UnmarkedPacket (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nativeMesh buffer : ℝ) where
  Fbound : ℝ
  hFbound : 0<Fbound
  Jc : Fin (nativeK buffer dmax+1)→ℕ
  Cc : Fin (nativeK buffer dmax+1)→ℝ
  degree : Fin (nativeK buffer dmax+1)→ℕ
  controls : Fin (nativeK buffer dmax+1)→Finset (ℕ×ℕ)
  Cl : Fin (nativeK buffer dmax+1)→ℝ
  D : ℕ
  hD : ∀kl,Jc kl+degree kl+1≤D
  positive : ∀kl,0<Cc kl ∧ 0<Cl kl
  late : UnmarkedLate Slot M A n yCell e0 nu0 loss heightLoss c step δ fee
    εm nativeError N quota dmin dmax price nativeMesh buffer Jc Cc degree controls Cl D

end
end QRH.Cycle092.P2CommonSourceMetadata
