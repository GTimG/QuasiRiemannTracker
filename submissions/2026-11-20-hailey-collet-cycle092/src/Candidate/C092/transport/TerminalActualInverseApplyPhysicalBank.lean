/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual event-free P6 suppliers on a finite bank of checked length/response
labels. Scalar fees, the common genuine rectangle bank and all physical
source meshes precede Slot, arithmetic data and live rows. -/
import Candidate.C092.transport.TerminalActualInverseApplyFiniteBank
import Candidate.C092.transport.StrongPairRegularTerminalNativeCaps

set_option autoImplicit false
set_option linter.unusedVariables false
namespace QRH.Cycle092.StrongPair
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter Set OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentWholeSlotDeletion HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorZeros
open CenteredMomentPrimeSlot CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyBands ConcretePrimeRowBridge
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentInductionEnergy
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.LowActual
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open Qrh.MarkedAnchor.Interface QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.MediumInversePrice QRH.Cycle092.TinyCore
open QRH.Cycle092.TerminalActualRow QRH.Cycle092.RegularColoredForward
open QRH.Cycle092.SourceInverseP6
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_TerminalActualInverseApplyPhysicalBank_2525c187ef990d95_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def TerminalActualClassMarkedPhysical (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (ρ : Contract.AnchorRect) (εm nativeError N quota dmin dmax price inverseMesh nativeMesh : ℝ) : Prop :=
    ∀ (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ ηlong baseLong : Character) (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q baseLong ≠ 0)
    (hQt : internalQ Q baseLong ≠ ⊤) (hQ72 : internalQ Q baseLong ≤ Ideal.span {(72:O)})
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ→ℂ) ⊆ Iic bΦ),
    ∃ Fbound : ℝ,0 < Fbound ∧
    ∀ (buffer : ℝ),0 < buffer →
    let b := buffer/2;
    let Kbig := ⌈(7/37:ℝ)/(b/dmax)⌉₊+1;
    ∃ Jc : Fin (Kbig+1)→Fin (Kbig+1)→ℕ,
    ∃ Cc : Fin (Kbig+1)→Fin (Kbig+1)→ℝ,
    ∃ degree : Fin (Kbig+1)→Fin (Kbig+1)→ℕ,
    ∃ controls : Fin (Kbig+1)→Fin (Kbig+1)→Finset (ℕ×ℕ),
    ∃ Cl : Fin (Kbig+1)→Fin (Kbig+1)→ℝ,
    ∃ D : ℕ,(∀ ki kl,Jc ki kl+degree ki kl+1 ≤ D) ∧
      (∀ ki kl,0 < Cc ki kl ∧ 0 < Cl ki kl) ∧
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
    ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap → s.character=η → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ η₀.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M H hH s η₀ (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+ez*(band u).val) ε (cutoffTable (window u))
        (Z^τ) ((Z^d)^(τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M H×RayQuotient.Characters M H)×
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
        (family M H hH s η₀ (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M H hH s η₀ hsM hsη (hkeep u.val u.property)
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
    ∀ (θ θLong : Slot→RayQuotient.Characters M H) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L ζ X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ min inverseMesh nativeMesh) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) → (∀ j,|vLong j| ≤ slotHeight) →
      (∀ u∈rows,∀ j,‖descriptor M H hH η η₀ W Z θ w v tMark u j‖=
        ‖normalizedSlot ηlong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M H 2 (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter M H hH baseLong (θLong j)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖) →
      0 ≤ eu →
      (∑ j,w j) ≤ L → 0 ≤ ζ → 367/500 ≤ r →
      0 ≤ QRH.Cycle092.Source.inverseQuota r-ζ →
      ρ.Admissible r (QRH.Cycle092.Source.inverseQuota r-ζ) 1 →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep ηlong (internalQ Q baseLong) u.val) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      nu0 ≤ 2*a-1+price → 2*a-1 ≤ nu0+step → eu ≤ e0+step →
      (c.inverse:ℝ) ≤ r → r ≤ 1 → 0 ≤ ε → ε ≤ fee →
      0 ≤ L → L ≤ 1 → L ≤ sourceWidth n yCell-(u:ℝ) →
      2*NativeFourthEffective.credit n d-d*quota ≤ fee/2 →
      ζ ≤ fee/2 →
      d*εshort+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
      |tMark|+|tLong|+slotHeight ≤ Z^τ →
    ∀ (jd : Slot) (p : Profiles (1/4) (9/4)) (jprofile : Fin 2),
    let selectedRows := descriptorRows M H hH rows η η₀ W Z (Cslot*Z^buffer) b θ w v tMark jd;
      selectedRows.Nonempty →
      (∀ u∈selectedRows,e0 ≤ measured M H hH η η₀ W Z (Cslot*Z^buffer) θ w v tMark u) →
      (∀ u∈selectedRows,measured M H hH η η₀ W Z (Cslot*Z^buffer) θ w v tMark u ≤ eu) →
    let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T);
    let hl := |tMark|+|tLong|+slotHeight;
    ∃ ki kl : Fin (Kbig+1),
    (∑ u∈selectedRows,‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val
      (p.profile jprofile) tLong X*
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 Y*
      (∏ j,descriptor M H hH η η₀ W Z θ w v tMark u j)‖^2) ≤
      (Cslot^(Fintype.card Slot)*Cy ki kl*(12*Cc ki kl+1)*
        (Cl ki kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls ki kl) (p.profile jprofile))^4+1)*
        (2+2*Real.pi+(3*I:ℕ))^(Jc ki kl+1)*(3:ℝ)^(degree ki kl))*
      Z^(V+radialAllowance V+loss+heightLoss)

def TerminalActualClassUnmarkedPhysical (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nativeMesh : ℝ) : Prop :=
    ∀ (Slot : Type) [Fintype Slot]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hWs : Function.support W ⊆ Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ ηlong baseLong : Character) (Q : Ideal O) (hQM : Q ≤ M) (hQ0 : internalQ Q baseLong ≠ 0)
    (hQt : internalQ Q baseLong ≠ ⊤) (hQ72 : internalQ Q baseLong ≤ Ideal.span {(72:O)})
    (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (hsΦ : Function.support (radialMajorant : ℝ→ℂ) ⊆ Iic bΦ),
    ∃ Fbound : ℝ,0 < Fbound ∧
    ∀ (buffer : ℝ),0 < buffer →
    let b := buffer/2;
    let Kbig := ⌈(7/37:ℝ)/(b/dmax)⌉₊+1;
    ∃ Jc : Fin (Kbig+1)→ℕ,
    ∃ Cc : Fin (Kbig+1)→ℝ,
    ∃ degree : Fin (Kbig+1)→ℕ,
    ∃ controls : Fin (Kbig+1)→Finset (ℕ×ℕ),
    ∃ Cl : Fin (Kbig+1)→ℝ,
    ∃ D : ℕ,(∀ kl,Jc kl+degree kl+1 ≤ D) ∧
      (∀ kl,0 < Cc kl ∧ 0 < Cl kl) ∧
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
    ∀ s : NaturalState Z Bmask bΦ,s.width ≤ Mcap → s.character=η → s.puncture=1 →
    ∀ (hsM : s.fixedModulus ≤ M) (hsη : s.fixedModulus ≤ η₀.modulus)
      (rows : Finset FreeRow) (hkeep : ∀ u∈rows,s.radial.keep u.val),
      (∀ u∈rows,s.radial.profile (‖ConcreteTraceCRT.eisEmbedding u.val‖^2/s.radial.scale) ≠ 0) →
      (∀ u∈rows,rowNorm u ≤ Z^d) →
    ∀ (K Je Jν : ℕ) (ε : ℝ)
      (level : rows→Fin (I+1)) (band : rows→Fin (K+1))
      (window : rows→Fin Je×Fin Jν) (cutoffTable : Fin Je×Fin Jν→ℝ)
      (parentWS : ∀ u : rows,SupportedWitness
        (family M H hH s η₀ (naturalRow s.character u.val.val u.val.property.1))
        (Z^d) ((51/100:ℝ)+ez*(band u).val) ε (cutoffTable (window u))
        (Z^τ) ((Z^d)^(τ/(2*dmax))) (level u).val)
      (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×
        Option (RayQuotient.Characters M H×RayQuotient.Characters M H)×
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
        (family M H hH s η₀ (naturalRow s.character u.val.val u.val.property.1))
        (family_nonprincipal M H hH s η₀ hsM hsη (hkeep u.val u.property)
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
    ∀ (θ θLong : Slot→RayQuotient.Characters M H) (w v vLong : Slot→ℝ)
      (tMark tLong slotHeight eu L X V : ℝ),
      (∀ j,0 ≤ w j) → (∀ j,w j/d ≤ nativeMesh) →
      0 ≤ slotHeight → (∀ j,|v j| ≤ slotHeight) → (∀ j,|vLong j| ≤ slotHeight) →
      (∀ u∈rows,∀ j,‖descriptor M H hH η η₀ W Z θ w v tMark u j‖=
        ‖normalizedSlot ηlong (fixedBadMask*idealGenerator 1) 1 u.val (primePool M H 2 (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter M H hH baseLong (θLong j)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w j)) (33/50) (vLong j) I) tLong (Z^(w j))‖) →
      0 ≤ eu →
      (∑ j,w j) ≤ L →
      0 < X → length (Z^d) X ≤ N →
      (∀ u∈rows,initialKeep ηlong (internalQ Q baseLong) u.val) →
      (98/100:ℝ) ≤ V → V ≤ d → d ≤ V+3*δ →
      nu0 ≤ 2*a-1+price → 2*a-1 ≤ nu0+step → eu ≤ e0+step →
      (c.inverse:ℝ) ≤ r → cutoff=totalCutoff c → ε ≤ fee →
      0 ≤ L → L ≤ 1 → L ≤ sourceWidth n yCell-(u:ℝ) →
      2*NativeFourthEffective.credit n d-d*quota ≤ fee/2 →
      (r ≤ 1 → inverseQuota r ≤ fee) →
      d*εshort+(d*(2*ε+εm)+d*nativeError)/2+buffer*(Fintype.card Slot:ℝ) ≤ fee →
      |tMark|+|tLong|+slotHeight ≤ Z^τ →
    ∀ (jd : Slot) (p : Profiles (1/4) (9/4)) (jprofile : Fin 2),
    let selectedRows := descriptorRows M H hH rows η η₀ W Z (Cslot*Z^buffer) b θ w v tMark jd;
      selectedRows.Nonempty →
      (∀ u∈selectedRows,e0 ≤ measured M H hH η η₀ W Z (Cslot*Z^buffer) θ w v tMark u) →
      (∀ u∈selectedRows,measured M H hH η η₀ W Z (Cslot*Z^buffer) θ w v tMark u ≤ eu) →
    let hi := max (|tMark|+slotHeight) (2*Real.pi*allowance+(3*i:ℕ)*T);
    let hl := |tMark|+|tLong|+slotHeight;
    ∃ kl : Fin (Kbig+1),
    (∑ u∈selectedRows,‖original ηlong (fixedBadMask*idealGenerator 1) 1 u.val
      (p.profile jprofile) tLong X*
      original s.character s.mask 1 u.val (twistProfile (Wi u) (σi u) (fi u)) 0 Y*
      (∏ j,descriptor M H hH η η₀ W Z θ w v tMark u j)‖^2) ≤
      (Cslot^(Fintype.card Slot)*Cy kl*(192*Cc kl+1)*
        (Cl kl*QuadraticInitialBound.diagonalControl radialMajorant*
          (sourceControl (controls kl) (p.profile jprofile))^4+1)*
        (2+2*Real.pi+(3*I:ℕ))^(Jc kl+1)*(3:ℝ)^(degree kl))*
      Z^(V+radialAllowance V+loss+heightLoss)

/-- One finite genuine source bank with a common positive physical mesh.
Native cap/quota guards and their payment are proved at every genuine bank
radius. The final physical suppliers still quantify Slot AFTER this mesh. -/
theorem terminal_finite_actual_class_physical_bank {Key : Type} [Fintype Key]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (n y el ν : Key→ℝ) (cut : Key→Cutoff) (bcell : Key→ℚ)
    (hy0 : ∀ k,sourceY0 ≤ y k) (hy1 : ∀ k,y k ≤ sourceY) (hyn : ∀ k,y k ≤ n k)
    (hn : ∀ k,n k ≤ sourceRatio*y k) (he : ∀ k,0 ≤ el k)
    (hν0 : ∀ k,el k ≤ ν k) (hν1 : ∀ k,ν k ≤ 3/4)
    (hg : ∀ k,CutoffGuard (bcell k) (cut k))
    (hp : ∀ k,PaidWithBand (y k) (el k) (ν k) (cut k))
    {loss : ℝ} (hloss : 0 < loss) (heightLoss : ℝ) (hheightLoss : 0 ≤ heightLoss)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (dBank : Finset ℝ) (hdb : ∀ d∈dBank,(98/100:ℝ) ≤ d ∧ dmin ≤ d ∧ d ≤ dmax)
    (price : ℝ) (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4) :
    ∃ feeM feeU commonFee : Key→ℝ,
      (∀ k,0 < feeM k ∧ 0 < feeU k ∧ 0 < commonFee k ∧ commonFee k ≤ feeM k ∧ commonFee k ≤ feeU k) ∧
    ∃ ζ : ℝ,0 < ζ ∧ (∀ k,ζ ≤ commonFee k/2) ∧
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1/1000 ∧ 3*δ ≤ ζ ∧
    ∃ J : ℕ,∃ bank : Fin J → Contract.AnchorRect,
      (∀ j,Contract.UniformInverseRectSource Contract.canonicalFamily (bank j)) ∧
      (∀ r : ℝ,367/500 ≤ r → r ≤ 1 →
        inverseQuota r ≤ ζ ∨ (0 ≤ inverseQuota r-ζ → ∃ j,(bank j).Admissible r (inverseQuota r-ζ) 1)) ∧
    ∃ quota : Key→dBank→ℝ,
      (∀ k d,0 ≤ terminalNativeCap (n k) d.val ∧ terminalNativeCap (n k) d.val < 1/2 ∧
        0 < quota k d ∧ quota k d < 3/20 ∧ quota k d < (1-2*terminalNativeCap (n k) d.val)/2 ∧
        2*NativeFourthEffective.credit (n k) d.val-d.val*quota k d ≤ commonFee k/4 ∧
        ∀ {U X : ℝ},0 < U → length U X ≤ n k → length (U^d.val) X ≤ terminalNativeCap (n k) d.val) ∧
    ∃ im nm : Key→dBank→Fin J→ℝ,∃ nu : Key→dBank→ℝ,
      (∀ k d j,0 < im k d j ∧ 0 < nm k d j) ∧ (∀ k d,0 < nu k d) ∧
    ∃ mesh : ℝ,0 < mesh ∧
      (∀ k d j,mesh ≤ im k d j ∧ mesh ≤ nm k d j) ∧ (∀ k d,mesh ≤ nu k d) ∧
      (∀ k d j,TerminalActualClassMarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeM k)
        (bank j) εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price (im k d j) (nm k d j)) ∧
      (∀ k d,TerminalActualClassUnmarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeU k)
        εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price (nu k d)) := by
  obtain ⟨feeM,feeU,fc,hfee,hM,hU,ζ,hζ,hζf,δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover⟩ :=
    terminal_finite_actual_class_inverse_bank hβ n y el ν cut bcell
      (by intro k;simpa only [sourceY0] using hy0 k) hy1 hn he hν0 hν1 hg hp hloss heightLoss hheightLoss
  have hnat (k : Key) (d : dBank) := terminal_native_source_parameters (hy0 k) (hy1 k) (hyn k) (hn k)
    (hdb d.val d.property).1 (hfee k).2.2.1
  choose quota hN0 hN hq hqcap hqmean hbudget hlength using hnat
  have hm (k : Key) (d : dBank) (j : Fin J) :
      ∃ im nm : ℝ,0 < im ∧ 0 < nm ∧
        TerminalActualClassMarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeM k)
          (bank j) εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price im nm := by
    simpa only [TerminalActualClassMarkedPhysical] using
      hM k hβ (bank j) (hsource j) εm nativeError hεm hnativeError (hN k d).le
        (hq k d).le (hqcap k d) (hqmean k d) dmin dmax hdmin hdmax price hprice0 hpriceBudget
  have hu (k : Key) (d : dBank) :
      ∃ nu : ℝ,0 < nu ∧
        TerminalActualClassUnmarkedPhysical (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeU k)
          εm nativeError (terminalNativeCap (n k) d.val) (quota k d) dmin dmax price nu := by
    simpa only [TerminalActualClassUnmarkedPhysical] using
      hU k hβ εm nativeError hεm hnativeError (hN k d).le
        (hq k d).le (hqcap k d) (hqmean k d) dmin dmax hdmin hdmax price hprice0 hpriceBudget
  choose im nm him hnm hmarked using hm
  choose nu hnu hunmarked using hu
  let meshes : (Key×dBank×Fin J)⊕(Key×dBank)→ℝ :=
    Sum.elim (fun p=>min (im p.1 p.2.1 p.2.2) (nm p.1 p.2.1 p.2.2)) (fun p=>nu p.1 p.2)
  have hmeshes : ∀ k,0 < meshes k := by
    intro k
    cases k with
    | inl p => exact lt_min (him p.1 p.2.1 p.2.2) (hnm p.1 p.2.1 p.2.2)
    | inr p => exact hnu p.1 p.2
  obtain ⟨mesh,hmesh,hfloor⟩ := terminal_positive_mesh_floor meshes hmeshes
  refine ⟨feeM,feeU,fc,hfee,ζ,hζ,hζf,δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover,quota,
    fun k d=>⟨hN0 k d,hN k d,hq k d,hqcap k d,hqmean k d,hbudget k d,hlength k d⟩,
    im,nm,nu,fun k d j=>⟨him k d j,hnm k d j⟩,hnu,mesh,hmesh,?_,?_,hmarked,hunmarked⟩
  · intro k d j
    have h := hfloor (Sum.inl (k,d,j))
    exact ⟨h.trans (min_le_left _ _),h.trans (min_le_right _ _)⟩
  · intro k d
    exact hfloor (Sum.inr (k,d))

#print axioms terminal_finite_actual_class_physical_bank
end
end QRH.Cycle092.StrongPair
