/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual event-free P6 suppliers on a finite bank of checked length/response
labels. Scalar fees, the common genuine rectangle bank and all physical
source meshes precede Slot, arithmetic data and live rows. -/
import Candidate.C092.transport.TerminalActualInverseApplyBounded
import Candidate.C092.transport.TerminalActualInverseApplyUnmarkedBounded
import Candidate.C092.transport.StrongPairRegularTerminalBanks

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
local instance c092LocalInst_Candidate_C092_transport_TerminalActualInverseApplyFiniteBank_584d628eef68a02a_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def TerminalActualClassMarkedSupplier (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ) : Prop :=
    ∀ (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (ρ : Contract.AnchorRect) (hsource : Contract.UniformInverseRectSource Contract.canonicalFamily ρ)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    {N quota : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota) (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (price : ℝ) (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4),
    ∃ inverseMesh nativeMesh : ℝ,0 < inverseMesh ∧ 0 < nativeMesh ∧
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

def TerminalActualClassUnmarkedSupplier (n yCell e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ) : Prop :=
    ∀ (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (εm nativeError : ℝ) (hεm : 0 < εm) (hnativeError : 0 < nativeError)
    {N quota : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota) (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (price : ℝ) (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4),
    ∃ nativeMesh : ℝ,0 < nativeMesh ∧
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

/-- These are actual analytic suppliers, obtained by invoking both checked
P6 constructions. The common bank uses their literal returned fees, so no
rho/fee quantifiers or Slot/mesh quantifiers are interchanged. -/
theorem terminal_finite_actual_class_inverse_bank {Key : Type} [Fintype Key]
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (n y el ν : Key→ℝ) (cut : Key→Cutoff) (bcell : Key→ℚ)
    (hy0 : ∀ k,(369/1000:ℝ) ≤ y k) (hy1 : ∀ k,y k ≤ sourceY)
    (hn : ∀ k,n k ≤ sourceRatio*y k) (he : ∀ k,0 ≤ el k)
    (hν0 : ∀ k,el k ≤ ν k) (hν1 : ∀ k,ν k ≤ 3/4)
    (hg : ∀ k,CutoffGuard (bcell k) (cut k))
    (hp : ∀ k,PaidWithBand (y k) (el k) (ν k) (cut k))
    {loss : ℝ} (hloss : 0 < loss) (heightLoss : ℝ) (hheightLoss : 0 ≤ heightLoss) :
    ∃ feeM feeU commonFee : Key→ℝ,
      (∀ k,0 < feeM k ∧ 0 < feeU k ∧ 0 < commonFee k ∧
        commonFee k ≤ feeM k ∧ commonFee k ≤ feeU k) ∧
      (∀ k,TerminalActualClassMarkedSupplier (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeM k)) ∧
      (∀ k,TerminalActualClassUnmarkedSupplier (n k) (y k) (el k) (ν k) loss heightLoss (cut k) (loss/10) (loss/10) (feeU k)) ∧
    ∃ ζ : ℝ,0 < ζ ∧ (∀ k,ζ ≤ commonFee k/2) ∧
    ∃ δ : ℝ,0 < δ ∧ δ ≤ 1/1000 ∧ 3*δ ≤ ζ ∧
    ∃ J : ℕ,∃ bank : Fin J → Contract.AnchorRect,
      (∀ j,Contract.UniformInverseRectSource Contract.canonicalFamily (bank j)) ∧
      ∀ r : ℝ,367/500 ≤ r → r ≤ 1 →
        inverseQuota r ≤ ζ ∨ (0 ≤ inverseQuota r-ζ → ∃ j,(bank j).Admissible r (inverseQuota r-ζ) 1) := by
  have hM (k : Key) := actual_class_marked_bounded (cut k) (hy0 k) (hy1 k) (hn k)
    (he k) (hν0 k) (hν1 k) (hg k) (hp k) hloss heightLoss hheightLoss
  have hU (k : Key) := actual_class_unmarked_bounded (cut k) (hy0 k) (hy1 k) (hn k)
    (he k) (hν0 k) (hν1 k) (hg k) (hp k) hloss heightLoss hheightLoss
  choose sm dm fm hsm hdm hfm hsem hdem hwm hM using hM
  choose su du fu hsu hdu hfu hseu hdeu hwu hU using hU
  let fc : Key→ℝ := fun k=>min (fm k) (fu k)
  have hfc (k : Key) : 0 < fc k := lt_min (hfm k) (hfu k)
  obtain ⟨ζ,hζ,hζf,δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover⟩ := terminal_uniform_genuine_inverse_bank hβ fc hfc
  refine ⟨fm,fu,fc,fun k=>⟨hfm k,hfu k,hfc k,min_le_left _ _,min_le_right _ _⟩,?_,?_,
    ζ,hζ,hζf,δ,hδ,hδsmall,hδζ,J,bank,hsource,hcover⟩
  · intro k
    simpa only [TerminalActualClassMarkedSupplier,hsem k,hdem k] using hM k
  · intro k
    simpa only [TerminalActualClassUnmarkedSupplier,hseu k,hdeu k] using hU k

#print axioms terminal_finite_actual_class_inverse_bank
end
end QRH.Cycle092.StrongPair
