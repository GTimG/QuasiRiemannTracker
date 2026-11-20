/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataLate
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataEvents_354988f655a9f229_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def SmallAt (Slot : Type) [Fintype Slot] [DecidableEq Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y mesh : ℝ) (P : SmallPacket Slot M A n y mesh) (U : ℝ) : Prop :=
    1 < U ∧
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
        P.C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control P.controls)^2*
          (1+|t₁|+|t₂|+height)^P.degree*
          U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))

def LowHighAt (Slot : Type) [Fintype Slot] [DecidableEq Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y e Vmax mesh buffer : ℝ) (P : LowHighPacket Slot M A n y e Vmax mesh buffer) (Cslot C U : ℝ) : Prop :=
    ∀ V : ℝ,(98/100:ℝ) ≤ V → V ≤ Vmax →
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
      C*QuadraticInitialBound.diagonalControl radialMajorant*(p.control P.controls)^2*
        (1+|t₁|+|t₂|+height)^P.degree*U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V))

def CoverAt (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (buffer Cslot U : ℝ) : Prop :=
    ∀(η η₀ : Character) (θ : Slot → RayQuotient.Characters M A.Hr) (w v : Slot → ℝ)
      (t : ℝ) (rows : Finset FreeRow),(∀j,0 ≤ w j) →
      (∀u∈rows,0 < measured M A.Hr A.hHr η η₀ A.W U (Cslot*U^buffer) θ w v t u) →
      ∀u∈rows,∃j,u∈descriptorRows M A.Hr A.hHr rows η η₀ A.W U (Cslot*U^buffer) (buffer/2) θ w v t j

variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ) → ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}

structure AtAll (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G : LateGeometry dmin dmax dBank) (Bshort m0 gap : ℝ) (L : LatePackets P G Bshort m0 gap)
    (I : ℕ) (Cslot CLo U : ℝ) : Prop where
  one : 1 < U
  small : SmallAt Slot M A n y smallMesh P.small U
  lowHigh : LowHighAt Slot M A n y e Vmax lowMesh buffer P.lowHigh Cslot CLo U
  ordinary : ∀(T : Finset Slot) (d : dBank),
    OrdinaryAt Slot M A n y dmin dmax εsource ordinaryMesh ordinaryBank dec P.ordinary T dBank G d m0 gap
      (L.ordinary T d).order (L.ordinary T d).C4 (L.ordinary T d).S (L.ordinary T d).C I U
  marked : ∀(T : Finset Slot) (d : dBank) (k : WindowKey table) (j : Fin B.J),
    MarkedAt T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeM k) (B.rhoBank j) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.im k d j) (B.nm k d j) buffer
      (P.inverse.marked T d k j) dBank G d Bshort (L.marked T d k j).order (L.marked T d k j).Cy I Cslot U
  unmarked : ∀(T : Finset Slot) (d : dBank) (k : WindowKey table),
    UnmarkedAt T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeU k) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.nu k d) buffer
      (P.inverse.unmarked T d k) dBank G d Bshort (L.unmarked T d k).order (L.unmarked T d k).Cy I Cslot U

  cover : ∀T : Finset Slot,CoverAt T M A buffer Cslot U

/-- One true event is chosen after the late payment constant and before
ALL live profiles, cofactor radii, original sparse rows and source classes.
Every field is the genuine corresponding source function at those rows. -/
theorem common_source_event
    (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G : LateGeometry dmin dmax dBank) (Bshort m0 gap : ℝ) (L : LatePackets P G Bshort m0 gap)
    (hbuffer : 0 < buffer) (I : ℕ) (Cslot : ℝ) (hCslot : 0 < Cslot) :
    ∃CLo : ℝ,0 < CLo ∧ ∀ᶠ U : ℝ in atTop,AtAll P G Bshort m0 gap L I Cslot CLo U := by
  obtain ⟨CLo,hCLo,hlo⟩ := P.lowHigh.late Cslot hCslot
  have hs : ∀ᶠ U : ℝ in atTop,SmallAt Slot M A n y smallMesh P.small U := P.small.late
  have hl : ∀ᶠ U : ℝ in atTop,LowHighAt Slot M A n y e Vmax lowMesh buffer P.lowHigh Cslot CLo U := hlo
  have ho := Filter.eventually_all.mpr (fun T : Finset Slot =>
    Filter.eventually_all.mpr (fun d : dBank => (L.ordinary T d).event I))
  have hm := Filter.eventually_all.mpr (fun T : Finset Slot =>
    Filter.eventually_all.mpr (fun d : dBank => Filter.eventually_all.mpr (fun k : WindowKey table =>
      Filter.eventually_all.mpr (fun j : Fin B.J => (L.marked T d k j).event I Cslot hCslot))))
  have hu := Filter.eventually_all.mpr (fun T : Finset Slot =>
    Filter.eventually_all.mpr (fun d : dBank => Filter.eventually_all.mpr (fun k : WindowKey table =>
      (L.unmarked T d k).event I Cslot hCslot)))
  have hc : ∀ᶠ U : ℝ in atTop,∀T : Finset Slot,CoverAt T M A buffer Cslot U :=
    Filter.eventually_all.mpr (fun T : Finset Slot =>
      (actual_calibrated_descriptor_cover (Slot:=T) M A.Hr A.hHr A.W A.hW.continuous A.hWs hbuffer hCslot).mono
        (fun _ h=>h.2))
  refine ⟨CLo,hCLo,?_⟩
  filter_upwards [hs,hl,ho,hm,hu,hc,eventually_gt_atTop (1:ℝ)] with U hs hl ho hm hu hc hU
  exact ⟨hU,hs,hl,ho,hm,hu,hc⟩

#print axioms common_source_event
end
end QRH.Cycle092.P2CommonSourceMetadata
