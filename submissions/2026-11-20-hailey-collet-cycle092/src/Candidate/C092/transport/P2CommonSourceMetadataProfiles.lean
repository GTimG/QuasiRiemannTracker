/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataLate
import Candidate.C092.transport.TerminalProfileUniformCommon
import Candidate.C092.transport.TerminalProfileUniformPair
import Candidate.C092.transport.TerminalActualInverseApplyProfiles
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataProfiles_c32e9587379131e8_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open QRH.Cycle092.TerminalProfileUniform QRH.Cycle092.TerminalActualInverseApply
def ShortGates (V : ℝ→ℂ) (Bshort : ℝ) : Prop :=
    ∀ (S : Finset (ℕ×ℕ)),(0,0)∈S → ∀ C : ℝ,1≤C →
    ∀ (p : Profiles (1/4) (9/4)) (orders : Finset ℕ) (extra : Finset (ℕ×ℕ)),
    UnitGates V (-1) 2 orders extra (unitPair S C p) →
    ∀ (j : Fin 2) (opened : Bool) (Dstar D freq a ez : ℝ),
      0<Dstar → 0≤D → D≤4*Dstar → 51/100≤a → a≤1 → 0<ez → ez<1/1000 →
    let Wi := TerminalActualRow.shortProfile V ((unitPair S C p).profile j) opened Dstar D;
      Function.support Wi ⊆ Icc (1/4:ℝ) (9/4) ∧ ContDiff ℝ ∞ Wi ∧
      Function.support (twistProfile Wi 0 freq) ⊆ Iic (9/4:ℝ) ∧
      (∀ x,‖twistProfile Wi 0 freq x‖≤Bshort) ∧
      ∀ k∈orders,∀ σ∈Icc (1-a-6*ez) 2,∀ t : ℝ,
        (1+|t|)^k*‖mellin Wi ((σ:ℂ)+t*Complex.I)‖ ≤ 1

structure DescriptorBound (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M) where
  F : ℝ
  positive : 0 < F
  bound : ∀Z : ℝ,1 < Z → ∀(η η₀ : Character)
    (θ : Slot → RayQuotient.Characters M A.Hr) (w v : Slot → ℝ) (t : ℝ),
    (∀j,0 ≤ w j) → ∀(u : FreeRow) (j : Slot),
      ‖descriptor M A.Hr A.hHr η η₀ A.W Z θ w v t u j‖^2 ≤ F*Z^(w j)

noncomputable def descriptor_bound (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M) :
    DescriptorBound Slot M A := by
  exact Classical.choice (by
    obtain ⟨F,hF,hbound⟩ := original_descriptor_bound (Slot:=Slot) M A.Hr A.hHr A.W A.hW.continuous A.hWs
    exact ⟨⟨F,hF,hbound⟩⟩)

variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ) → ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}

structure LateBundle (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G : LateGeometry dmin dmax dBank) (m0 gap : ℝ) (V : ℝ → ℂ) where
  Bshort : ℝ
  Bshort_one : 1 ≤ Bshort
  shortGates : ShortGates V Bshort
  sources : LatePackets P G Bshort m0 gap
  S : Finset (ℕ×ℕ)
  S_zero : (0,0)∈S
  extra_le : P.controlsBound⊆S
  C : ℝ
  C_one : 1 ≤ C
  unitGates : ∀p : Profiles (1/4) (9/4),UnitGates V (-1) 2 sources.orders P.controlsBound (unitPair S C p)
  reconstruct : ∀(p : Profiles (1/4) (9/4)) (i : Fin 2),
    (C*sourceControl S (p.profile i)) • (unitPair S C p).profile i=p.profile i
  descriptor : ∀T : Finset Slot,DescriptorBound T M A

/-- The amplitude bound is chosen before the native short order. The finite
unit bank is then chosen after all retained orders but before every profile.
The same bound AND its genuine all-profile gate function are kept together. -/
theorem genuine_late_bundle
    (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G : LateGeometry dmin dmax dBank) (m0 gap : ℝ) (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hes : 0 ≤ εsource)
    (hbank : ∀b∈ordinaryBank,(98/100:ℝ) ≤ b.1 ∧ b.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ b.2 ∧ b.2 ≤ 51/100 ∧
      0 < dec b ∧ dec b ≤ gap ∧ 0 < nearOrdinaryQuota n b.2 b.1-dec b)
    (hnet : ∀d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
      ∃b∈ordinaryBank,b.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-b.1 < gap ∧ m ≤ b.2 ∧ b.2-m < gap)
    (hτD : G.τ*(P.degreeBound:ℝ) ≤ heightLoss) : Nonempty (LateBundle P G m0 gap V) := by
  obtain ⟨Bshort,hBshort,hshort⟩ := actual_unit_short_gates V hV
  let L := late_packets P G Bshort m0 gap (zero_le_one.trans hBshort) hes hbank hnet hτD
  obtain ⟨S,hS,hextra,C,hC,hunit⟩ := actual_pair_unit_bank V hV (1/4) (9/4) (by norm_num) (-1) 2 L.orders P.controlsBound
  exact ⟨{
    Bshort:=Bshort,Bshort_one:=hBshort,shortGates:=hshort,sources:=L,
    S:=S,S_zero:=hS,extra_le:=hextra,C:=C,C_one:=hC,
    unitGates:=fun p=>(hunit p).1,reconstruct:=fun p i=>(hunit p).2 i,
    descriptor:=fun T=>descriptor_bound T M A }⟩

namespace LateBundle
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {V : ℝ → ℂ}

def controlsBound (L : LateBundle P G m0 gap V) : Finset (ℕ×ℕ) :=
  L.S ∪ L.sources.ordinaryControls ∪ P.controlsBound

def normalizationConstant (L : LateBundle P G m0 gap V) : ℝ :=
  L.C+∑p : Finset Slot×dBank,(L.sources.ordinary p.1 p.2).C

def CslotFloor (L : LateBundle P G m0 gap V) : ℝ :=
  1+∑T : Finset Slot,(L.descriptor T).F

theorem controls_zero (L : LateBundle P G m0 gap V) : (0,0)∈L.controlsBound := by
  exact Finset.mem_union_left _ (Finset.mem_union_left _ L.S_zero)

theorem unit_controls_le (L : LateBundle P G m0 gap V) : L.S⊆L.controlsBound :=
  Finset.subset_union_left.trans Finset.subset_union_left

theorem early_controls_le (L : LateBundle P G m0 gap V) : P.controlsBound⊆L.controlsBound := Finset.subset_union_right

theorem ordinary_controls_le (L : LateBundle P G m0 gap V) (T : Finset Slot) (d : dBank) :
    (L.sources.ordinary T d).S⊆L.controlsBound :=
  (L.sources.ordinary_controls T d).trans (Finset.subset_union_right.trans Finset.subset_union_left)

theorem normalization_bounds (L : LateBundle P G m0 gap V) :
    1 ≤ L.normalizationConstant ∧ L.C ≤ L.normalizationConstant ∧
    ∀(T : Finset Slot) (d : dBank),(L.sources.ordinary T d).C ≤ L.normalizationConstant := by
  have hs : 0 ≤ ∑p : Finset Slot×dBank,(L.sources.ordinary p.1 p.2).C :=
    Finset.sum_nonneg (fun p _=>zero_le_one.trans (L.sources.ordinary p.1 p.2).C_one)
  refine ⟨by unfold normalizationConstant;linarith [L.C_one],by unfold normalizationConstant;linarith,?_⟩
  intro T d
  have h := Finset.single_le_sum (f:=fun p : Finset Slot×dBank=>(L.sources.ordinary p.1 p.2).C)
    (fun p _=>zero_le_one.trans (L.sources.ordinary p.1 p.2).C_one) (Finset.mem_univ (T,d))
  dsimp only at h
  unfold normalizationConstant
  linarith [L.C_one]

theorem CslotFloor_pos (L : LateBundle P G m0 gap V) : 0 < L.CslotFloor := by
  have hs : 0 ≤ ∑T : Finset Slot,(L.descriptor T).F := Finset.sum_nonneg (fun T _=>(L.descriptor T).positive.le)
  unfold CslotFloor
  linarith

theorem descriptor_le_floor (L : LateBundle P G m0 gap V) (T : Finset Slot) : (L.descriptor T).F ≤ L.CslotFloor := by
  have h := Finset.single_le_sum (f:=fun T : Finset Slot=>(L.descriptor T).F)
    (fun T _=>(L.descriptor T).positive.le) (Finset.mem_univ T)
  unfold CslotFloor
  linarith

theorem zero_width_paid (L : LateBundle P G m0 gap V) (T : Finset Slot)
    {U Cslot : ℝ} (hU : 1 < U) (hCslot : L.CslotFloor ≤ Cslot)
    (η η₀ : Character) (θ : T → RayQuotient.Characters M A.Hr) (w v : T → ℝ) (t : ℝ)
    (hw : ∀j,0 ≤ w j) (u : FreeRow) (j : T) (hj : w j=0) :
    ‖QRH.Cycle092.SourceInverseP6.descriptor M A.Hr A.hHr η η₀ A.W U θ w v t u j‖^2 ≤ Cslot := by
  have h := (L.descriptor T).bound U hU η η₀ θ w v t hw u j
  rw [hj,Real.rpow_zero,mul_one] at h
  exact h.trans ((L.descriptor_le_floor T).trans hCslot)

/-- The common finite control union pays arbitrary independent profiles;
no commonPair specialization is used in this algebraic comparison. -/
theorem profile_control_le (L : LateBundle P G m0 gap V) {a b : ℝ}
    (p : Profiles a b) (S : Finset (ℕ×ℕ)) (hS : S⊆L.controlsBound) :
    p.control S ≤ p.control L.controlsBound := by
  unfold Profiles.control
  exact mul_le_mul
    (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 0))
    (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem profile_cost_le (L : LateBundle P G m0 gap V) {a b : ℝ}
    (p : Profiles a b) (C : ℝ) (hC : 0 ≤ C) (hCn : C ≤ L.normalizationConstant)
    (S : Finset (ℕ×ℕ)) (hS : S⊆L.controlsBound) :
    C^4*(p.control S)^2 ≤ L.normalizationConstant^4*(p.control L.controlsBound)^2 := by
  exact mul_le_mul (pow_le_pow_left₀ hC hCn 4)
    (pow_le_pow_left₀ (p.control_nonneg S) (L.profile_control_le p S hS) 2) (by positivity) (by positivity)

theorem profile_payments (L : LateBundle P G m0 gap V) {a b : ℝ} (p : Profiles a b) :
    (p.control P.small.controls)^2 ≤ L.normalizationConstant^4*(p.control L.controlsBound)^2 ∧
    (p.control P.lowHigh.controls)^2 ≤ L.normalizationConstant^4*(p.control L.controlsBound)^2 ∧
    L.C^4*(p.control L.S)^2 ≤ L.normalizationConstant^4*(p.control L.controlsBound)^2 ∧
    ∀(T : Finset Slot) (d : dBank),
      (L.sources.ordinary T d).C^4*(p.control (L.sources.ordinary T d).S)^2 ≤
        L.normalizationConstant^4*(p.control L.controlsBound)^2 := by
  have hs := L.profile_cost_le p 1 (by norm_num) L.normalization_bounds.1 P.small.controls
    ((P.controls_bounds.2.1).trans L.early_controls_le)
  have hl := L.profile_cost_le p 1 (by norm_num) L.normalization_bounds.1 P.lowHigh.controls
    ((P.controls_bounds.2.2.1).trans L.early_controls_le)
  refine ⟨by simpa only [one_pow,one_mul] using hs,by simpa only [one_pow,one_mul] using hl,
    L.profile_cost_le p L.C (zero_le_one.trans L.C_one) L.normalization_bounds.2.1 L.S L.unit_controls_le,?_⟩
  intro T d
  exact L.profile_cost_le p (L.sources.ordinary T d).C (zero_le_one.trans (L.sources.ordinary T d).C_one)
    (L.normalization_bounds.2.2 T d) (L.sources.ordinary T d).S (L.ordinary_controls_le T d)

/-- Every normalization bank and both direct profile controls are paid by
one fixed Fourier weight before the live pair selector and Fourier variables. -/
theorem common_pair_payments (L : LateBundle P G m0 gap V) :
    ∃J : ℕ,∃K : ℝ,0 < K ∧
    ∀e : Fin 2×Fin 2,∀tau : ℝ×ℝ,
      ((QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau).control P.small.controls)^2 ≤
        K*QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.pairWeight J tau ∧
      ((QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau).control P.lowHigh.controls)^2 ≤
        K*QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.pairWeight J tau ∧
      L.C^4*((QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau).control L.S)^2 ≤
        K*QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.pairWeight J tau ∧
      ∀(T : Finset Slot) (d : dBank),
        (L.sources.ordinary T d).C^4*
          ((QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau).control (L.sources.ordinary T d).S)^2 ≤
        K*QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.pairWeight J tau := by
  obtain ⟨J,K,hK,hpay⟩ := common_pair_payment L.controlsBound (C:=L.normalizationConstant)
    (zero_lt_one.trans_le L.normalization_bounds.1)
  refine ⟨J,K,hK,?_⟩
  intro e tau
  let p := QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.commonPair e tau
  have hctrl (S : Finset (ℕ×ℕ)) (hS : S⊆L.controlsBound) : p.control S ≤ p.control L.controlsBound := by
    unfold Profiles.control
    exact mul_le_mul
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 0))
      (CenteredMomentEnergyReferenceProfileBudget.control_mono hS (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hcost (C : ℝ) (hC : 0 ≤ C) (hCn : C ≤ L.normalizationConstant)
      (S : Finset (ℕ×ℕ)) (hS : S⊆L.controlsBound) :
      C^4*(p.control S)^2 ≤ K*QRH.SilDensitySplit.CubeFree.Packet.ProfileSeparation.pairWeight J tau := by
    apply (mul_le_mul (pow_le_pow_left₀ hC hCn 4)
      (pow_le_pow_left₀ (p.control_nonneg S) (hctrl S hS) 2) (by positivity) (by positivity)).trans
    exact hpay e tau
  have hs := hcost 1 (by norm_num) L.normalization_bounds.1 P.small.controls
    ((P.controls_bounds.2.1).trans L.early_controls_le)
  have hl := hcost 1 (by norm_num) L.normalization_bounds.1 P.lowHigh.controls
    ((P.controls_bounds.2.2.1).trans L.early_controls_le)
  refine ⟨by simpa only [one_pow,one_mul] using hs,by simpa only [one_pow,one_mul] using hl,
    hcost L.C (zero_le_one.trans L.C_one) L.normalization_bounds.2.1 L.S L.unit_controls_le,?_⟩
  intro T d
  exact hcost (L.sources.ordinary T d).C (zero_le_one.trans (L.sources.ordinary T d).C_one)
    (L.normalization_bounds.2.2 T d) (L.sources.ordinary T d).S (L.ordinary_controls_le T d)

end LateBundle

#print axioms genuine_late_bundle
#print axioms LateBundle.zero_width_paid
#print axioms LateBundle.profile_payments
#print axioms LateBundle.common_pair_payments
end
end QRH.Cycle092.P2CommonSourceMetadata
