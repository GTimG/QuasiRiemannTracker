/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider, diagonal half: `UniformDiagAt`, the artificial divisor cap, one side of `rootChoice` and `diag_supply`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderDiag7
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteDiagAssemblyT
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderFinal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceMass
open CenteredMomentActiveSource CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectorLocalization CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFirstSectors CenteredMomentFirstSectorTransform CenteredMomentFirstMixedAllowance
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedFirstCommonSum MixedFirstPaidRetained
open MixedInnerExceptionalBlock MixedFirstExceptionalWindow
open RepairedRawContext RepairedSourceSideSupply
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open scoped ContDiff
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentSecondWindowBudget
open MixedFirstPhysicalApplication MixedFirstPhysicalBudget MixedFirstRetainedFixed
open MixedFirstExceptionalNormalization RepairedFirstRawSides RepairedFirstRawScalar RepairedFirstRawBlock
open Qrh.MarkedAnchor.Ordinary.RootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstScale EisensteinSchwartzPoisson
open CenteredMomentCompleteCommon CenteredMomentFirstCanonicalFamily
open QRH.Record1252270103KernelMass
open MixedPrincipalBudget MixedPrincipalCentered MixedCommonCoefficient
open MixedInnerExceptionalLedger MixedFirstAllocatedRemainders MixedFirstProfileEnvelope
open QRH.SilDensitySplit.CubeFree.Second.ConcreteDiagAssembly
open QRH.SilDensitySplit.CubeFree.Second.Provider Qrh.MarkedAnchor.Ordinary.Second.Provider
open MixedPrincipalPoolCaps MixedActualRetained
open ActualEisensteinCubic CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalDyadicAssembly MixedFirstRetainedFixed MixedFirstCommonSum

local instance (priority := 2000) instDecEqSubtypeProvDiag8 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {ι : Type u} [Fintype ι] {a b : ℝ}

open CenteredMomentGaussEnergy CenteredMomentSourceRow CenteredMomentHeckeColumnWindow
open CenteredMomentFirstAmplificationChoice CenteredMomentSmoothedWindowEnergy
open CenteredMomentFirstPhysicalSource CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentChildRows CenteredMomentFirstColumns
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentSecondLocalization CenteredMomentSupportedTailAggregate
open CenteredMomentSourceSecondZeroEnergy EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedPrincipalBudget
open MixedCommonCoefficient MixedCommonRestriction MixedOriginalSecondZero MixedFirstLiveSource
open MixedOriginalTail MixedOriginalNormCap MixedOriginalTailPower MixedPoissonLocalization
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedLocalizedDictionary
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete

/-- The conclusion of `diag_avg_uniformT` at one `Z`. -/
def UniformDiagAt (N : ℕ) (α Bcap a b ε δ Bnorm Lrad Cr εsum Btl ξr saving : ℝ)
    (ha : 0<a) (hb : 0≤b) (J : ℕ) (control : Finset (ℕ×ℕ)) (Ckernel : ℝ) (Q : Id)
    (A Csum C0 Ct : ℝ) (controlT : Finset (ℕ×ℕ)) (Z : ℝ) : Prop :=
      ∀(ι : Type) [Fintype ι],∀s : Source ι a b,∀cover : OriginalEnclosure s,∀G : Id,
      ∀JB : (B : actualAllocations (tuplePools s) G) → Finset (liveIndices B.val),
      ∀(Us : Finset Id)(τ : Character)(χ₀ : RayCharacter)(m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∀(K Lref : ℝ)(T W M Y : actualAllocations (tuplePools s) G → ℝ),
      0<K → 0<Lref → Lref≤s.L → K≤Z^Btl →
      (∀B, 0≤T B ∧ frequencyRadius (T B) Z ξr≤Cr*Z^Lrad ∧ T B≤Z^Btl) →
      (∀B, 0<W B ∧ W B≤Z^Btl ∧ (W B)⁻¹≤Z^Btl ∧ 0≤M B ∧ 1≤Y B ∧ Y B≤Z^Btl) →
      (∀B, Fintype.card (Rest (JB B))≤N ∧
        ((restOf s hb cover G B (JB B)).Fhole.absNorm:ℝ)≤Z^Bcap ∧
        (∏i,2*(restOf s hb cover G B (JB B)).P i)≤Z^Bcap ∧
        poolCap (restOf s hb cover G B (JB B))≤Z^Bnorm ∧
        poolCap (restOf s hb cover G B (JB B))≤Z^Btl ∧
        sourceNormCap (restOf s hb cover G B (JB B)).P b (restOf s hb cover G B (JB B)).T
          (restOf s hb cover G B (JB B)).d≤Z^Bnorm ∧
        sourceNormCap (restOf s hb cover G B (JB B)).P b (restOf s hb cover G B (JB B)).T
          (restOf s hb cover G B (JB B)).d≤Y B ∧
        (Y B)^2/(16*K*W B^4)≤T B ∧
        ∀ξ : RayCharacter, familyConductorBudget (restOf s hb cover G B (JB B))
          (childCharacter τ ξ) (frequencyRadius (T B) Z ξr)≤Z^Bcap) →
      ∀v : ℝ,
      outerAvg s hb cover G JB τ v M (diagAvgT s ha hb cover G JB Us τ χ₀ Q m v K T Z ξr W)≤
        (((Finset.univ : Finset (actualAllocations (tuplePools s) G)).card : ℝ) *
          ∑ B : actualAllocations (tuplePools s) G, ‖allocWeight s G B‖^2 *
            (AtotP (allocatedLiveSource s hb cover G B) (JB B) * ((2:ℝ)^(Fintype.card (JB B)) * M B) *
              ((Fintype.card RayCharacter : ℝ) * (Fintype.card RayCharacter : ℝ) *
                xiB s hb cover G JB Us K Lref W Y J control controlT Q Z ε α Bnorm δ εsum saving
                  C0 Ckernel A Csum Ct B)))*
          (1+‖v‖)^(2*J)

theorem diag_avg_uniformT' (N : ℕ)
    (α Bcap a b ε δ Bnorm Lrad Cr εsum Btl ξr saving : ℝ)
    (hα0 : 0≤α) (hα23 : α<2/3) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1)
    (hBnorm : 0≤Bnorm) (hLrad : 0≤Lrad) (hCr : 0<Cr) (hεsum : 0<εsum)
    (hBtl : 0≤Btl) (hξr : 0<ξr) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),∃Ckernel : ℝ,0≤Ckernel ∧
      ∀Q : Id,Q≠0 → Q≠⊤ → Q≤Ideal.span {(72:O)} →
      ∃A Csum C0 Ct : ℝ,∃controlT : Finset (ℕ×ℕ),0<A ∧ 0<Csum ∧ 0<C0 ∧ 0<Ct ∧
      ∀ᶠZ : ℝ in atTop,1<Z ∧ UniformDiagAt N α Bcap a b ε δ Bnorm Lrad Cr εsum Btl ξr saving ha hb
        J control Ckernel Q A Csum C0 Ct controlT Z :=
  diag_avg_uniformT.{0} N α Bcap a b ε δ Bnorm Lrad Cr εsum Btl ξr saving hα0 hα23 hBcap ha hb hε
    hδ hgap hBnorm hLrad hCr hεsum hBtl hξr

/-- The artificial divisors have norm at most the pool cap. -/
theorem artificial_norm_le {ι : Type*} [Fintype ι] {a b : ℝ} (s : Source ι a b) (hb : 0 ≤ b)
    (C D : Id) (hD : D ≠ 0) :
    ∀ u ∈ concreteArtificial s C D hD, (u.absNorm:ℝ) ≤ poolCap s := by
  intro u hu
  have hu1 := (Finset.mem_filter.mp hu).1
  unfold MixedFirstPhysicalApplication.artificialDivisors
    CenteredMomentMobiusRegroup.divisorPool at hu1
  obtain ⟨J, -, hJ⟩ := Finset.mem_biUnion.mp hu1
  simp only [IdealMobiusDivisorSum.idealDivisors, Finset.mem_filter, Set.Finite.mem_toFinset,
    Set.mem_ofPred_eq] at hJ
  have hle := hJ.1
  rw [element_span] at hle
  have hJmem := (Finset.mem_filter.mp J.property).1
  rw [CenteredMomentFirstSectors.mem_residualPool] at hJmem
  have hcol : D*J.val ∈ sourceColumns s := (Finset.mem_filter.mp hJmem).1
  have h1 := MixedPrincipalPoolCaps.source_column_pool_norm s hb _ hcol
  have hD1 : 1 ≤ Ideal.absNorm D := Nat.one_le_iff_ne_zero.mpr
    (fun h => hD (Ideal.absNorm_eq_zero_iff.mp h))
  have h2 : Ideal.absNorm J.val ≤ Ideal.absNorm (D*J.val) := by
    rw [map_mul]; exact Nat.le_mul_of_pos_left _ hD1
  calc (u.absNorm:ℝ) ≤ (Ideal.absNorm J.val : ℝ) := by exact_mod_cast hle
    _ ≤ (Ideal.absNorm (D*J.val) : ℝ) := by exact_mod_cast h2
    _ ≤ poolCap s := h1


/-- The fixed constant of the family conductor cap. -/
def cfam : ℝ := 4*cfix*(Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
  (Ideal.span {(72:O)}).absNorm*(Ideal.span {(12:O)}).absNorm

theorem rpow_nat_eq (Z : ℝ) (k : ℕ) : Z^(k:ℝ) = Z^k := Real.rpow_natCast Z k

set_option maxHeartbeats 3200000 in
/-- **One side of the diagonal half of `rootChoice`** at a fixed `Z`: the uniform diagonal bound
(`UniformDiagAt`, with every structural cap discharged from the root) and the budget
(`diag_side_budget`). -/
theorem diag_side_at {D : StepData} {G : StepGates D} {κ : Type} [Fintype κ]
    {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {Wsl : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    (d : RootInput G M H hH κ Wsl N Holes ε Z Kslot η η₀) (hε : 0 < ε)
    (Nm : ℕ) (hNm : Fintype.card κ ≤ Nm) (hK1 : 1 ≤ Kslot)
    (ms : ℝ) (hm0 : 0 < ms) (hmesh : ∀ i, d.w i ≤ ms) (hms : ms ≤ mesh G ε)
    (C Dl : Id) (hC : Supported C) (hD : Supported Dl)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport Dl)
    (hcpC : commonPart C Dl = C) (hcpD : commonPart Dl C = Dl)
    (hNC : (C.absNorm:ℝ) ≤ Z^(8:ℝ)) (hND : (Dl.absNorm:ℝ) ≤ Z^(8:ℝ))
    (hDC : (Dl.absNorm:ℝ) ≤ (C.absNorm:ℝ)^3)
    (E : Finset (CommonIndex C Dl)) (τ : Character)
    (hmod : τ.modulus = η.modulus*Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}*
      Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C Dl => P.val) E*activeConductor C Dl})
    (n : ℤ) (hn : Retained (frequencyRadius (firstNominalScale C Dl (∏ P ∈ E, P.val) d.Kroot
      (sourceVolume d.root)) Z (cutoffLoss G N ε)) n)
    (hKlo : 1/2 ≤ childScale Z (cutoffLoss G N ε) n)
    (hKhi : childScale Z (cutoffLoss G N ε) n ≤ Z^(33:ℝ))
    (Us : Finset Id) (hUs : ∀ u ∈ Us, Squarefree u) (hUX : ∀ u ∈ Us, (Ideal.absNorm u : ℝ) ≤ Z^(8:ℝ))
    (Mc : ℝ) (hMc0 : 0 ≤ Mc) (hMc : Mc ≤ 1*Z^(ε/4))
    (Q : Id) (JL : ℕ) (cL controlT : Finset (ℕ×ℕ))
    (εL δ εsum saving C0 Ckernel A Csum Ct : ℝ) (hεL : 0 ≤ εL) (hC0 : 0 ≤ C0)
    (hCk : 0 ≤ Ckernel) (hA : 0 ≤ A) (hCsum : 0 ≤ Csum) (hCt : 0 ≤ Ct)
    (hU : UniformDiagAt Nm (alphaP G ε) 80 (1/4) (9/4) εL δ 8 17 1 εsum 40 ms saving
      (by norm_num) (by norm_num) JL cL Ckernel Q A Csum C0 Ct controlT Z)
    (Cc eC : ℝ) (hCc : 0 ≤ Cc)
    (hcard : ((Finset.univ : Finset (actualAllocations (tuplePools d.root) C)).card : ℝ)^2 ≤ Cc*Z^eC)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Cside : ℝ) (hCs : 0 < Cside) (hJL : 2*JL ≤ J)
    (hcL : cL ⊆ control) (h00 : (0,0) ∈ control)
    (θ0 θf θt : ℝ) (hθ0 : 0 ≤ θ0) (hθt : 0 ≤ θt)
    (hAf : kF Cc 1 8 Kslot Ckernel A Csum Nm JL Q*(Real.log Z + 1)*
      Z^(eC+ε/4+2*8*δ+εsum+2*εL+5*cutoffLoss G N ε/4) ≤ θf*Cside*Z^(3*ε))
    (hA0 : k0 Cc 1 8 Kslot C0 εL Nm*(Real.log Z + 1)*
      Z^(eC+ε/4+εL+3*cutoffLoss G N ε/2) ≤ θ0*Cside*Z^(3*ε))
    (hAt : kT Cc 1 Kslot Ct controlT Nm*(Real.log Z + 1)*Z^(eC+ε/4+8+2-saving) ≤
      θt*Cside*Z^(3*ε-20))
    (hZa : (2:ℝ)^Nm ≤ Z) (hZb : (81/16:ℝ)*(2:ℝ)^Nm ≤ Z^(7:ℝ)) (hZc : cfam ≤ Z) :
    ∃ X : ℝ, (∀ v : ℝ, outerAvg d.root (by norm_num) d.cover C (selOf d hε ms hm0.le hmesh C) τ v
        (fun _ => Mc)
        (diagAvgT d.root (by norm_num) (by norm_num) d.cover C (selOf d hε ms hm0.le hmesh C) Us τ 1 Q
          CenteredMomentSecondHeightFamily.fixedBadMask v (childScale Z (cutoffLoss G N ε) n)
          (fun B => Tfreq d C B (selOf d hε ms hm0.le hmesh C B)
            (16 * childScale Z (cutoffLoss G N ε) n *
              (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
                (selOf d hε ms hm0.le hmesh C B))^4)) Z ms
          (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
            (selOf d hε ms hm0.le hmesh C B))) ≤ X*(1+‖v‖)^(2*JL)) ∧
      X ≤ (θ0+θf+θt)*balancedBudget d.root τ C Dl (amplitude d.root d.t₀ d.V J control Cside) Z (3*ε) := by
  have hZ1 := d.one_lt_Z
  have hz : 0 < Z := zero_lt_one.trans hZ1
  have hZ5 := d.hZ
  set κc := cutoffLoss G N ε with hκc
  set K := childScale Z κc n with hKdef
  set JB := selOf d hε ms hm0.le hmesh C with hJB
  have hK0 : 0 < K := by linarith
  have hgates := root_width_gates d hε
  have hVZ := RepairedRootCaps.root_volume_cap M H hH d
  have hV0 := sourceVolume_pos d.root
  have h2N : (2:ℝ)^(Fintype.card κ) ≤ (2:ℝ)^Nm := pow_le_pow_right₀ (by norm_num) hNm
  have h2N0 : (0:ℝ) ≤ (2:ℝ)^Nm := by positivity
  -- powers as natural powers
  have e7 := rpow_nat_eq Z 7
  have e8 := rpow_nat_eq Z 8
  have e16 := rpow_nat_eq Z 16
  have e17 := rpow_nat_eq Z 17
  have e33 := rpow_nat_eq Z 33
  have e40 := rpow_nat_eq Z 40
  have e80 := rpow_nat_eq Z 80
  push_cast at e7 e8 e16 e17 e33 e40 e80
  have hZ1' : (1:ℝ) ≤ Z := hZ1.le
  have hmon : ∀ a b : ℕ, a ≤ b → Z^a ≤ Z^b := fun a b h => pow_le_pow_right₀ hZ1' h
  -- the widths
  set q := (81/16:ℝ)*(2:ℝ)^Nm*Z with hq
  have hq8 : q ≤ Z^8 := by
    rw [hq, show Z^8 = Z^7*Z by ring]; rw [e7] at hZb
    exact mul_le_mul_of_nonneg_right hZb hz.le
  have hq1 : 1 ≤ q := by
    rw [hq]; have : (1:ℝ) ≤ (2:ℝ)^Nm := one_le_pow₀ (by norm_num); nlinarith
  have hcapq : ∀ B : actualAllocations (tuplePools d.root) C,
      sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
        (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d ≤ q := by
    intro B
    refine (rest_normCap_le d.root (by norm_num) d.cover C B (JB B)).trans
      ((live_normCap_le d.root (by norm_num) d.cover C B).trans ?_)
    rw [hq, show (9/4:ℝ)^2 = 81/16 by norm_num]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2N (by norm_num)) hVZ hV0.le (by positivity)
  have hW1 : ∀ B : actualAllocations (tuplePools d.root) C,
      1 ≤ slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B) := by
    intro B; unfold slotWidth
    exact Finset.one_le_prod₀ (fun j _ => by
      have := (allocatedLiveSource d.root (by norm_num) d.cover C B).hP j.val; linarith)
  have hWZ : ∀ B : actualAllocations (tuplePools d.root) C,
      slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B) ≤ Z^2 := by
    intro B
    refine (selOf_width d hε ms hm0.le hmesh hms C B Nm hNm).trans ?_
    have hu : Z^(uMax G ε (∑ i, d.w i)) ≤ Z := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith [hgates.1] : uMax G ε (∑ i, d.w i) ≤ 1)
    rw [sq]; exact mul_le_mul hZa hu (Real.rpow_nonneg hz.le _) hz.le
  have hms2 : ms/2 ≤ 1 := by
    have := (mesh_spec G ε hε).2.1; have := (rootReserve_spec G).2.2.2; linarith
  refine ⟨_, fun v => hU κ d.root d.cover C JB Us τ 1 CenteredMomentSecondHeightFamily.fixedBadMask
    CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
    K ((2/9)*Z^d.ell)
    (fun B => Tfreq d C B (JB B) (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4))
    (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B)) (fun _ => Mc)
    (fun B => max 1 (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
      (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d))
    hK0 (by positivity) d.hminimum ?_ ?_ ?_ ?_ v, ?_⟩
  · rw [e40]; rw [e33] at hKhi; exact hKhi.trans (hmon 33 40 (by norm_num))
  · intro B
    have hW := hW1 B
    have hc0 := normCap_nonneg (restOf d.root (by norm_num) d.cover C B (JB B))
    set Y := max 1 (capRes d C B (JB B)) with hY
    have hY8 : Y ≤ Z^8 := max_le (by linarith) ((hcapq B).trans hq8)
    have hY1 : 1 ≤ Y := le_max_left _ _
    have hden : 1 ≤ 16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4 := by
      have : 1 ≤ (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4 := one_le_pow₀ hW
      nlinarith
    have hT0 : 0 ≤ Tfreq d C B (JB B) (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4) := by
      unfold Tfreq; exact div_nonneg (sq_nonneg _) (by linarith)
    have hT : Tfreq d C B (JB B) (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4) ≤ Z^16 := by
      unfold Tfreq
      rw [← hY]
      calc Y^2 / _ ≤ Y^2 := div_le_self (sq_nonneg _) hden
        _ ≤ (Z^8)^2 := pow_le_pow_left₀ (by linarith) hY8 2
        _ = Z^16 := by ring
    refine ⟨hT0, ?_, ?_⟩
    · unfold frequencyRadius
      have hzm : Z^(ms/2) ≤ Z := by
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1.le hms2
      rw [e17, one_mul, show Z^17 = Z^16*Z by ring]
      exact mul_le_mul hT hzm (Real.rpow_nonneg hz.le _) (by positivity)
    · rw [e40]; exact hT.trans (hmon 16 40 (by norm_num))
  · intro B
    have hc0 := normCap_nonneg (restOf d.root (by norm_num) d.cover C B (JB B))
    refine ⟨slotWidth_pos _ _, ?_, ?_, hMc0, le_max_left _ _, ?_⟩
    · rw [e40]; exact (hWZ B).trans (hmon 2 40 (by norm_num))
    · rw [e40]
      exact (inv_le_one_of_one_le₀ (hW1 B)).trans (one_le_pow₀ hZ1')
    · rw [e40]; exact (max_le (by linarith) ((hcapq B).trans hq8)).trans (hmon 8 40 (by norm_num))
  · intro B
    have hc0 := normCap_nonneg (restOf d.root (by norm_num) d.cover C B (JB B))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, le_max_right _ _, le_of_eq rfl, ?_⟩
    · refine (Fintype.card_subtype_le _).trans ?_
      rw [Fintype.card_coe]
      exact (Finset.card_le_univ _).trans hNm
    · show ((d.root.Fhole).absNorm : ℝ) ≤ Z^(80:ℝ)
      rw [d.hF, map_one, Nat.cast_one]
      exact Real.one_le_rpow hZ1' (by norm_num)
    · have hp := prod_comp_le (fun k : Rest (JB B) => k.val.val)
        (Subtype.val_injective.comp Subtype.val_injective) (fun i => 2 * d.root.P i)
        (fun i => by linarith [d.root.hP i])
      refine hp.trans ?_
      show (∏ i, 2 * d.root.P i) ≤ Z^(80:ℝ)
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, e80]
      have hP := root_prodP d
      rw [Real.rpow_one] at hP
      calc (2:ℝ)^(Fintype.card κ) * ∏ i, d.root.P i ≤ Z * Z :=
            mul_le_mul (h2N.trans hZa) hP
              (Finset.prod_nonneg (fun i _ => by linarith [d.root.hP i])) hz.le
        _ = Z^2 := by ring
        _ ≤ Z^80 := hmon 2 80 (by norm_num)
    · exact (restOf_pool_le d.root (by norm_num) d.cover C B (JB B)).trans d.hpool
    · rw [e40]
      exact ((restOf_pool_le d.root (by norm_num) d.cover C B (JB B)).trans d.hpool).trans
        (by rw [e8]; exact hmon 8 40 (by norm_num))
    · rw [e8]; exact (hcapq B).trans hq8
    · intro ξ
      have hτn := tau_norm_le C Dl hC.1 E τ η hmod
      have hσ : ((childCharacter τ ξ).modulus.absNorm:ℝ) ≤
          (τ.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
        exact_mod_cast CenteredMomentSecondRadicalBudget.child_modulus_bound τ ξ
      have hη := d.hη
      have hX1 : ((childCharacter τ ξ).modulus.absNorm:ℝ) ≤
          (Z*(Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
            (Ideal.span {(72:O)}).absNorm*(Z^8*Z^8))*(Ideal.span {(12:O)}).absNorm := by
        refine hσ.trans (mul_le_mul_of_nonneg_right (hτn.trans ?_) (Nat.cast_nonneg _))
        rw [e8] at hNC
        have hc0 : (0:ℝ) ≤ (C.absNorm:ℝ) := Nat.cast_nonneg _
        gcongr
      have hR : ((restOf d.root (by norm_num) d.cover C B (JB B)).R.absNorm:ℝ) ≤ Z^(8:ℝ) := by
        show ((d.root.R * C).absNorm:ℝ) ≤ Z^(8:ℝ)
        rw [d.hR, one_mul]; exact hNC
      have hpool := (restOf_pool_le d.root (by norm_num) d.cover C B (JB B)).trans d.hpool
      set Y := max 1 (sourceNormCap (restOf d.root (by norm_num) d.cover C B (JB B)).P (9/4)
        (restOf d.root (by norm_num) d.cover C B (JB B)).T (restOf d.root (by norm_num) d.cover C B (JB B)).d) with hY
      have hY8 : Y ≤ Z^8 := max_le (by linarith) ((hcapq B).trans hq8)
      have hY1 : 1 ≤ Y := le_max_left _ _
      have hden : 1 ≤ 16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4 := by
        have : 1 ≤ (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4 :=
          one_le_pow₀ (hW1 B)
        nlinarith
      have hT0 : 0 ≤ Tfreq d C B (JB B) (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4) := by
        unfold Tfreq; exact div_nonneg (sq_nonneg _) (by linarith)
      have hT : Tfreq d C B (JB B) (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4) ≤ Z^16 := by
        unfold Tfreq capRes
        rw [← hY]
        calc Y^2 / _ ≤ Y^2 := div_le_self (sq_nonneg _) hden
          _ ≤ (Z^8)^2 := pow_le_pow_left₀ (by linarith) hY8 2
          _ = Z^16 := by ring
      have hrad : frequencyRadius (Tfreq d C B (JB B) (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4)) Z ms ≤ Z^17 := by
        unfold frequencyRadius
        have hzm : Z^(ms/2) ≤ Z := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ1.le hms2
        rw [show Z^17 = Z^16*Z by ring]
        exact mul_le_mul hT hzm (Real.rpow_nonneg hz.le _) (by positivity)
      have hr0 : 0 ≤ frequencyRadius (Tfreq d C B (JB B) (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B) (JB B))^4)) Z ms := by
        unfold frequencyRadius; exact mul_nonneg hT0 (Real.rpow_nonneg hz.le _)
      refine (family_cap (restOf d.root (by norm_num) d.cover C B (JB B)) (childCharacter τ ξ) _ Z _ _ _
        hZ1 hX1 hR hpool hr0 hrad).trans ?_
      rw [e8, e16, e80]
      have hcf : 0 ≤ cfam := by unfold cfam; have := cfix_nonneg; positivity
      calc 4*((Z*(Ideal.span {CenteredMomentSecondHeightFamily.fixedBadMask}).absNorm*
            (Ideal.span {(72:O)}).absNorm*(Z^8*Z^8))*(Ideal.span {(12:O)}).absNorm*cfix)*Z^8*
            (Z^8)^2*Z^16*Z^17 = cfam*Z^74 := by unfold cfam; ring
        _ ≤ Z*Z^74 := mul_le_mul_of_nonneg_right hZc (by positivity)
        _ = Z^75 := by ring
        _ ≤ Z^80 := hmon 75 80 (by norm_num)
  · exact diag_side_budget d hε Nm hNm hK1 C Dl hC hD hCD hcpC hcpD hNC hND hDC E τ hmod n hn
      JB Us hUs 8 le_rfl hUX 1 (ε/4) Mc zero_le_one hMc0 hMc
      (fun B => selOf_card_le d hε ms hm0.le hmesh C B Nm hNm)
      (fun B => selOf_width d hε ms hm0.le hmesh hms C B Nm hNm)
      JL cL controlT Q εL 8 δ εsum saving C0 Ckernel A Csum Ct hεL hC0 hCk hA hCsum hCt
      Cc eC hCc hcard J control Cside hCs hJL hcL h00 θ0 θf θt hθ0 hθt hAf hA0 hAt

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderDiag
