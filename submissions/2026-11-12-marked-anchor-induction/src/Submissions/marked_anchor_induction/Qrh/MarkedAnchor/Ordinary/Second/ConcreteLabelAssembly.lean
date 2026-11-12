/- Copyright (c) 2026 Sil. Apache-2.0.
Label assembly, part 1: the one-sided SOURCE energies of `grouped_label_blocks` are
dominated by the frame energies of the concrete (raised) labels.

For a residual FP source `s` on `Fin N` in canonical form, a second label (genuine pair
`(C₂, D₂)`, unit set `U`, second exceptional family `τ` over the child base
`childCharacter F.left ξ`, second artificial divisor `t₂ = L`, ray character `χ`) and either
column `G ∈ {C₂, D₂}`:

  `E^{src}_{G,L,χ}(v; H) := sourceRestrictedEnergy (nonexceptional ψ χ Q m A₂)
      (residualPool G S) (I ↦ [(G, I) = 1, L ∣ I] β(G·I)) (heightCoeff (τ χ) v) ballProfile H`

(the hypothesis shape of `Concrete.grouped_label_blocks`, `S` the active residual columns,
`β` the seedless residual coefficient) satisfies (`source_le_frame`)

  `E^{src}(v; H) ≤ rawEnergy η r x v`

for the frame label `x = LabelData.toLabel η …` of the column (twin character, dyad `k` with
`2H ≤ 2^k`), on the frame source `r` of `s`. The steps: pool enlargement by zero columns
(`sourceRestrictedEnergy_pool_eq`), `Family.nonexceptional_iff` (the keep is the canonical
keep of `τ χ`, with `Q = internalQ θ.Q θ.η₀`), radius monotonicity, the canonical bridge
(`labelEnergy_source`), and the twin transfer (`labelEnergy_packed_col`) whose first-step
zero-prime hypothesis is DISCHARGED from `C ∣ R` (the first common factor is in the residual
puncture, as for FP `liveSource`, `R = s.R * s.G`): `zeroPrimes_of_puncture`.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteFrame
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteFrameReindex
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteLabelGroup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open Candidate.FourthPower QRH.SilDensitySplit.CubeFree.FP QRH.SilDensitySplit.CubeFree.Packet.Reduce
open QRH.SilDensitySplit.CubeFree.Packet QRH.SilDensitySplit.CubeFree.Packet.Grouped
open QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelAssignmentReindex KernelNaturalSlots ReferencePrimeEnclosure MixedCompletedRows
open NativeFiniteHoles NativeInjectiveEnergy
open MixedCenteredEnergy MixedLiveRows MixedLiveNormalization MixedCanonicalSource
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation
open MixedCommonSource MixedOriginalSource MixedRestrictedDictionary MixedHeightEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot (primePool)
open CenteredMomentInductionEnergy CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentFiniteProfileExceptional
open CenteredMomentRayMaskedFloor HeckeDyadic CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentFirstSectors CenteredMomentSourceRectangle CenteredMomentSourceMass
open CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst CenteredMomentSourceRow
open CanonicalRowCompletion CompletedGauss RayFourExpansion CenteredMomentFirstPhysicalSource
open CenteredMomentSecondCanonicalNonunit CenteredMomentChildRows CenteredMomentRestrictedEnergy
open CenteredMomentRowNorm MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

/-! ### 1. Restricted energies: zero columns, keep -/

theorem rowPolynomial_source (Q : Finset Id) (g : Id → ℂ) (z : O) :
    rowPolynomial (Finset.univ : Finset (supportedColumns Q)) (sourceGenerator Q)
        (fun I : supportedColumns Q => g I) z =
      ∑ I ∈ supportedColumns Q, g I * idealRowHom z I := by
  unfold rowPolynomial
  rw [← Finset.sum_coe_sort (supportedColumns Q) (fun I => g I * idealRowHom z I)]
  apply Finset.sum_congr rfl
  intro I _
  rw [sourceGenerator, primary_span_supported I (Finset.mem_filter.mp I.property).2]

/-- Enlarging the column set by columns with vanishing coefficient does not change a
restricted source energy. -/
theorem sourceRestrictedEnergy_pool_eq (keep : O → Prop) (Q Q' : Finset Id) (hQ : Q ⊆ Q')
    (c f : Id → ℂ) (hz : ∀ I ∈ Q', I ∉ Q → c I = 0) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceRestrictedEnergy keep Q c f W K = sourceRestrictedEnergy keep Q' c f W K := by
  unfold sourceRestrictedEnergy restrictedEnergy
  congr 1
  funext z
  have hsum : ∑ I ∈ supportedColumns Q, c I * f I * idealRowHom z I =
      ∑ I ∈ supportedColumns Q', c I * f I * idealRowHom z I := by
    apply Finset.sum_subset (Finset.filter_subset_filter _ hQ)
    intro I hI hnI
    have hIQ : I ∉ Q := fun h => hnI (Finset.mem_filter.mpr ⟨h, (Finset.mem_filter.mp hI).2⟩)
    rw [hz I (Finset.mem_filter.mp hI).1 hIQ, zero_mul, zero_mul]
  rw [rowPolynomial_source Q (fun I => c I * f I) z, rowPolynomial_source Q' (fun I => c I * f I) z,
    hsum]

theorem residualPool_mono (G : Id) (hG : G ≠ 0) {S S' : Finset Id} (h : S ⊆ S') :
    residualPool G hG S ⊆ residualPool G hG S' := by
  intro I hI
  rw [mem_residualPool] at hI ⊢
  exact h hI

/-! ### 2. Coprimality of the nonzero columns to the puncture -/

theorem originalColumn_coprime {α : Type*} [Fintype α] (S H : Finset PrimeIdeal)
    (pool : α → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (J : Id) (h : originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ J ≠ 0) :
    IsCoprime J R := by
  unfold originalColumn finiteColumnCoefficient at h
  obtain ⟨v, hv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hvJ := (Finset.mem_filter.mp hv).2
  by_contra hc
  apply hne
  unfold profileCoefficient
  rw [hvJ, if_neg hc]
  ring

/-- The first exponent-zero primes divide the first common factor. -/
theorem coprime_zeroPrimes {C D I : Id} (h : IsCoprime I C) : IsCoprime I (firstZeroPrimes C D) := by
  unfold firstZeroPrimes
  rw [IsCoprime.prod_right_iff]
  intro i _
  exact h.of_isCoprime_of_dvd_right (activePrime_dvd C D i)

theorem coprime_zeroPrimesRight {C D I : Id} (h : IsCoprime I C) :
    IsCoprime I (firstZeroPrimesRight C D) := by
  unfold firstZeroPrimesRight
  rw [IsCoprime.prod_right_iff]
  intro i _
  exact h.of_isCoprime_of_dvd_right (activePrime_dvd C D i)

/-- **The zero-prime hypothesis of the twin transfer from the puncture.** -/
theorem zeroPrimes_of_puncture {α : Type*} [Fintype α] (S H : Finset PrimeIdeal)
    (pool : α → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (P : α → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (C D G : Id) (hCR : C ∣ R) (I : Id)
    (h : originalColumn S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ (G * I) ≠ 0) :
    IsCoprime I (firstZeroPrimes C D) := by
  have h1 := originalColumn_coprime S H pool d hd R seed ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ _ h
  exact coprime_zeroPrimes ((h1.of_isCoprime_of_dvd_right hCR).of_mul_left_right)

/-! ### 2'. The packing datum of one first-step side -/

/-- The packing datum of one first-step side: the side character, its packed twist `V`, the
dictionary phase `j₀`, the exponent-zero primes `Z₀`, the first common factor `Cs` of the side
(in the residual puncture), the packing identity off `Z₀`, and `(I, Cs) = 1 → (I, Z₀) = 1`. -/
structure SidePack (η : Character) where
  base : Character
  V : O
  j₀ : DictIdx
  Z₀ : Id
  Cs : Id
  hV : V ≠ 0
  hZ₀ : Z₀ ≠ 0
  pack : ∀ I : Id, Supported I → IsCoprime I Z₀ → ∀ t : ℝ,
    heightCoeff base t I = heightCoeff (anchors η j₀) t I * idealRowHom V I
  zcop : ∀ I : Id, IsCoprime I Cs → IsCoprime I Z₀

theorem activePrime_dvd_right (C D : Id) (i : ActiveIndex C D) : activePrime C D i ∣ D :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
    (Multiset.mem_toFinset.mp (Finset.mem_inter.mp i.val.property).2)

theorem coprime_zeroPrimesRight_D {C D I : Id} (h : IsCoprime I D) :
    IsCoprime I (firstZeroPrimesRight C D) := by
  unfold firstZeroPrimesRight
  rw [IsCoprime.prod_right_iff]
  intro i _
  exact h.of_isCoprime_of_dvd_right (activePrime_dvd_right C D i)

/-- The left side of a fixed pair (`F.left`, `V_C`, `ξ₁·firstPhase`, first common factor `C`). -/
def SidePack.left {η : Character} {C D : Id} {hC : Supported C} {E : Finset (CommonIndex C D)}
    {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂) : SidePack η where
  base := F.left
  V := firstPacked C D hC E
  j₀ := ξ₁ * firstPhase C D hC
  Z₀ := firstZeroPrimes C D
  Cs := C
  hV := firstPacked_ne_zero C D hC E
  hZ₀ := firstZeroPrimes_ne_zero C D
  pack I hI hZ t := left_packed F I hI hZ t
  zcop I h := coprime_zeroPrimes h

/-- The right side of a fixed pair (`F.right`, `V_D`, `ξ₂·firstPhase`, first common factor `D`). -/
def SidePack.right {η : Character} {C D : Id} {hC : Supported C} {E : Finset (CommonIndex C D)}
    {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂) : SidePack η where
  base := F.right
  V := firstPackedRight C D hC E
  j₀ := ξ₂ * firstPhase C D hC
  Z₀ := firstZeroPrimesRight C D
  Cs := D
  hV := firstPackedRight_ne_zero C D hC E
  hZ₀ := firstZeroPrimesRight_ne_zero C D
  pack I hI hZ t := right_packed F I hI hZ t
  zcop I h := coprime_zeroPrimesRight_D h

@[simp] theorem SidePack.left_base {η : Character} {C D : Id} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂) :
    (SidePack.left F).base = F.left ∧ (SidePack.left F).V = firstPacked C D hC E ∧
      (SidePack.left F).Cs = C := ⟨rfl, rfl, rfl⟩

@[simp] theorem SidePack.right_base {η : Character} {C D : Id} {hC : Supported C}
    {E : Finset (CommonIndex C D)} {ξ₁ ξ₂ : RayCharacter} (F : FixedPair η C D hC E ξ₁ ξ₂) :
    (SidePack.right F).base = F.right ∧ (SidePack.right F).V = firstPackedRight C D hC E ∧
      (SidePack.right F).Cs = D := ⟨rfl, rfl, rfl⟩

/-- **Second-step packing for the child base of a side.** -/
theorem second_packed_side {η : Character} (P : SidePack η) (ξ : RayCharacter)
    {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂} {U : Finset (CommonIndex C₂ D₂)}
    {τ : RayCharacter → Character}
    (h : Family (childCharacter P.base ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) (hZ : IsCoprime I P.Z₀)
    (hi : IsCoprime C₂ I ∨ IsCoprime D₂ I) (t : ℝ) :
    heightCoeff (τ χ) t I =
      heightCoeff (anchors η (P.j₀ * ξ * χ)) t I * idealRowHom (P.V * secondTwist C₂ D₂ U) I := by
  rw [h.height_eq χ I hI hi t, heightCoeff_child P.base ξ t I hI, P.pack I hI hZ t]
  unfold anchors
  rw [rayAnchor_mul_height η _ χ I hI t, rayAnchor_mul_height η _ ξ I hI t, secondTwist]
  simp only [idealRowHom_argument_mul]
  ring

theorem zeroPrimes_side {η : Character} (P : SidePack η) {α : Type*} [Fintype α]
    (S H : Finset PrimeIdeal)
    (pool : α → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (R seed : Id)
    (ν : α → Id → ℂ) (Wslot : α → ℝ → ℂ) (Pw : α → ℝ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ)
    (G : Id) (hCR : P.Cs ∣ R) (I : Id)
    (h : originalColumn S H pool d hd R seed ν Wslot Pw W₁ W₂ b X₁ X₂ Y₁ Y₂ (G * I) ≠ 0) :
    IsCoprime I P.Z₀ := by
  have h1 := originalColumn_coprime S H pool d hd R seed ν Wslot Pw W₁ W₂ b X₁ X₂ Y₁ Y₂ _ h
  exact P.zcop I ((h1.of_isCoprime_of_dvd_right hCR).of_mul_left_right)

/-! ### 3. The twin transfer on either second column -/

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

/-- `labelEnergy_packed` for the column `G` (`G = C₂` or `G = D₂`). -/
theorem labelEnergy_packed_col {η : Character} (P : SidePack η)
    (ξ : RayCharacter) {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂}
    {U : Finset (CommonIndex C₂ D₂)} {τ : RayCharacter → Character}
    (hfam : Family (childCharacter P.base ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (G : Ideal O) (hGs : Supported G) (hGc : ∀ I, IsCoprime G I → IsCoprime C₂ I ∨ IsCoprime D₂ I)
    (M : Ideal O) [NeZero M] (Hray : Subgroup (O ⧸ M)ˣ)
    (hHray : RayOrthogonality.globalUnits M ≤ Hray) {α : Type*} [Fintype α] (W : ℝ → ℂ)
    (η₀ : Character) (θs : α → RayQuotient.Characters M Hray) (w σ freq : α → ℝ)
    (t : ℝ) (R₀ : α → Finset (Ideal O)) (Q : Ideal O) (n : Fin 4 → ℤ)
    (Cap Lcap : ℝ) (R : Ideal O) (hG : G ≠ 0) (seed D' : Ideal O) (H : Finset PrimeIdeal)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b X₁ X₂ Y₁ Y₂ : ℝ) (d : Ideal O × Ideal O) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (v : ℝ) (hCR : P.Cs ∣ R) :
    labelEnergy M Hray hHray W η₀ θs Z w σ freq t R₀ (τ χ) Q n Cap Lcap R G hG seed D' H
        W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v =
      labelEnergy M Hray hHray W η₀ θs Z w σ freq t R₀
        (packedChar η (P.j₀ * ξ * χ) (P.V * secondTwist C₂ D₂ U)) Q n Cap Lcap R G hG
        seed D' H W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v := by
  have hV : P.V * secondTwist C₂ D₂ U ≠ 0 :=
    mul_ne_zero P.hV (secondTwist_ne_zero C₂ D₂ hC₂ U)
  apply labelEnergy_congr M Hray hHray W η₀ θs Z w σ freq t R₀ _ _ Q n Cap Lcap R G hG seed D' H
    W₁ W₂ t₁ t₂ b X₁ X₂ Y₁ Y₂ d hd v (packMask P.Z₀ G)
    (packMask_ne_zero _ _ P.hZ₀ hGs)
  · intro I hI hw
    obtain ⟨hz, hc⟩ := packMask_coprime _ _ I hw
    have h1 := second_packed_side P ξ hfam χ I hI hz (hGc I hc) 0
    rw [Packet.heightCoeff_zero, Packet.heightCoeff_zero] at h1
    rw [h1, packedChar_coef η _ _ hV I hI]
  · intro I _ hc _ h0
    have hz := zeroPrimes_side P _ H _ d hd R seed _ _ _ _ _ b X₁ X₂ Y₁ Y₂ G hCR I h0
    rw [packMask, ConcretePrimeRowBridge.span_idealGenerator]
    exact IsCoprime.mul_right hz hc.symm

/-! ### 4. The canonical bridge for an arbitrary character -/

/-- `rawEnergy_srcOf` for an arbitrary character: the literal label energy on frame slot data
agreeing with a canonical FP source is that source's restricted second-step energy. -/
theorem labelEnergy_source (s : Source (Fin θ.N) θ.a θ.b) (rs : GSrc θ mesh Z)
    (hW₁ : rs.W₁ = s.W₁) (hW₂ : rs.W₂ = s.W₂) (ht₁ : rs.t₁ = s.t₁ / (2 * Real.pi))
    (ht₂ : rs.t₂ = s.t₂ / (2 * Real.pi)) (hX₁ : rs.X₁ = s.X₁) (hX₂ : rs.X₂ = s.X₂)
    (hY₁ : rs.Y₁ = s.Y₁) (hY₂ : rs.Y₂ = s.Y₂)
    (τ : Character) (Q : Id) (n : Fin 4 → ℤ) (R G : Id) (hG : G ≠ 0) (seed D : Id)
    (H : Finset PrimeIdeal) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0) (v : ℝ)
    (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ H R d) (ha : 0 < θ.a) :
    labelEnergy θ.rayM θ.Hray θ.hH θ.W θ.η₀ rs.χ Z rs.w rs.σ rs.freq rs.t rs.R₀ τ Q n θ.Cap
        θ.Lcap R G hG seed D H rs.W₁ rs.W₂ rs.t₁ rs.t₂ θ.b rs.X₁ rs.X₂ rs.Y₁ rs.Y₂ d hd v =
      sourceRestrictedEnergy (canonicalRadial τ Q n).keep (residualPool G hG (sourceColumns s))
        (fun I => if IsCoprime G I ∧ D ∣ I then sourceCoefficient s ha seed (G * I) else 0)
        (heightCoeff τ v) ballProfile (dyadicScale (n 1)) := by
  obtain ⟨hS, hH, hpool, hν, hWs, hP, hR, hdd⟩ := hcan
  have hpool' := funext hpool
  have hν' := funext hν
  have hWs' := funext hWs
  have hP' := funext hP
  rw [hW₁, hW₂, ht₁, ht₂, hX₁, hX₂, hY₁, hY₂]
  unfold labelEnergy sourceColumns sourceCoefficient MixedPrincipalAllocations.tuplePools
  rw [normPowerProfile_eq_phase, normPowerProfile_eq_phase]
  cases s
  simp only at hS hH hpool' hν' hWs' hP' hR hdd ⊢
  subst hS hH hpool' hν' hWs' hP' hR hdd
  rfl

/-! ### 5. Source energies below frame energies -/

/-- **The grouped source energy of one (label, `t₂`, column, ray) is at most the frame energy
of the concrete label** (twin character, dyad `x.n 1` with `2H ≤ 2^{x.n 1}`). -/
theorem source_le_frame {η : Character} (P : SidePack η)
    (ξ : RayCharacter) {C₂ D₂ : Ideal O} {hC₂ : Supported C₂} {hD₂ : Supported D₂}
    {U : Finset (CommonIndex C₂ D₂)} {τ : RayCharacter → Character}
    (hfam : Family (childCharacter P.base ξ) C₂ D₂ hC₂ hD₂ U τ) (χ : RayCharacter)
    (G : Ideal O) (hGs : Supported G) (hGc : ∀ I, IsCoprime G I → IsCoprime C₂ I ∨ IsCoprime D₂ I)
    (Q : Id) (m : O) (hm : m ≠ 0) (hml : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (hQ : internalQ θ.Q θ.η₀ = Q)
    (s : Source (Fin θ.N) θ.a θ.b) (ha : 0 < θ.a) (rs : GSrc θ mesh Z)
    (hW₁ : rs.W₁ = s.W₁) (hW₂ : rs.W₂ = s.W₂) (ht₁ : rs.t₁ = s.t₁ / (2 * Real.pi))
    (ht₂ : rs.t₂ = s.t₂ / (2 * Real.pi)) (hX₁ : rs.X₁ = s.X₁) (hX₂ : rs.X₂ = s.X₂)
    (hY₁ : rs.Y₁ = s.Y₁) (hY₂ : rs.Y₂ = s.Y₂) (hV₀ : rs.V₀ = P.V)
    (hCR : P.Cs ∣ s.R)
    (x : LabelData) (hj : x.j = P.j₀ * ξ * χ) (hA : x.A₂ = secondTwist C₂ D₂ U)
    (hxG : x.G = G) (hseed : x.seed = 1) (hx : x.Good rs)
    (hcan : Canonical s Z rs.χ rs.w rs.σ rs.freq rs.t rs.R₀ x.holesH x.R x.d)
    (S : Finset Id) (hSs : S ⊆ sourceColumns s)
    (hSz : ∀ I ∈ sourceColumns s, I ∉ S → sourceCoefficient s ha 1 I = 0)
    (Hs : ℝ) (hH : 0 < Hs) (hHk : 2 * Hs ≤ dyadicScale (x.n 1)) (v : ℝ) :
    sourceRestrictedEnergy (nonexceptional (childCharacter P.base ξ) χ Q m (secondTwist C₂ D₂ U))
        (residualPool G hGs.1 S)
        (fun I => if IsCoprime G I ∧ x.D ∣ I then sourceCoefficient s ha 1 (G * I) else 0)
        (heightCoeff (τ χ) v) ballProfile Hs ≤
      rawEnergy η rs (x.toLabel η) (toLabel_fits η rs x hx) v := by
  -- (a) enlarge the pool
  rw [sourceRestrictedEnergy_pool_eq _ _ _ (residualPool_mono G hGs.1 hSs) _ _ (by
    intro I hI hnI
    rw [mem_residualPool] at hI
    have hnI' : G * I ∉ S := fun h => hnI ((mem_residualPool G hGs.1 S I).mpr h)
    by_cases hc : IsCoprime G I ∧ x.D ∣ I
    · rw [if_pos hc, hSz _ hI hnI']
    · rw [if_neg hc])]
  -- (b) the keep is the canonical keep
  have hkeep : nonexceptional (childCharacter P.base ξ) χ Q m (secondTwist C₂ D₂ U) =
      (canonicalRadial (τ χ) (internalQ θ.Q θ.η₀) x.n).keep := by
    rw [hQ]
    funext z
    exact propext (hfam.nonexceptional_iff χ Q m z hm hml hm2)
  rw [hkeep]
  -- (c) radius
  refine (ConcreteGroup.sourceRestrictedEnergy_radius_le _ _ _ _ _ _ hH (dyadicScale_pos _)
    hHk).trans (le_of_eq ?_)
  -- (d) the canonical bridge and the twin
  have hG0 : x.G ≠ 0 := hx.G_ne
  obtain ⟨j, A₂, n, R, Gx, seed, D', holesH, d, pre⟩ := x
  simp only at hj hA hxG hseed hG0 hcan hHk ⊢
  subst hj hA hxG hseed
  have hb := labelEnergy_source s rs hW₁ hW₂ ht₁ ht₂ hX₁ hX₂ hY₁ hY₂ (τ χ)
    (internalQ θ.Q θ.η₀) n R Gx hG0 1 D' holesH d ⟨hx.d₁, hx.d₂⟩ v hcan ha
  rw [← hb]
  have hR : s.R = R := hcan.R
  rw [labelEnergy_packed_col P ξ hfam χ Gx hGs hGc θ.rayM θ.Hray θ.hH θ.W θ.η₀ rs.χ rs.w rs.σ
    rs.freq rs.t rs.R₀ (internalQ θ.Q θ.η₀) n θ.Cap θ.Lcap R hG0 1 D' holesH rs.W₁ rs.W₂ rs.t₁
    rs.t₂ θ.b rs.X₁ rs.X₂ rs.Y₁ rs.Y₂ d _ v (hR ▸ hCR)]
  unfold rawEnergy
  rw [← hV₀]
  rfl

end
end Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
