/- Copyright (c) 2026 Sil. Apache-2.0.
One uniform loss choice and the literal original-root-to-outer admission.
The original source, actual common allocations and retained first row
determine the declared radius and both selected-window gates.
-/
import Candidate.SilPrior.FourthPower.OuterFreshCutoffAllowance
import Candidate.SilPrior.FourthPower.OuterFreshSelection
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondActualWidth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.OuterFreshRootAdmission
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion ActualEisensteinCubic
open QRH.Record1252270103KernelMass
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedFirstLiveSource MixedLiveNormalization MixedCommonCoefficient
open MixedFirstExceptionalNormalization MixedFirstExceptionalWindow MixedFirstGeometricCaps
open MixedFirstCutoffs MixedFirstNonexceptionalAllocation
open MixedFirstLiveRemainders MixedInnerExceptionalBlock
open MixedSupplierFourthRow MixedSupplierSource
open OuterFreshSource OuterFreshSelected OuterFreshSelection
open OuterFreshSelectedWindow
open OuterFreshMixedCapacity OuterFreshCutoffAllowance
open OuterFreshDeclaredRadius OuterFreshNonexceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondChildRadialWidth CenteredMomentSecondScaled
open CenteredMomentSecondDyadicRowSupport
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type*} [Fintype ι] {a b : ℝ}

theorem presentation_loss_mono (b Z : ℝ) (hZ : 1<Z) {n N : ℕ} (hn : n≤N) :
    presentationLoss b Z n≤presentationLoss b Z N := by
  have hc:=Real.logb_le_logb_of_le hZ (capConstant_pos b n) (capConstant_mono b hn)
  have hd:(n:ℝ)*Real.logb Z (2:ℝ)≤(N:ℝ)*Real.logb Z (2:ℝ):=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (Real.logb_nonneg hZ (by norm_num))
  unfold presentationLoss
  linarith

/-- The event depends only on fixed support, dimension and loss.
Every later source subtype, ideal, profile, height and retained row is
chosen after this event. The presentation loss includes its full cap. -/
def UniformEvent (b : ℝ) (N : ℕ) (θ Z : ℝ) : Prop :=
  1<Z ∧ 2≤Z^θ ∧ frequencyLoss Z 1 θ≤θ ∧
    ∀n : ℕ,n≤N→(n:ℝ)*Real.logb Z (2:ℝ)≤θ ∧ presentationLoss b Z n≤θ

theorem uniform_event (b : ℝ) (N : ℕ) (θ : ℝ) (hθ : 0<θ) :
    ∀ᶠZ : ℝ in atTop,UniformEvent b N θ Z := by
  have htwo:∀ᶠZ : ℝ in atTop,(2:ℝ)≤Z^θ:=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop hθ)) _
  have hfour:∀ᶠZ : ℝ in atTop,(4:ℝ)≤Z^(θ/2):=
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<θ/2))) _
  filter_upwards [common_enclosure_cost_eventually N θ hθ,
    presentation_loss_eventually b N θ hθ,htwo,hfour] with Z he hp ht hf
  refine ⟨he.1,ht,?_,?_⟩
  · have hl:=Real.logb_le_logb_of_le he.1 (by norm_num : (0:ℝ)<4) hf
    rw [Real.logb_rpow (zero_lt_one.trans he.1) he.1.ne'] at hl
    simp only [frequencyLoss,mul_one]
    linarith
  · intro n hn
    exact ⟨he.2 n hn,(presentation_loss_mono b Z he.1 hn).trans hp.2⟩

/-- This single choice pays both common enclosure errors, both cutoff
losses and the declared-radius enlargement. The last strict inequality
leaves the rest of the caller's epsilon budget untouched. -/
theorem choose_uniform_reserve (b : ℝ) (N : ℕ) (Delta rhoMixed mesh ε : ℝ)
    (hgap : rhoMixed+4*mesh<Delta) (hε : 0<ε) :
    ∃θ : ℝ,0<θ ∧ rhoMixed+4*mesh+4*θ≤Delta ∧
      4*θ+5*(θ+θ)/6<ε ∧ ∀ᶠZ : ℝ in atTop,UniformEvent b N θ Z := by
  let θ:=min ((Delta-rhoMixed-4*mesh)/16) (ε/8)
  have hθ:0<θ:=lt_min (by linarith) (by linarith)
  have h₁:θ≤(Delta-rhoMixed-4*mesh)/16:=min_le_left _ _
  have h₂:θ≤ε/8:=min_le_right _ _
  exact ⟨θ,hθ,by linarith,by linarith,uniform_event b N θ hθ⟩

/-- The actual declared width uses the frozen volume only once. -/
def declaredWidth (q : Data ι) (η : Character) (K Z D0 c θ : ℝ)
    (C E : Id) (U : Finset (CommonIndex C E)) : ℝ :=
  (inputWidth η K Z-Real.logb Z (frozenVolume q))+(D0-c)-max (D0-c) 0-
    2*Real.logb Z (selectedVolume q)-
    Real.logb Z (normValue (commonFrequencyGenerator C E))+
    Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)-θ+4*θ

/-- The whole second common norm already dominates the unit subset.
Consequently no growing second common factor enters this upper cap. -/
theorem declared_width_le_input (q : Data ι) (hP : ∀i,1≤q.P i)
    (η : Character) (K Z D0 c θ : ℝ) (hZ : 1<Z)
    (C E : Id) (hC : Supported C) (U : Finset (CommonIndex C E)) :
    declaredWidth q η K Z D0 c θ C E U ≤ inputWidth η K Z+3*θ := by
  have hf:1≤frozenVolume q:=Finset.one_le_prod₀ (fun i _=>hP i.val)
  have hd:1≤selectedVolume q:=Finset.one_le_prod₀ (fun i _=>hP i.val.val)
  have hfl:=Real.logb_nonneg hZ hf
  have hdl:=Real.logb_nonneg hZ hd
  have hcommon:=CenteredMomentSecondActualWidth.actual_common_log_ge_unit C E hC U Z hZ
  unfold declaredWidth
  linarith [le_max_left (D0-c) 0]

/-- Only original K/conductor/presentation caps are needed; no bound on
the moving frozen or second common ideals is assumed here. -/
theorem declared_width_polynomial_cap (q : Data ι) (hP : ∀i,1≤q.P i)
    (η : Character) (K Z D0 c θ BK Bη BF : ℝ) (hK : 0<K) (hZ : 1<Z)
    (hKcap : K≤Z^BK) (hηcap : (η.modulus.absNorm:ℝ)≤Z^Bη)
    (hFcap : fixedPresentationCost≤Z^BF)
    (C E : Id) (hC : Supported C) (U : Finset (CommonIndex C E)) :
    declaredWidth q η K Z D0 c θ C E U≤BK+Bη+BF+3*θ := by
  have hk:=Real.logb_le_logb_of_le hZ hK hKcap
  have hn:=Real.logb_le_logb_of_le hZ
    (zero_lt_one.trans_le (ideal_norm_one_le η.modulus_ne_bot)) hηcap
  have hf:=Real.logb_le_logb_of_le hZ fixedPresentationCost_pos hFcap
  rw [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] at hk hn hf
  have hd:=declared_width_le_input q hP η K Z D0 c θ hZ C E hC U
  unfold inputWidth at hd
  linarith

set_option maxHeartbeats 800000 in
/-- Admission from the ORIGINAL root domain, not from an asserted child
capacity or an energy bound. Both generations of actual common allocation
and the actual retained first cutoff are included. The second physical
radius is constructed from the exact residual support envelope.

The same declared radius pays the physical disk and the mixed/native
gates for every second allocation. Summation and analytic window estimates
are deliberately not claimed by this admission theorem. -/
theorem actual_first_large_admission
    (s : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure s)
    (w : ι→ℝ) (rhoFloor mesh : ℝ) (hm : 0≤mesh)
    (hw : ∀i,0≤w i) (hwm : ∀i,w i≤mesh)
    (η τ : Character) (C₁ D₁ : Id) (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (hCD₁ : CompletedGauss.primeSupport C₁=CompletedGauss.primeSupport D₁)
    (E₁ : Finset (CommonIndex C₁ D₁))
    (B₁ : actualAllocations (tuplePools s) C₁)
    (hf₁ : frozenCoefficient B₁.val C₁ s.R s.ν s.Wslot s.P≠0)
    (Z K θ Delta rhoMixed : ℝ) (hK : 0<K) (hθ : 0<θ)
    (hevent : UniformEvent b (Fintype.card ι) θ Z)
    (hreserve : rhoMixed+4*mesh+4*θ≤Delta)
    (hP : ∀i,s.P i=Z^(w i))
    (hroot : Real.logb Z (s.T/pairNorm s.d)+(93/25:ℝ)*(∑i,w i) ≤ inputWidth η K Z-Delta)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C₁ D₁=>P.val) E₁*activeConductor C₁ D₁})
    (n : ℤ)
    (hn : Retained (frequencyRadius (firstCutoff C₁ D₁ E₁ K (sourceVolume s)) Z θ) n)
    (u : Id) (L : Finset (liveIndices B₁.val))
    (hrho : 0<rhoFloor) (hlarge : rhoFloor<liveWidth L (fun i=>w i.val))
    (C₂ D₂ : Id) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : CompletedGauss.primeSupport C₂=CompletedGauss.primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (G : Id) (hG : G=C₂ ∨ G=D₂) :
    letI : DecidableEq (liveIndices B₁.val) := Classical.decEq _
    let s₁ : Source (liveIndices B₁.val) a b := allocatedLiveSource s hb cover C₁ B₁
    let cover₁ : OriginalEnclosure s₁ := live_enclosure (allocationSource s hb cover C₁ B₁)
    let J:=chosenSlots L (fun i=>w i.val) rhoFloor mesh hm (fun i=>hw i.val) (fun i=>hwm i.val)
    let q : Data (liveIndices B₁.val) := supplierData s₁ ha u L J
    let D0:=deficit C₁ D₁ E₁ K (sourceVolume s) Z n
    let Rdecl:=declaredWidth q η K Z D0 (Real.logb Z (C₁.absNorm:ℝ)) θ C₂ D₂ U
    ∀x : Frozen q,MixedSupplierFourthRow.frozenWeight q x≠0→
      OuterFreshDeclaredRadius.physicalWidth τ (frozenProduct q x) C₂ D₂ U
        (frequencyRadius (secondSourceCutoff (residualSource s₁ ha cover₁ u L J x)
          (nominalChildScale C₁ D₁ E₁ K (sourceVolume s) Z θ n)) Z θ) Z≤Rdecl ∧
      let r:=unavoidedResidual s₁ ha cover₁ u L J x
      ∀B₂ : actualAllocations (tuplePools r) G,
        frozenCoefficient B₂.val G r.R r.ν r.Wslot r.P≠0→
        let live:=allocatedLiveSource r hb (unavoided_enclosure s₁ ha cover₁ u L J x) G B₂
        Real.logb Z (live.T/pairNorm live.d)+
            2*(∑j : liveIndices B₂.val,w j.val.val.val.val)+
            4*Real.logb Z (selectedVolume q)≤Rdecl-rhoMixed ∧
          rhoFloor/400<Real.logb Z (selectedVolume q)-
            (3/4:ℝ)*(∑j : liveIndices B₂.val,w j.val.val.val.val) ∧
          (3/4:ℝ)*(∑j : liveIndices B₂.val,w j.val.val.val.val)<Real.logb Z (selectedVolume q) := by
  letI : DecidableEq (liveIndices B₁.val) := Classical.decEq _
  let s₁ : Source (liveIndices B₁.val) a b := allocatedLiveSource s hb cover C₁ B₁
  let cover₁ : OriginalEnclosure s₁ := live_enclosure (allocationSource s hb cover C₁ B₁)
  let w₁:liveIndices B₁.val→ℝ:=fun i=>w i.val
  let J:=chosenSlots L w₁ rhoFloor mesh hm (fun i=>hw i.val) (fun i=>hwm i.val)
  let q : Data (liveIndices B₁.val) := supplierData s₁ ha u L J
  let D0:=deficit C₁ D₁ E₁ K (sourceVolume s) Z n
  let c:=Real.logb Z (C₁.absNorm:ℝ)
  let Rdecl:=declaredWidth q η K Z D0 c θ C₂ D₂ U
  have hZ:=hevent.1
  have hcard:Fintype.card (liveIndices B₁.val)≤Fintype.card ι:=
    Fintype.card_le_of_injective (fun i : liveIndices B₁.val=>i.val) Subtype.val_injective
  have hrest:Fintype.card (RestIndex q)≤Fintype.card ι:=(rest_card_le q).trans hcard
  have hcost:=(hevent.2.2.2 (Fintype.card ι) le_rfl).1
  have hcost₂:=(hevent.2.2.2 (Fintype.card (RestIndex q)) hrest).1
  have hpresentation:=(hevent.2.2.2 (Fintype.card (liveIndices B₁.val)) hcard).2
  have hD0:-θ≤D0:=by
    have hd:=actual_retained_deficit C₁ D₁ hC₁ hD₁ hCD₁ E₁ K (sourceVolume s) Z θ
      hK (sourceVolume_pos s) hZ n hn
    exact (neg_le_neg hevent.2.2.1).trans hd
  have hc:0≤c:=Real.logb_nonneg hZ (ideal_norm_one_le hC₁.1)
  have hroot₁:Real.logb Z (s₁.T/pairNorm s₁.d)+(93/25:ℝ)*(∑i,w₁ i)≤
      inputWidth η K Z-c-(Delta-(Fintype.card ι:ℝ)*Real.logb Z (2:ℝ)):=by
    have hh:=actual_first_common_root s hb cover C₁ hC₁.1 B₁ Z w hZ hw hP s.hW hf₁
      (inputWidth η K Z) Delta hroot
    dsimp only at hh
    change Real.logb Z (s₁.T/pairNorm s₁.d)+(93/25:ℝ)*(∑i,w₁ i)≤_ at hh
    linarith
  have herr:Real.logb Z (effectiveVolume s₁)-Real.logb Z (sourceVolume s)+c≤θ:=
    (first_allocation_error s hb cover C₁ hC₁.1 B₁ Z hZ hf₁).trans hcost
  have hdeclared:(inputWidth η K Z-Real.logb Z (∏i : ↥Lᶜ,s₁.P i.val))+
      (D0-c)-max (D0-c) 0-
      2*Real.logb Z (MixedSelectedVolume.volume q)-
      Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)-θ≤Rdecl:=by
    change _≤(inputWidth η K Z-Real.logb Z (∏i : ↥Lᶜ,s₁.P i.val))+
      (D0-c)-max (D0-c) 0-
      2*Real.logb Z (MixedSelectedVolume.volume q)-
      Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)-θ+4*θ
    linarith
  have hgates:=chosen_allocated_large_gate s₁ ha hb cover₁ u L w₁ rhoFloor mesh hm
    (fun i=>hw i.val) (fun i=>hwm i.val) Z hZ (fun i=>hP i.val) hrho hlarge
    C₂ D₂ hC₂ hD₂ hCD₂ U G hG (inputWidth η K Z) c D0
    (Delta-(Fintype.card ι:ℝ)*Real.logb Z (2:ℝ)) θ θ Rdecl rhoMixed
    hc hθ.le hD0 hroot₁ hdeclared (by linarith)
  dsimp only
  intro x hx
  constructor
  · have hp:=actual_physical_width s₁ ha cover₁ u L J x hx η τ C₁ D₁ hC₁ hD₁ hCD₁ E₁
      K (sourceVolume s) Z θ θ hK (sourceVolume_pos s) hZ hmod n C₂ D₂ U
    dsimp only at hp
    change _≤Rdecl
    change _≤(inputWidth η K Z-Real.logb Z (frozenVolume q))+(D0-c)-max (D0-c) 0-
      2*Real.logb Z (selectedVolume q)-
      Real.logb Z (normValue (commonFrequencyGenerator C₂ D₂))+
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)-θ+4*θ
    linarith only [hp,herr,hpresentation,hθ]
  · exact hgates x

/-- A nonzero actual block supplies the character cap required by the
uniform window theorem. No separate polynomial estimate for its moving
sharp conductor is needed. Both orientations retain their exact rows. -/
theorem sharp_nonempty_window_caps
    (τ : Character) (f : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ f ξ C E hC hE U ψ)
    (t : ℝ) (S : Finset Id) (β : Id→ℂ) (Rfreq : ℝ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock τ t S β C E hC hE U Rfreq rows W K n≠0)
    (Z Rdecl B : ℝ) (hZ : 1<Z)
    (hpaid : physicalWidth τ f C E U Rfreq Z≤Rdecl) (hcap : Rdecl≤B) :
    0≤Rdecl ∧ 1≤dyadicScale (n 1) ∧
      ∀χ : RayCharacter,((ψ χ).modulus.absNorm:ℝ)≤Z^B ∧
        ∀z∈dyadicRows (liveRows C E U Rfreq rows) n,
          normValue z≤paddedRadius (ψ χ) Z Rdecl ∧
          normValue (-z)≤paddedRadius (ψ χ) Z Rdecl := by
  have hadmit:=physical_nonempty_admission τ f ξ C E hC hE U ψ hψ
    t S β Rfreq rows W K hK n hne Z Rdecl hZ hpaid (1:RayCharacter)
  refine ⟨hadmit.1,hadmit.2,?_⟩
  intro χ
  obtain ⟨z,hzl,_hzd,hz,_⟩:=physicalBlock_live_dyadic_witness
    τ t S β C E hC hE U Rfreq rows W K n hne
  have hp:1≤paddedRadius (ψ χ) Z Rdecl:=
    (normValue_ge_one z hz).trans (physical_rows_padded τ f ξ C E hC hE U ψ hψ
      t S β Rfreq rows W K hK n hne Z Rdecl hZ hpaid χ z hzl)
  have hη:0<((ψ χ).modulus.absNorm:ℝ):=
    zero_lt_one.trans_le (ideal_norm_one_le (ψ χ).modulus_ne_bot)
  have hden:0<fixedPresentationCost*((ψ χ).modulus.absNorm:ℝ):=
    mul_pos fixedPresentationCost_pos hη
  have hpaidnorm:fixedPresentationCost*((ψ χ).modulus.absNorm:ℝ)≤Z^Rdecl:=by
    exact (one_mul _).symm.trans_le ((le_div_iff₀ hden).mp hp)
  constructor
  · calc
      ((ψ χ).modulus.absNorm:ℝ)≤fixedPresentationCost*((ψ χ).modulus.absNorm:ℝ):=
        le_mul_of_one_le_left hη.le MixedFirstChosenEnergy.fixed_presentation_one_le
      _≤Z^Rdecl:=hpaidnorm
      _≤Z^B:=Real.rpow_le_rpow_of_exponent_le hZ.le hcap
  · intro z hz
    have hp:=physical_rows_padded τ f ξ C E hC hE U ψ hψ t S β Rfreq rows W K hK n hne
      Z Rdecl hZ hpaid χ z (dyadicRows_subset _ n hz)
    exact ⟨hp,by simpa only [normValue,Ideal.span_singleton_neg] using hp⟩

end
end Candidate.SilPrior.FourthPower.OuterFreshRootAdmission
