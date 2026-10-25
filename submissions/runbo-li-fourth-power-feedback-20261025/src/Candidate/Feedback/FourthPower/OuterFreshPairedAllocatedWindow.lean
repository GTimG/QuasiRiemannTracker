/- Copyright (c) 2026 Sil. Apache-2.0.
Actual paired allocated windows, before the outer common/divisor/Fourier sums.

-/
import Candidate.Feedback.FourthPower.OuterFreshRootAdmission
import Candidate.Feedback.FourthPower.OuterFreshAllocatedWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.Feedback.FourthPower.OuterFreshPairedAllocatedWindow
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CompletedGauss
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource CenteredMomentSourceRow
open CenteredMomentActiveSource CenteredMomentSecondBlockAggregate
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal
open CenteredExceptionalProfile CenteredMomentSecondScaled
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondLiveBlock
open CenteredMomentSecondEnergySplit
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentChildRows
open CenteredMomentSecondRetainedWidth CenteredMomentSecondDyadicRowSupport
open CenteredMomentSecondChildRadialWidth CenteredMomentSecondRadicalBudget
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedLiveNormalization
open MixedFirstSeededEnergy MixedFirstSourceWindow MixedFirstSourceMoment
open MixedFirstProfileEnvelope MixedFirstUniformLossBudget MixedFirstChosenEnergy
open MixedFirstActualNonexceptional
open MixedFirstReferenceChoice MixedFirstLiveSource MixedFirstSourceGeometry
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource
open MixedSupplierOriginalFrequency MixedCanonicalSource ReferencePrimeEnclosure
open OuterFreshSource OuterFreshSelectedWindow OuterFreshConsumer OuterFreshDeclaredRadius
open OuterFreshWindowPair OuterFreshRows OuterFreshNonexceptionalFamily
open OuterFreshStructure
open OuterFreshAllocatedWindow OuterFreshRootAdmission
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- One nonzero actual block gives the structural conductor bound. It then
applies to ANY retained row at the same radius, not just that block's possibly
selected-dependent partition. The nonunit frequency norm cancels exactly.
No implication from a partitioned nonzero sum to an unpartitioned sum is used. -/
theorem sharp_any_live_row_padded
    (τ : Character) (f : Id) (ξ : RayCharacter)
    (C E : Id) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ f ξ C E hC hE U ψ)
    (t : ℝ) (S : Finset Id) (β : Id→ℂ) (Rfreq : ℝ) (rows₀ : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ)
    (hne : physicalBlock τ t S β C E hC hE U Rfreq rows₀ W K n≠0)
    (Z Rdecl : ℝ) (hZ : 1<Z)
    (hpaid : physicalWidth τ f C E U Rfreq Z≤Rdecl)
    (χ : RayCharacter) (rows : Finset O) (z : O)
    (hz : z∈liveRows C E U Rfreq rows) :
    normValue z≤paddedRadius (ψ χ) Z Rdecl := by
  obtain ⟨hR,hG,hV,hz0,_,hrow,_⟩ := retained_geometry Rfreq
    (commonFrequencyGenerator C E) (nonunitFrequencyGenerator C E U) z
    (liveRows_weight C E U Rfreq rows z hz)
  have hη : 0<((ψ χ).modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le (ψ χ).modulus_ne_bot)
  have hτ : 0<(τ.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hF : 0<(fixedFactor:ℝ) := by exact_mod_cast fixedFactor_pos
  have hg := normValue_pos (commonFrequencyGenerator C E) hG
  have hv := normValue_pos (nonunitFrequencyGenerator C E U) hV
  have hN : ((ψ χ).modulus.absNorm:ℝ)≤
      ((τ.modulus.absNorm:ℝ)*(fixedFactor:ℝ)*((∏P∈U,P.val).absNorm:ℝ)*
        normValue (nonunitFrequencyGenerator C E U))*
          (ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ) := by
    dsimp only [normValue]
    exact_mod_cast (hψ.physical_budget t S β Rfreq rows₀ W K hK n hne χ).1
  have hprod : 0<
      ((τ.modulus.absNorm:ℝ)*(fixedFactor:ℝ)*((∏P∈U,P.val).absNorm:ℝ)*
        normValue (nonunitFrequencyGenerator C E U))*
          (ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ) := hη.trans_le hN
  have hcubic : 0<(ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ) := by
    have hc0 : 0≤(ReferenceCubicCharacter.conductorConstant*f.absNorm:ℝ) := by positivity
    rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge hc0) hneg.2)
  have hunit : 0<((∏P∈U,P.val).absNorm:ℝ) := by
    by_contra hnot
    have hzunit : ((∏P∈U,P.val).absNorm:ℝ)=0 :=
      le_antisymm (le_of_not_gt hnot) (Nat.cast_nonneg _)
    rw [hzunit,mul_zero,zero_mul,zero_mul] at hprod
    exact (lt_irrefl 0 hprod)
  have hlogN := Real.logb_le_logb_of_le hZ hη hN
  rw [Real.logb_mul (mul_pos (mul_pos (mul_pos hτ hF) hunit) hv).ne' hcubic.ne',
    Real.logb_mul (mul_pos (mul_pos hτ hF) hunit).ne' hv.ne',
    Real.logb_mul (mul_pos hτ hF).ne' hunit.ne',Real.logb_mul hτ.ne' hF.ne'] at hlogN
  have hlogrow := Real.logb_le_logb_of_le hZ (normValue_pos z hz0) hrow
  rw [Real.logb_div (mul_pos (by norm_num : (0:ℝ)<4) hR).ne' (mul_pos hg hv).ne',
    Real.logb_mul (by norm_num : (4:ℝ)≠0) hR.ne',Real.logb_mul hg.ne' hv.ne'] at hlogrow
  apply row_le_padded (ψ χ) Z Rdecl hZ z hz0
  unfold physicalWidth at hpaid
  rw [Real.logb_mul (by norm_num : (4:ℝ)≠0) hF.ne'] at hpaid
  linarith

/-- The same literal outer nonexceptional partition, indexed by the selected
product instead of a tuple representing it. No selected-dependent support is
used to choose the common labels or the dyadic row set. -/
def actualKeep (q : Data ι) (x : Frozen q) (τ : Character) (ξ χ : RayCharacter)
    (Q C E : Id) (U : Finset (CommonIndex C E)) (R : ℝ) (F : Id) (z : O) : Prop :=
  z∈sourceRows C E U R ∧
    ¬FixedInducingRow (childCharacter τ (ξ*χ)) Q fixedBadMask
      (oldMoving C E U*(primaryGenerator (frozenProduct q x))^2*(primaryGenerator F)^2) z

theorem actual_keep_selected (q : Data ι) (x : Frozen q) (y : Selected q)
    (τ : Character) (ξ χ : RayCharacter) (Q C E : Id)
    (U : Finset (CommonIndex C E)) (R : ℝ) (z : O) :
    actualKeep q x τ ξ χ Q C E U R (selectedProduct q y) z ↔
      z∈outerRows false q x y τ ξ χ Q C E U R := by
  simp only [actualKeep,outerRows,Finset.mem_filter,Bool.false_eq_true,ite_false]

theorem actual_keep_admission (q : Data ι) (x : Frozen q)
    (τ : Character) (ξ χ₀ χ₁ χ₂ : RayCharacter) (Q C E : Id)
    (hQ : Q≤Ideal.span {(72:O)}) (hC : Supported C) (hE : Supported E)
    (U : Finset (CommonIndex C E)) (ψ : RayCharacter→Character)
    (hψ : SharpFamily τ (frozenProduct q x) ξ C E hC hE U ψ)
    (R : ℝ) (F : Id) (hF : F∈selectedProducts q) (z : O)
    (hz : actualKeep q x τ ξ χ₀ Q C E U R F z) :
    z≠0 ∧ ¬FixedInducingRow (ψ χ₁) Q fixedBadMask ((primaryGenerator F)^2) z ∧
      ¬FixedInducingRow (ψ χ₂) Q fixedBadMask ((primaryGenerator F)^2) (-z) := by
  obtain ⟨y,hy,hyF⟩ := Finset.mem_image.mp hF
  subst F
  exact actual_outer_noninducing_rays q x y τ ξ χ₀ χ₁ χ₂ Q C E hQ hC hE U ψ hψ
    (selected_products_supported q _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩)) R z
    ((actual_keep_selected q x y τ ξ χ₀ Q C E U R z).mp hz)

/-- Reflection changes the physical row, not the character or the original
coefficient. Its finite sum is transported exactly. -/
private theorem sum_neg_image (rows : Finset O) (f : O→ℝ) :
    (∑z∈rows.image (fun z=>-z),f z)=∑z∈rows,f (-z) := by
  rw [Finset.sum_image]
  exact fun _ _ _ _ h=>neg_injective h

/-- An elementary weighted Cauchy inequality. It will only be used with
literal allocated windows and their already-proved source bounds. -/
private theorem weighted_pair_sq {α : Type*} (s : Finset α) (w f g : α→ℝ)
    (hw : ∀i∈s,0≤w i) :
    (∑i∈s,w i*f i*g i)^2≤(∑i∈s,w i*f i^2)*(∑i∈s,w i*g i^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i=>Real.sqrt (w i)*f i) (fun i=>Real.sqrt (w i)*g i)
  have hp (i : α) (hi : i∈s) :
      (Real.sqrt (w i)*f i)*(Real.sqrt (w i)*g i)=w i*f i*g i := by
    calc
      _=(Real.sqrt (w i))^2*f i*g i := by ring
      _=_ := by rw [Real.sq_sqrt (hw i hi)]
  have hf (i : α) (hi : i∈s) : (Real.sqrt (w i)*f i)^2=w i*f i^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i hi)]
  have hg (i : α) (hi : i∈s) : (Real.sqrt (w i)*g i)^2=w i*g i^2 := by
    rw [mul_pow,Real.sq_sqrt (hw i hi)]
  rw [Finset.sum_congr rfl hp,Finset.sum_congr rfl hf,Finset.sum_congr rfl hg] at hc
  exact hc

/-- Finite positive paired window, with one selected normalization. -/
def pairedWindowMass {α : Type*} [Fintype α] (q : Data α) (rows : Finset O)
    (keep : Id→O→Prop) (left right : Id→O→ℂ) : ℝ :=
  ∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    ∑z∈rows,if keep F.val z then ‖left F.val z‖*‖right F.val z‖ else 0

private theorem paired_window_sq {α : Type*} [Fintype α] (q : Data α)
    (hP : ∀i,0<q.P i)
    (rows : Finset O) (keep : Id→O→Prop) (left right : Id→O→ℂ) :
    pairedWindowMass q rows keep left right ^2≤
      (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
        ∑z∈rows,if keep F.val z then ‖left F.val z‖^2 else 0)*
      (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
        ∑z∈rows,if keep F.val z then ‖right F.val z‖^2 else 0) := by
  let weight := fun p : selectedProducts q × O =>
    if keep p.1.val p.2 then groupedWeight q p.1.val/MixedSelectedVolume.scale q else 0
  have hw (p : selectedProducts q × O) (_ : p∈Finset.univ×ˢrows) : 0≤weight p := by
    dsimp only [weight]
    split_ifs
    · exact div_nonneg (grouped_weight_nonneg q _) (MixedSelectedVolume.scale_pos q hP).le
    · exact le_rfl
  have he := weighted_pair_sq (Finset.univ×ˢrows) weight
    (fun p=>‖left p.1.val p.2‖) (fun p=>‖right p.1.val p.2‖) hw
  simpa only [Finset.sum_product,weight,pairedWindowMass,Finset.mul_sum,
    ite_mul,mul_ite,zero_mul,mul_zero,mul_assoc] using he

/-- The literal single-side RHS from `uniform_actual_allocated_window`.
The original residual normalization has already been restored by that theorem:
the live/original marked volume ratio and the enlarged ordinary prefix survive. -/
def allocationWindowCost {α : Type*} [Fintype α] (r : Source α a b)
    (G : Id) (Balloc : actualAllocations (tuplePools r) G)
    (C Kslot : ℝ) (N degree : ℕ) (control : Finset (ℕ×ℕ))
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (t₀ tp V θwin Z Rdecl ε : ℝ) (D : Id) : ℝ :=
  let c:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Balloc.val*
    frozenCoefficient Balloc.val G r.R r.ν r.Wslot r.P
  let E:=C*Kslot^(2*N)*(∏i : liveIndices Balloc.val,r.M i.val)^2*
    (sourceControl control r.W₁*sourceControl control r.W₂)^2*
    (height t₀ V r.t₁ r.t₂)^degree*heightCost tp θwin^(2*degree)*
    (∫v : ℝ,(1+‖v‖)^degree*‖columnDensity Vwin hVc hVs v‖)^2*
    (Z^Rdecl/fixedPresentationCost)*Z^ε
  (‖c‖^2*((∏i : liveIndices Balloc.val,r.P i.val)/(∏i,r.P i))*E)/
    (pairNorm (r.d.1*Balloc.val (Sum.inr 0),r.d.2*Balloc.val (Sum.inr 1))*(D.absNorm:ℝ))

private theorem normalized_pair
    (A a₁ a₂ L R P B₁ B₂ : ℝ)
    (hA : 0≤A) (ha₁ : 0≤a₁) (ha₂ : 0≤a₂)
    (hL : 0≤L) (hR : 0≤R) (hP : 0≤P)
    (hpair : P^2≤L*R)
    (hleft : A*a₁^2*L≤B₁) (hright : A*a₂^2*R≤B₂) :
    A*a₁*a₂*P≤Real.sqrt (B₁*B₂) := by
  have hl0 : 0≤A*a₁^2*L := mul_nonneg (mul_nonneg hA (sq_nonneg _)) hL
  have hr0 : 0≤A*a₂^2*R := mul_nonneg (mul_nonneg hA (sq_nonneg _)) hR
  have hb₁ : 0≤B₁ := hl0.trans hleft
  have hb₂ : 0≤B₂ := hr0.trans hright
  apply (Real.le_sqrt (by positivity) (mul_nonneg hb₁ hb₂)).mpr
  calc
    _=(A^2*a₁^2*a₂^2)*P^2 := by ring
    _≤(A^2*a₁^2*a₂^2)*(L*R) :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _=(A*a₁^2*L)*(A*a₂^2*R) := by ring
    _≤B₁*B₂ := mul_le_mul hleft hright hr0 hb₁

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

set_option maxHeartbeats 1200000 in
/-- Both actual allocated physical sides, with shared constants before the
moving source, supplier, common label and genuine allocations. The declared
width and the two strict scalar capacity gates are the only outstanding
numerical admissions. No analytic source/window estimate is assumed.

The retained row set is fixed before the selected product; the actual
nonexceptional predicate is allowed to depend on that product. The sole
nonzero witness may use its own actual selected-dependent partition. -/
theorem uniform_actual_paired_allocated_window
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl lo hi Kslot Bseed ε rho : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤Bwindow)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : Bwindow≤Lcap)
    (hslots : (N:ℝ)*Lslot+1≤Bwindow) (hCap : 2≤Cap)
    (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBdecl : 0≤Bdecl)
    (hdeclWindow : Bdecl+1≤Bwindow)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step:=budgetStep Bwindow Bseed ε rho
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)
      (t₀ tp V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s→
      (∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀cover : OriginalEnclosure s,∀u : Id,∀L : Finset ι,∀J : Finset {i // i∉Lᶜ},
    let q:=supplierData s ha u L J
    ∀x : Frozen q,MixedSupplierFourthRow.frozenWeight q x≠0→
    ∀seed : Id,Squarefree seed→u=frozenProduct q x*seed→
    ∀p : FixedLabel (fixedPool q x (residualSource s ha cover u L J x) seed),
    ∀(hC : Supported p.val.1)(hE : Supported p.val.2),
    ∀(τ : Character)(ξ χ₀ : RayCharacter)(U : Finset (CommonIndex p.val.1 p.val.2))
      (ψ : RayCharacter→Character),
      SharpFamily τ (frozenProduct q x) ξ p.val.1 p.val.2 hC hE U ψ→
    ∀(Rfreq : ℝ)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),0<K→∀n : Fin 4→ℤ,
    ∀y₀ : Selected q,
      physicalBlock τ tp (fixedPool q x (residualSource s ha cover u L J x) seed)
        (outerColumn q x y₀ seed ξ) p.val.1 p.val.2 hC hE U Rfreq
        (outerRows false q x y₀ τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq) Φ K n≠0→
    ∀Rdecl : ℝ,physicalWidth τ (frozenProduct q x) p.val.1 p.val.2 U Rfreq Z≤Rdecl→
      Rdecl≤Bdecl→
    let r:=unavoidedResidual s ha cover u L J x
    ∀Bleft : actualAllocations (tuplePools r) p.val.1,
    ∀Bright : actualAllocations (tuplePools r) p.val.2,
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    Real.logb Z (s.T/pairNorm (s.d.1*Bleft.val (Sum.inr 0),s.d.2*Bleft.val (Sum.inr 1)))+
      2*(∑i : liveIndices Bleft.val,w i.val.val.val)+4*d≤Rdecl-rho→
    (3/4:ℝ)*(∑i : liveIndices Bleft.val,w i.val.val.val)<d→
    Real.logb Z (s.T/pairNorm (s.d.1*Bright.val (Sum.inr 0),s.d.2*Bright.val (Sum.inr 1)))+
      2*(∑i : liveIndices Bright.val,w i.val.val.val)+4*d≤Rdecl-rho→
    (3/4:ℝ)*(∑i : liveIndices Bright.val,w i.val.val.val)<d→
    ∀D : Id,Squarefree D→(D.absNorm:ℝ)≤Z^Bseed→
    ∀(χleft χright : RayCharacter)(Xleft Xright θwin : ℝ),0<Xleft→0<Xright→
    let actualleft:=allocatedLiveSource (residualSource s ha cover u L J x)
      (zero_le_one.trans hb) cover p.val.1 Bleft
    let actualright:=allocatedLiveSource (residualSource s ha cover u L J x)
      (zero_le_one.trans hb) cover p.val.2 Bright
    let cleft:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Bleft.val*
      frozenCoefficient Bleft.val p.val.1 r.R (residualSource s ha cover u L J x).ν r.Wslot r.P
    let cright:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Bright.val*
      frozenCoefficient Bright.val p.val.2 r.R (residualSource s ha cover u L J x).ν r.Wslot r.P
    let rows:=dyadicRows (liveRows p.val.1 p.val.2 U Rfreq
      (sourceRows p.val.1 p.val.2 U Rfreq)) n
    let keep:=actualKeep q x τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq
    Z^step*‖normalization (r.X₁*r.X₂) r.P‖^2*‖cleft‖*‖cright‖*
      pairedWindowMass q rows keep
        (fun F z=>windowedPolynomial actualleft ha D F (ψ χleft) fixedBadMask 1
          tp Vwin Xleft θwin z)
        (fun F z=>windowedPolynomial actualright ha D F (ψ χright) fixedBadMask 1
          tp Vwin Xright (-θwin) (-z))≤
      Real.sqrt (
        allocationWindowCost r p.val.1 Bleft C Kslot N degree control Vwin hVc hVs
          t₀ tp V θwin Z Rdecl ε D *
        allocationWindowCost r p.val.2 Bright C Kslot N degree control Vwin hVc hVs
          t₀ tp V (-θwin) Z Rdecl ε D) := by
  dsimp only
  obtain ⟨degree,control,hbase⟩ := uniform_actual_allocated_window (ι:=ι) M Hray hHray
    Vwin hVc hVs N Holes hcard Wslot a b Lorig Bwindow Lslot Lcap Cap BR0 BH Bdecl
    lo hi Kslot Bseed ε rho hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap
    hslots hCap hCapc hBR0 hBH hBdecl hdeclWindow hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hCpos,hbase⟩ := hbase η₀ hη₀
  refine ⟨C,hCpos,?_⟩
  filter_upwards [hbase] with Z hbaseZ
  have hZ:=hbaseZ.1
  refine ⟨hZ,?_⟩
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx seed hseed hu p
    hC hE τ ξ χ₀ U ψ hψ Rfreq Φ K hK n y₀ hne Rdecl hpaid hcap
    Bleft Bright hmixedL hnativeL hmixedR hnativeR D hD hDcap χleft χright Xleft Xright θwin hXL hXR
  let q:=supplierData s ha u L J
  let r:=unavoidedResidual s ha cover u L J x
  let ra:=residualSource s ha cover u L J x
  let actualleft:=allocatedLiveSource ra (zero_le_one.trans hb) cover p.val.1 Bleft
  let actualright:=allocatedLiveSource ra (zero_le_one.trans hb) cover p.val.2 Bright
  let cleft:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Bleft.val*
    frozenCoefficient Bleft.val p.val.1 r.R ra.ν r.Wslot r.P
  let cright:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Bright.val*
    frozenCoefficient Bright.val p.val.2 r.R ra.ν r.Wslot r.P
  let rows:=dyadicRows (liveRows p.val.1 p.val.2 U Rfreq
    (sourceRows p.val.1 p.val.2 U Rfreq)) n
  let keep:=actualKeep q x τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq
  let left:=fun F z=>windowedPolynomial actualleft ha D F (ψ χleft) fixedBadMask 1 tp Vwin Xleft θwin z
  let right:=fun F z=>windowedPolynomial actualright ha D F (ψ χright) fixedBadMask 1 tp Vwin Xright (-θwin) (-z)
  let EL:=∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    ∑z∈rows,if keep F.val z then ‖left F.val z‖^2 else 0
  let ER:=∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    ∑z∈rows,if keep F.val z then ‖right F.val z‖^2 else 0
  let BL:=allocationWindowCost r p.val.1 Bleft C Kslot N degree control Vwin hVc hVs
    t₀ tp V θwin Z Rdecl ε D
  let BR:=allocationWindowCost r p.val.2 Bright C Kslot N degree control Vwin hVc hVs
    t₀ tp V (-θwin) Z Rdecl ε D
  have hadmit:=sharp_nonempty_window_caps τ (frozenProduct q x) ξ p.val.1 p.val.2 hC hE U ψ hψ
    tp (fixedPool q x ra seed) (outerColumn q x y₀ seed ξ) Rfreq
    (outerRows false q x y₀ τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq) Φ K hK n hne
    Z Rdecl Bdecl hZ hpaid hcap
  have hRcap : Rdecl≤Bwindow := by linarith
  have hall (χ : RayCharacter) (z : O) (hz : z∈rows) : normValue z≤paddedRadius (ψ χ) Z Rdecl :=
    sharp_any_live_row_padded τ (frozenProduct q x) ξ p.val.1 p.val.2 hC hE U ψ hψ
      tp (fixedPool q x ra seed) (outerColumn q x y₀ seed ξ) Rfreq
      (outerRows false q x y₀ τ ξ χ₀ Q p.val.1 p.val.2 U Rfreq) Φ K hK n hne
      Z Rdecl hZ hpaid χ (sourceRows p.val.1 p.val.2 U Rfreq) z
      (dyadicRows_subset _ n hz)
  have hkeep (F : Id) (hF : F∈selectedProducts q) (z : O) (hz : keep F z) :=
    actual_keep_admission q x τ ξ χ₀ χleft χright Q p.val.1 p.val.2 hQ72 hC hE U ψ hψ
      Rfreq F hF z hz
  have hm : fixedBadMask≠0 := fixedBadMask_ne_zero
  have hml : goodLambda∣fixedBadMask := dvd_mul_right _ _
  have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
  have hsource:=hbaseZ.2 θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀
    s hcanonical hMs hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx seed hseed hu p
  have hleft := hsource p.val.1 (Or.inl rfl) Bleft (ψ χleft) (hadmit.2.2 χleft).1
    Rdecl hadmit.1 hRcap χ₀ fixedBadMask hm hml hm2 hmixedL hnativeL keep
    (fun F hF z hz=>(hkeep F hF z hz).1)
    (fun F hF z hz=>(hkeep F hF z hz).2.1)
    D hD hDcap Xleft θwin hXL rows (hall χleft)
  have hright := hsource p.val.2 (Or.inr rfl) Bright (ψ χright) (hadmit.2.2 χright).1
    Rdecl hadmit.1 hRcap χ₀ fixedBadMask hm hml hm2 hmixedR hnativeR
    (fun F z=>keep F (-z))
    (by intro F hF z hz; exact neg_ne_zero.mp (hkeep F hF (-z) hz).1)
    (by intro F hF z hz; simpa only [neg_neg] using (hkeep F hF (-z) hz).2.2)
    D hD hDcap Xright (-θwin) hXR (rows.image (fun z=>-z))
    (by
      intro z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      simpa only [normValue,Ideal.span_singleton_neg] using hall χright v hv)
  have hleft' : Z^(budgetStep Bwindow Bseed ε rho)*
      ‖normalization (r.X₁*r.X₂) r.P‖^2*‖cleft‖^2*EL≤BL := by
    exact hleft
  have hreflection :
      (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
        ∑z∈rows.image (fun z=>-z),if keep F.val (-z) then
          ‖windowedPolynomial actualright ha D F.val (ψ χright) fixedBadMask 1 tp Vwin Xright (-θwin) z‖^2 else 0)=ER := by
    dsimp only [ER]
    apply Finset.sum_congr rfl
    intro F hF
    congr 1
    rw [sum_neg_image]
    simp only [right,neg_neg]
  have hright' : Z^(budgetStep Bwindow Bseed ε rho)*
      ‖normalization (r.X₁*r.X₂) r.P‖^2*‖cright‖^2*ER≤BR := by
    change Z^(budgetStep Bwindow Bseed ε rho)*
      ‖normalization (r.X₁*r.X₂) r.P‖^2*‖cright‖^2*
        (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
          ∑z∈rows.image (fun z=>-z),if keep F.val (-z) then
            ‖windowedPolynomial actualright ha D F.val (ψ χright) fixedBadMask 1 tp Vwin Xright (-θwin) z‖^2 else 0)≤BR at hright
    rw [hreflection] at hright
    exact hright
  have hP : ∀i,0<q.P i := fun i=>zero_lt_one.trans_le (s.hP i)
  have hweight (F : selectedProducts q) : 0≤groupedWeight q F.val/MixedSelectedVolume.scale q :=
    div_nonneg (grouped_weight_nonneg q F.val) (MixedSelectedVolume.scale_pos q hP).le
  have hEL : 0≤EL := by
    apply Finset.sum_nonneg
    intro F hF
    apply mul_nonneg (hweight F)
    exact Finset.sum_nonneg (fun z _=>by
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl)
  have hER : 0≤ER := by
    apply Finset.sum_nonneg
    intro F hF
    apply mul_nonneg (hweight F)
    exact Finset.sum_nonneg (fun z _=>by
      split_ifs
      · exact sq_nonneg _
      · exact le_rfl)
  have hPair : 0≤pairedWindowMass q rows keep left right := by
    apply Finset.sum_nonneg
    intro F hF
    apply mul_nonneg (hweight F)
    exact Finset.sum_nonneg (fun z _=>by
      split_ifs
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
      · exact le_rfl)
  exact normalized_pair
    (Z^(budgetStep Bwindow Bseed ε rho)*‖normalization (r.X₁*r.X₂) r.P‖^2)
    ‖cleft‖ ‖cright‖ EL ER (pairedWindowMass q rows keep left right) BL BR
    (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (sq_nonneg _))
    (norm_nonneg _) (norm_nonneg _) hEL hER hPair
    (paired_window_sq q hP rows keep left right) hleft' hright'

end
end Candidate.Feedback.FourthPower.OuterFreshPairedAllocatedWindow
