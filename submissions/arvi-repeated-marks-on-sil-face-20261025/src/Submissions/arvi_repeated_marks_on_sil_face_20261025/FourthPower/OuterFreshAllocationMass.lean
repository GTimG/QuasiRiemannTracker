/- Copyright (c) 2026 Sil. Apache-2.0.
The genuine-allocation scalar mass left by the actual paired window.
This file is pure finite normalization and divisor counting. It assumes no
energy estimate and retains the full common norm and ordinary prefix.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.OuterFreshPairedAllocatedWindow
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstNonexceptionalAllocation

set_option autoImplicit false
namespace Candidate.FourthPower.OuterFreshAllocationMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentFirstPhysicalSource
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentLogDyadic
open MixedPrincipalPair MixedPrincipalAllocations MixedCommonCoefficient
open MixedCommonRestriction MixedFirstLiveSource
open MixedCommonEnergy MixedLiveNormalization MixedSourceAssembly
open MixedFirstNonexceptionalAllocation MixedFirstSourceWindow MixedFirstChosenEnergy
open MixedFirstUniformLossBudget MixedFirstProfileEnvelope MixedSupplierFourthRow MixedSupplierSource
open MixedSupplierPositive
open OuterFreshSource OuterFreshSelectedWindow OuterFreshPairedAllocatedWindow
local notation "Id" => Ideal HeckeFamily.O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def scalar (r : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools r) G) : ℂ :=
  MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) B.val*
    frozenCoefficient B.val G r.R r.ν r.Wslot r.P

/-- Exactly the allocation-dependent part of allocationWindowCost. -/
def core (r : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools r) G) : ℝ :=
  ‖scalar r G B‖^2*((∏i : liveIndices B.val,r.P i.val)/(∏i,r.P i))*
    (∏i : liveIndices B.val,r.M i.val)^2/
    pairNorm (r.d.1*B.val (Sum.inr 0),r.d.2*B.val (Sum.inr 1))

theorem core_nonneg (r : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools r) G) : 0≤core r G B := by
  unfold core
  exact div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _)
      (div_nonneg (Finset.prod_nonneg (fun i _=>zero_le_one.trans (r.hP i.val)))
        (Finset.prod_nonneg (fun i _=>zero_le_one.trans (r.hP i))))) (sq_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- The live/original volume ratio supplies the single rawReduction
reciprocal. In particular the enlarged ordinary prefix is not discarded. -/
theorem core_eq_raw (r : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools r) G) :
    core r G B=(‖scalar r G B‖^2/rawReduction B.val r.P)*
      (∏i : liveIndices B.val,r.M i.val)^2/pairNorm r.d := by
  have hB := (allocation_data (tuplePools r) G B.val
    (Finset.mem_filter.mp B.property).1).1
  have hp : 0<∏i,r.P i := Finset.prod_pos (fun i _=>zero_lt_one.trans_le (r.hP i))
  have hr := rawReduction_pos B.val hB r.P (fun i=>zero_lt_one.trans_le (r.hP i))
  have hd := pairNorm_pos r.hd.1 r.hd.2
  have he := live_volume_ratio B.val hB r.d 1 r.P
    (fun i=>zero_lt_one.trans_le (r.hP i))
  simp only [one_mul] at he
  have hq : ((∏i : liveIndices B.val,r.P i.val)/(∏i,r.P i))/
      pairNorm (r.d.1*B.val (Sum.inr 0),r.d.2*B.val (Sum.inr 1))=
      1/(pairNorm r.d*rawReduction B.val r.P) := by
    calc
      _=((∏i : liveIndices B.val,r.P i.val)/
          pairNorm (r.d.1*B.val (Sum.inr 0),r.d.2*B.val (Sum.inr 1)))/(∏i,r.P i) := by ring
      _=(((∏i,r.P i)/pairNorm r.d)/rawReduction B.val r.P)/(∏i,r.P i) := by rw [he]
      _=_ := by field_simp [hp.ne',hr.ne',hd.ne']
  calc
    _=‖scalar r G B‖^2*(∏i : liveIndices B.val,r.M i.val)^2*
        (((∏i : liveIndices B.val,r.P i.val)/(∏i,r.P i))/
          pairNorm (r.d.1*B.val (Sum.inr 0),r.d.2*B.val (Sum.inr 1))) := by unfold core;ring
    _=_ := by rw [hq];ring

/-- A fixed profile multiplier. Its size may depend on the fixed slot
dimension and the fixed annular test; it contributes no new Z exponent. -/
def rootFactor (r : Source ι a b) : ℝ :=
  (∏i,r.M i)^4*(2:ℝ)^Fintype.card ι/pairNorm r.d

theorem rootFactor_nonneg (r : Source ι a b) : 0≤rootFactor r := by
  unfold rootFactor
  exact div_nonneg (mul_nonneg (by positivity) (by positivity))
    (pairNorm_pos r.hd.1 r.hd.2).le

/-- An actual allocation has the full 1/N(G) saving. A crude fixed
profile factor is used here rather than pretending that live factors vanish. -/
theorem core_le (r : Source ι a b) (G : Id) (hG : G≠0)
    (B : actualAllocations (tuplePools r) G) :
    core r G B≤rootFactor r/(G.absNorm:ℝ) := by
  have hB := (allocation_data (tuplePools r) G B.val
    (Finset.mem_filter.mp B.property).1).1
  have hprod := (Finset.mem_filter.mp B.property).2
  have hP : ∀i,0<r.P i := fun i=>zero_lt_one.trans_le (r.hP i)
  have hr := rawReduction_pos B.val hB r.P hP
  have hm := frozen_normalized_cost B.val hB G r.R hG hprod r.ν r.Wslot r.P r.M
    hP r.hν r.hWnorm r.hM 1 2 zero_lt_one r.hW
  rw [max_eq_right (by norm_num : (1:ℝ)≤2)] at hm
  have hs : ‖scalar r G B‖≤‖frozenCoefficient B.val G r.R r.ν r.Wslot r.P‖ :=
    frozen_scalar_norm_le (punctureProduct r.S r.H) B.val _
  have hs2 := div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hs 2) hr.le
  have hMprod : 0≤∏i,r.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (r.hM i))
  have hMlive : 0≤∏i : liveIndices B.val,r.M i.val :=
    Finset.prod_nonneg (fun i _=>zero_le_one.trans (r.hM i.val))
  have hlive : (∏i : liveIndices B.val,r.M i.val)≤∏i,r.M i :=
    injected_prod_le (fun i : liveIndices B.val=>i.val) Subtype.val_injective r.M r.hM
  have hbound := mul_le_mul (hs2.trans hm) (pow_le_pow_left₀ hMlive hlive 2)
    (sq_nonneg _) (by positivity)
  rw [core_eq_raw]
  apply (div_le_div_of_nonneg_right hbound (pairNorm_pos r.hd.1 r.hd.2).le).trans_eq
  unfold rootFactor
  ring

/-- One common scalar factor of the window budget, before division by
the artificial divisor. It keeps the original ordinary profile controls. -/
def windowEnvelope (r : Source ι a b) (C Kslot : ℝ) (N degree : ℕ)
    (control : Finset (ℕ×ℕ)) (Vwin : ℝ→ℂ)
    (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (t₀ tp V θwin Z Rdecl ε : ℝ) : ℝ :=
  C*Kslot^(2*N)*(sourceControl control r.W₁*sourceControl control r.W₂)^2*
    (height t₀ V r.t₁ r.t₂)^degree*heightCost tp θwin^(2*degree)*
    (∫v : ℝ,(1+‖v‖)^degree*‖columnDensity Vwin hVc hVs v‖)^2*
    (Z^Rdecl/fixedPresentationCost)*Z^ε

theorem allocationWindowCost_factored (r : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools r) G) (C Kslot : ℝ) (N degree : ℕ)
    (control : Finset (ℕ×ℕ)) (Vwin : ℝ→ℂ)
    (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (t₀ tp V θwin Z Rdecl ε : ℝ) (D : Id) :
    allocationWindowCost r G B C Kslot N degree control Vwin hVc hVs
      t₀ tp V θwin Z Rdecl ε D=
    core r G B*windowEnvelope r C Kslot N degree control Vwin hVc hVs
      t₀ tp V θwin Z Rdecl ε/(D.absNorm:ℝ) := by
  unfold allocationWindowCost core scalar windowEnvelope
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- A zero canonical frozen coefficient forces the actual avoided scalar
to vanish. RootAdmission need not supply capacity gates on this branch. -/
theorem actual_scalar_zero_of_canonical (s : Source ι a b) (ha : 0<a)
    (cover : OriginalEnclosure s) (u G : Id) (L : Finset ι)
    (J : Finset {i // i∉Lᶜ}) (x : Frozen (supplierData s ha u L J))
    (B : actualAllocations (tuplePools (unavoidedResidual s ha cover u L J x)) G)
    (hzero : frozenCoefficient B.val G (unavoidedResidual s ha cover u L J x).R
      (unavoidedResidual s ha cover u L J x).ν
      (unavoidedResidual s ha cover u L J x).Wslot
      (unavoidedResidual s ha cover u L J x).P=0) :
    scalar (residualSource s ha cover u L J x) G B=0 := by
  have he := actual_frozen_cost s ha cover u G L J x B
  dsimp only at he
  rw [hzero,mul_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] at he
  have hn : ‖scalar (residualSource s ha cover u L J x) G B‖=0 := by
    change ‖scalar (residualSource s ha cover u L J x) G B‖^2≤0 at he
    nlinarith [norm_nonneg (scalar (residualSource s ha cover u L J x) G B)]
  exact norm_eq_zero.mp hn

/-- Genuine allocation multiplicities cost only a subpower, uniformly
before the source. The left side is the exact squared sum of square-root
costs arising from the paired-window triangle inequality. -/
theorem uniform_sqrt_core_mass (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],Fintype.card ι≤N→
      ∀a b : ℝ,∀r : Source ι a b,∀G : Id,G≠0→
      (∑B : actualAllocations (tuplePools r) G,Real.sqrt (core r G B))^2≤
        C*(G.absNorm:ℝ)^δ*(rootFactor r/(G.absNorm:ℝ)) := by
  obtain ⟨C,hC,hcount⟩ := genuine_count_squared (N+2) δ hδ
  refine ⟨C,hC,?_⟩
  intro ι inst hn a b r G hG
  let A:=actualAllocations (tuplePools r) G
  have hg : 0<(G.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hG)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun B=>Real.sqrt (core r G B)) (fun _=>(1:ℝ))
  have hsqrt (B : A) : (Real.sqrt (core r G B))^2=core r G B :=
    Real.sq_sqrt (core_nonneg r G B)
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    hsqrt] at hc
  have hsum : (∑B : A,core r G B)≤(Fintype.card A:ℝ)*(rootFactor r/(G.absNorm:ℝ)) := by
    calc
      _≤∑_B : A,rootFactor r/(G.absNorm:ℝ) :=
        Finset.sum_le_sum (fun B _=>core_le r G hG B)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hdim : Fintype.card (ι⊕Fin 2)≤N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hn 2
  have hcard:=hcount hdim (tuplePools r) G hG
  have hfactor : 0≤rootFactor r/(G.absNorm:ℝ) := div_nonneg (rootFactor_nonneg r) hg.le
  calc
    _≤(∑B : A,core r G B)*(Fintype.card A:ℝ) := hc
    _≤((Fintype.card A:ℝ)*(rootFactor r/(G.absNorm:ℝ)))*(Fintype.card A:ℝ) :=
      mul_le_mul_of_nonneg_right hsum (Nat.cast_nonneg _)
    _=((actualAllocations (tuplePools r) G).card:ℝ)^2*(rootFactor r/(G.absNorm:ℝ)) := by
      simp only [A,Fintype.card_coe]
      ring
    _≤_ := mul_le_mul_of_nonneg_right hcard hfactor

/-- Both genuine sums are paid together; there is no separate cardinality
loss left over after this bound. Both full common ideals remain visible. -/
theorem uniform_pair_core_mass (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],Fintype.card ι≤N→
      ∀a b : ℝ,∀r : Source ι a b,∀G₁ G₂ : Id,G₁≠0→G₂≠0→
      (∑B₁ : actualAllocations (tuplePools r) G₁,
        ∑B₂ : actualAllocations (tuplePools r) G₂,
        Real.sqrt (core r G₁ B₁*core r G₂ B₂))^2≤
      (C*(G₁.absNorm:ℝ)^δ*(rootFactor r/(G₁.absNorm:ℝ)))*
        (C*(G₂.absNorm:ℝ)^δ*(rootFactor r/(G₂.absNorm:ℝ))) := by
  obtain ⟨C,hC,hside⟩ := uniform_sqrt_core_mass N δ hδ
  refine ⟨C,hC,?_⟩
  intro ι inst hn a b r G₁ G₂ hG₁ hG₂
  have h₁ := hside hn a b r G₁ hG₁
  have h₂ := hside hn a b r G₂ hG₂
  have hnonneg : 0≤C*(G₁.absNorm:ℝ)^δ*(rootFactor r/(G₁.absNorm:ℝ)) := by
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (div_nonneg (rootFactor_nonneg r) (Nat.cast_nonneg _))
  have hprod := mul_le_mul h₁ h₂ (sq_nonneg _) hnonneg
  have he : (∑B₁ : actualAllocations (tuplePools r) G₁,
      ∑B₂ : actualAllocations (tuplePools r) G₂,
      Real.sqrt (core r G₁ B₁*core r G₂ B₂))=
      (∑B₁ : actualAllocations (tuplePools r) G₁,Real.sqrt (core r G₁ B₁))*
        (∑B₂ : actualAllocations (tuplePools r) G₂,Real.sqrt (core r G₂ B₂)) := by
    have hsqrt (B₁ : actualAllocations (tuplePools r) G₁)
        (B₂ : actualAllocations (tuplePools r) G₂) :
        Real.sqrt (core r G₁ B₁*core r G₂ B₂)=
          Real.sqrt (core r G₁ B₁)*Real.sqrt (core r G₂ B₂) :=
      Real.sqrt_mul (core_nonneg r G₁ B₁) _
    simp_rw [hsqrt]
    simp only [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [he,mul_pow]
  exact hprod

/-- The artificial divisor occurs in both squared costs, hence only once
after the paired square root. This equality keeps its full norm; it is
not replaced by a square root of that norm or by a count of divisors. -/
theorem pair_cost_factor (r : Source ι a b) (G₁ G₂ : Id)
    (E₁ E₂ Dnorm : ℝ) (hE₁ : 0≤E₁) (hE₂ : 0≤E₂) (hD : 0<Dnorm) :
    (∑B₁ : actualAllocations (tuplePools r) G₁,
      ∑B₂ : actualAllocations (tuplePools r) G₂,
      Real.sqrt ((core r G₁ B₁*E₁/Dnorm)*(core r G₂ B₂*E₂/Dnorm)))=
      (∑B₁ : actualAllocations (tuplePools r) G₁,
        ∑B₂ : actualAllocations (tuplePools r) G₂,
        Real.sqrt (core r G₁ B₁*core r G₂ B₂))*Real.sqrt (E₁*E₂)/Dnorm := by
  have hpoint (B₁ : actualAllocations (tuplePools r) G₁)
      (B₂ : actualAllocations (tuplePools r) G₂) :
      Real.sqrt ((core r G₁ B₁*E₁/Dnorm)*(core r G₂ B₂*E₂/Dnorm))=
        Real.sqrt (core r G₁ B₁*core r G₂ B₂)*Real.sqrt (E₁*E₂)/Dnorm := by
    have he : (core r G₁ B₁*E₁/Dnorm)*(core r G₂ B₂*E₂/Dnorm)=
        ((core r G₁ B₁*core r G₂ B₂)*(E₁*E₂))/Dnorm^2 := by ring
    rw [he,Real.sqrt_div (mul_nonneg (mul_nonneg (core_nonneg r G₁ B₁)
      (core_nonneg r G₂ B₂)) (mul_nonneg hE₁ hE₂)),
      Real.sqrt_mul (mul_nonneg (core_nonneg r G₁ B₁) (core_nonneg r G₂ B₂)),
      Real.sqrt_sq_eq_abs,abs_of_pos hD]
  simp_rw [hpoint]
  simp only [Finset.sum_div,Finset.sum_mul]

private theorem exchange_four {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (rows : Finset δ)
    (w : α→ℝ) (f : α→δ→β→γ→ℝ) :
    (∑i,w i*∑z∈rows,∑j,∑k,f i z j k)=
      ∑j,∑k,∑i,w i*∑z∈rows,f i z j k := by
  simp_rw [Finset.mul_sum]
  calc
    _=∑i,∑j,∑k,∑z∈rows,w i*f i z j k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]

/-- The actual residual windows, with the selected-dependent keep,
expand into the genuine left/right allocation pairs BEFORE the analytic
estimate is applied. The right window has both -theta and -z. This is
an unconditional finite triangle inequality, not an energy hypothesis. -/
theorem residual_pair_le_allocations {κ : Type*} [Fintype κ]
    (q : Data κ) (hqP : ∀i,0<q.P i)
    (r : Source ι a b) (ha : 0<a) (hb : 0≤b) (cover : OriginalEnclosure r)
    (G₁ G₂ seed D : Id) (hG₁ : Supported G₁) (hG₂ : Supported G₂)
    (hs₁ : seed∣G₁) (hs₂ : seed∣G₂)
    (η₁ η₂ : Character) (t θ X₁ X₂ : ℝ)
    (rows : Finset HeckeFamily.O) (keep : Id→HeckeFamily.O→Prop) :
    pairedWindowMass q rows keep
      (fun F z=>residualWindow false r ha G₁ hG₁ seed D F η₁ t θ X₁ z)
      (fun F z=>residualWindow true r ha G₂ hG₂ seed D F η₂ t θ X₂ (-z))≤
    ∑B₁ : actualAllocations (tuplePools r) G₁,
      ∑B₂ : actualAllocations (tuplePools r) G₂,
      ‖scalar r G₁ B₁‖*‖scalar r G₂ B₂‖*
        pairedWindowMass q rows keep
          (fun F z=>windowedPolynomial (allocatedLiveSource r hb cover G₁ B₁) ha D F
            η₁ fixedBadMask 1 t logAnnulus X₁ θ z)
          (fun F z=>windowedPolynomial (allocatedLiveSource r hb cover G₂ B₂) ha D F
            η₂ fixedBadMask 1 t logAnnulus X₂ (-θ) (-z)) := by
  let A₁:=actualAllocations (tuplePools r) G₁
  let A₂:=actualAllocations (tuplePools r) G₂
  let left:=fun (B : A₁)(F : Id)(z : HeckeFamily.O)=>
    windowedPolynomial (allocatedLiveSource r hb cover G₁ B) ha D F
      η₁ fixedBadMask 1 t logAnnulus X₁ θ z
  let right:=fun (B : A₂)(F : Id)(z : HeckeFamily.O)=>
    windowedPolynomial (allocatedLiveSource r hb cover G₂ B) ha D F
      η₂ fixedBadMask 1 t logAnnulus X₂ (-θ) (-z)
  let w:=fun F : selectedProducts q=>groupedWeight q F.val/MixedSelectedVolume.scale q
  let f:=fun (F : selectedProducts q)(z : HeckeFamily.O)(B₁ : A₁)(B₂ : A₂)=>
    if keep F.val z then ‖scalar r G₁ B₁‖*‖scalar r G₂ B₂‖*
      (‖left B₁ F.val z‖*‖right B₂ F.val z‖) else 0
  have hw (F : selectedProducts q) : 0≤w F :=
    div_nonneg (MixedSupplierPositive.grouped_weight_nonneg q _)
      (MixedSelectedVolume.scale_pos q hqP).le
  have hleft (F : Id) (z : HeckeFamily.O) :
      residualWindow false r ha G₁ hG₁ seed D F η₁ t θ X₁ z=
        ∑B : A₁,scalar r G₁ B*left B F z := by
    simpa only [scalar,left,windowAngle,Bool.false_eq_true,ite_false] using
      residual_window_allocated false r ha hb cover G₁ seed D F hG₁ hs₁ η₁ t θ X₁ z
  have hright (F : Id) (z : HeckeFamily.O) :
      residualWindow true r ha G₂ hG₂ seed D F η₂ t θ X₂ (-z)=
        ∑B : A₂,scalar r G₂ B*right B F z := by
    simpa only [scalar,right,windowAngle,ite_true] using
      residual_window_allocated true r ha hb cover G₂ seed D F hG₂ hs₂ η₂ t θ X₂ (-z)
  have hpoint (F : Id) (z : HeckeFamily.O) :
      ‖residualWindow false r ha G₁ hG₁ seed D F η₁ t θ X₁ z‖*
        ‖residualWindow true r ha G₂ hG₂ seed D F η₂ t θ X₂ (-z)‖≤
      ∑B₁ : A₁,∑B₂ : A₂,‖scalar r G₁ B₁‖*‖scalar r G₂ B₂‖*
        (‖left B₁ F z‖*‖right B₂ F z‖) := by
    rw [hleft,hright]
    apply (mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).trans_eq
    simp only [norm_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro B₁ hB₁
    apply Finset.sum_congr rfl
    intro B₂ hB₂
    ring
  calc
    _≤∑F : selectedProducts q,w F*∑z∈rows,∑B₁ : A₁,∑B₂ : A₂,f F z B₁ B₂ := by
      apply Finset.sum_le_sum
      intro F hF
      apply mul_le_mul_of_nonneg_left _ (hw F)
      apply Finset.sum_le_sum
      intro z hz
      by_cases hk : keep F.val z
      · simpa only [hk,ite_true,f] using hpoint F.val z
      · simp only [hk,ite_false,f,Finset.sum_const_zero,le_refl]
    _=∑B₁ : A₁,∑B₂ : A₂,∑F : selectedProducts q,w F*∑z∈rows,f F z B₁ B₂ :=
      exchange_four rows w f
    _=_ := by
      apply Finset.sum_congr rfl
      intro B₁ hB₁
      apply Finset.sum_congr rfl
      intro B₂ hB₂
      simp only [pairedWindowMass,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hk : keep F.val z
      · simp only [f,hk,ite_true,w,left,right]
        ring
      · simp only [f,hk,ite_false,mul_zero]

end
end Candidate.FourthPower.OuterFreshAllocationMass
