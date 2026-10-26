/- Copyright (c) 2026 Sil. Apache-2.0.
Actual frozen-supplier counting for RAW first-child energy.
The residual seed is replaced by the ORIGINAL artificial divisor only via
u=frozenProduct*seed; its full norm saving is retained. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedRawReference

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedRawSupplier
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedSupplierFourthRow MixedSupplierPositive
open MixedSupplierSource MixedSupplierOuterActive
open OuterFreshSource OuterFreshSelected OuterFreshCutoffAllowance OuterFreshSelectedWindow
open RepairedRawReference OuterFreshAllocationMass
open MixedSelectedVolume
local notation "Id" => Ideal HeckeFamily.O
local instance {α:Type*} : DecidableEq α := Classical.decEq _
variable {α:Type u}[Fintype α]{a b:ℝ}

def activeFrozen (q:Data α) : Finset (Frozen q) :=
  Finset.univ.filter (fun x=>Function.Injective x ∧ MixedSupplierFourthRow.frozenWeight q x≠0)

def residualSeed (q:Data α)(x:activeFrozen q) : Id :=
  Classical.choose (frozen_divides q x.val (Finset.mem_filter.mp x.property).2.1
    (Finset.mem_filter.mp x.property).2.2)

theorem residualSeed_spec (q:Data α)(x:activeFrozen q) :
    q.u=frozenProduct q x.val*residualSeed q x :=
  Classical.choose_spec (frozen_divides q x.val (Finset.mem_filter.mp x.property).2.1
    (Finset.mem_filter.mp x.property).2.2)

theorem residualSeed_unique (q:Data α)(x:activeFrozen q)(seed:Id)
    (h:q.u=frozenProduct q x.val*seed) : seed=residualSeed q x :=
  mul_left_cancel₀ (frozen_nonzero q x.val) (h.symm.trans (residualSeed_spec q x))

theorem residualSeed_squarefree (q:Data α)(hu:Squarefree q.u)(x:activeFrozen q) :
    Squarefree (residualSeed q x) := by
  have hd:residualSeed q x∣q.u:=by
    rw [residualSeed_spec q x]
    exact dvd_mul_left _ _
  intro I hI
  exact hu I (hI.trans hd)

theorem active_frozen_card (q:Data α)(hu:q.u≠0) :
    (activeFrozen q).card≤(IdealMobiusDivisorSum.idealDivisors q.u).card^(Fintype.card ↥q.Lᶜ) := by
  let e (x:activeFrozen q) : ↥q.Lᶜ→IdealMobiusDivisorSum.idealDivisors q.u := fun i=>
    ⟨(x.val i).val,by
      apply (IdealMobiusDivisorSum.mem_idealDivisors hu).mpr
      have hx:=frozen_divides q x.val (Finset.mem_filter.mp x.property).2.1
        (Finset.mem_filter.mp x.property).2.2
      exact (Finset.dvd_prod_of_mem (fun j:↥q.Lᶜ=>(x.val j).val) (Finset.mem_univ i)).trans hx⟩
  have he:Function.Injective e:=by
    intro x y h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrArg (fun v:IdealMobiusDivisorSum.idealDivisors q.u=>(v:Id)) (congrFun h i)
  simpa only [Fintype.card_coe,Fintype.card_fun] using Fintype.card_le_of_injective e he

/-- The same count constant works for every actual first live subtype,
supplier partition and original artificial divisor. -/
theorem uniform_frozen_count (N:ℕ)(δ:ℝ)(hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀{α:Type u}[Fintype α],Fintype.card α≤N→
      ∀q:Data α,q.u≠0→((activeFrozen q).card:ℝ)≤C*(q.u.absNorm:ℝ)^δ := by
  let e:=δ/((N:ℝ)+1)
  have he:0<e:=by unfold e;positivity
  obtain ⟨C,hC,hdiv⟩:=IdealDivisorBound.ideal_divisor_small_power e he
  refine ⟨(1+C)^N,pow_pos (by linarith) _,?_⟩
  intro α inst hcard q hu
  have hN:1≤(q.u.absNorm:ℝ):=ideal_norm_one_le hu
  have hdim:Fintype.card ↥q.Lᶜ≤N:=
    (Fintype.card_le_of_injective (fun i:↥q.Lᶜ=>i.val) Subtype.val_injective).trans hcard
  have hpow:1≤(q.u.absNorm:ℝ)^e:=Real.one_le_rpow hN he.le
  have hb:1≤(1+C)*(q.u.absNorm:ℝ)^e:=by nlinarith
  have hexp:e*(N:ℝ)≤δ:=by
    have hh:e*((N:ℝ)+1)=δ:=by unfold e;field_simp
    nlinarith
  calc
    _≤((IdealMobiusDivisorSum.idealDivisors q.u).card:ℝ)^(Fintype.card ↥q.Lᶜ):=by
      exact_mod_cast active_frozen_card q hu
    _≤((1+C)*(q.u.absNorm:ℝ)^e)^(Fintype.card ↥q.Lᶜ):=by
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      exact (hdiv q.u hu).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    _≤((1+C)*(q.u.absNorm:ℝ)^e)^N:=pow_le_pow_right₀ hb hdim
    _=(1+C)^N*(q.u.absNorm:ℝ)^(e*(N:ℝ)):=by
      rw [mul_pow,←Real.rpow_natCast ((q.u.absNorm:ℝ)^e) N,←Real.rpow_mul (zero_le_one.trans hN)]
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN hexp) (by positivity)

theorem selected_card_scale (q:Data α)(N:ℕ)(hcard:Fintype.card α≤N)
    (hP:∀i,0<q.P i)(hpool:∀i,∀I∈q.pool i,(I.absNorm:ℝ)≤2*q.P i) :
    ((activeSelected q).card:ℝ)*scale q≤(512:ℝ)^N*(selectedVolume q)^2 := by
  have hc:=active_selected_annular_card q (fun i=>(hP i).le) hpool
  have hj:Fintype.card q.J≤N:=(selected_card_le q).trans hcard
  calc
    _≤((256:ℝ)^(Fintype.card q.J)*selectedVolume q)*scale q:=
      mul_le_mul_of_nonneg_right hc (scale_pos q hP).le
    _=((256:ℝ)^(Fintype.card q.J)*(2:ℝ)^(Fintype.card q.J))*(selectedVolume q)^2:=by
      unfold scale padding volume selectedVolume
      ring
    _=(512:ℝ)^(Fintype.card q.J)*(selectedVolume q)^2:=by rw [←mul_pow];norm_num
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) (sq_nonneg _)

/-- This is the exact scalar multiplying the first reference after
reconstructing original source normalization and selected Cauchy. -/
def rawSupplierCost (q:Data α)(x:Frozen q)(seed:Id) : ℝ :=
  (‖MixedSupplierFourthRow.frozenWeight q x‖^2*256*((activeSelected q).card:ℝ)*scale q)/
    (frozenVolume q*(selectedVolume q)^2*(seed.absNorm:ℝ))

theorem rawSupplierCost_nonneg (q:Data α)(hP:∀i,0<q.P i)(x:Frozen q)(seed:Id) :
    0≤rawSupplierCost q x seed := by
  have hs:0<scale q:=scale_pos q hP
  have hf:0<frozenVolume q:=frozenVolume_pos q hP
  have hv:0<selectedVolume q:=OuterFreshSelected.selectedVolume_pos q hP
  unfold rawSupplierCost
  positivity

/-- Exact RAW scalar: no residual/source-volume ratio is present. -/
private theorem raw_supplier_scalar (F0 A S P D f s u J T M:ℝ)
    (hF0:0≤F0)(hAS:0≤A*S)(hP:1≤P)(hD:1≤D)(hf:0<f)(hs:0<s)(hu:u=f*s)
    (hJ:0≤J)(hT:0≤T)(hM:0≤M)
    (hcount:A*S≤J*D^2)(hweight:F0≤M)(hfrozen:f≤T*P) :
    F0*256*A*S/(P*D^2*s)≤256*J*T*M/u := by
  have hp:0<P:=zero_lt_one.trans_le hP
  have hd:0<D:=zero_lt_one.trans_le hD
  have hu0:0<u:=hu.symm ▸ mul_pos hf hs
  have hmul:F0*(A*S)*f≤M*(J*D^2)*(T*P):=
    mul_le_mul (mul_le_mul hweight hcount hAS hM) hfrozen hf.le
      (mul_nonneg hM (mul_nonneg hJ (sq_nonneg _)))
  calc
    _=256*(F0*(A*S)*f)/(P*D^2*u):=by
      rw [hu]
      field_simp [hp.ne',hd.ne',hf.ne',hs.ne']
      <;> ring
    _≤256*(M*(J*D^2)*(T*P))/(P*D^2*u):=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by norm_num)) (by positivity)
    _=_:=by field_simp [hp.ne',hd.ne',hu0.ne'] <;> ring
theorem actual_raw_supplier_cost (s:Source α a b)(ha:0<a)(u:Id)(L:Finset α)(J:Finset {i//i∉Lᶜ})
    (N:ℕ)(hcard:Fintype.card α≤N)(Kslot:ℝ)(hK:1≤Kslot)(hM:∀i,s.M i≤Kslot)
    (x:Frozen (supplierData s ha u L J))(hx:MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x≠0)
    (seed:Id)(hs:seed≠0)(hu:u=frozenProduct (supplierData s ha u L J) x*seed) :
    rawSupplierCost (supplierData s ha u L J) x seed≤
      (256*(512:ℝ)^N*(2:ℝ)^N*Kslot^(2*N))/(u.absNorm:ℝ) := by
  let q:=supplierData s ha u L J
  have hP:∀i,0<q.P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have hPF:1≤frozenVolume q:=Finset.one_le_prod₀ (fun i _=>s.hP i.val)
  have hPD:1≤selectedVolume q:=Finset.one_le_prod₀ (fun i _=>s.hP i.val.val)
  have hdim:Fintype.card ↥Lᶜ≤N:=
    (Fintype.card_le_of_injective (fun i:↥Lᶜ=>i.val) Subtype.val_injective).trans hcard
  have hfw:‖MixedSupplierFourthRow.frozenWeight q x‖≤Kslot^N := by
    have hh:=frozen_weight_norm q x (fun _=>Kslot) (fun _=>zero_le_one.trans hK)
      (fun i I _=>s.hν i I) (fun i z=>(s.hWnorm i z).trans (hM i))
    apply hh.trans
    simp only [Finset.prod_const,Finset.card_univ]
    exact pow_le_pow_right₀ hK hdim
  have hfw2:‖MixedSupplierFourthRow.frozenWeight q x‖^2≤Kslot^(2*N) := by
    apply (pow_le_pow_left₀ (norm_nonneg _) hfw 2).trans_eq
    rw [←pow_mul]
    congr 1
    omega
  have hfn:((frozenProduct q x).absNorm:ℝ)≤(2:ℝ)^N*frozenVolume q :=
    (actual_frozen_window s ha u L J x hx).2.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hdim) (zero_le_one.trans hPF))
  have hprod:(u.absNorm:ℝ)=((frozenProduct q x).absNorm:ℝ)*(seed.absNorm:ℝ):=by
    rw [hu]
    simp only [map_mul,Nat.cast_mul]
    rfl
  have hcount:=selected_card_scale q N hcard hP (fun i I hI=>(s.hpn i I hI).2)
  exact raw_supplier_scalar _ _ _ _ _ _ _ _ _ _ _ (sq_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (scale_pos q hP).le) hPF hPD
    (zero_lt_one.trans_le (ideal_norm_one_le (frozen_nonzero q x)))
    (zero_lt_one.trans_le (ideal_norm_one_le hs)) hprod
    (by positivity) (by positivity) (by positivity) hcount hfw2 hfn

/-- Complete frozen-assignment sum, with residual seed chosen before all
characters/heights. The remaining norm is the ORIGINAL first divisor u. -/
theorem uniform_raw_supplier_mass (N:ℕ)(δ:ℝ)(hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀{α:Type u}[Fintype α],Fintype.card α≤N→
      ∀a b:ℝ,∀s:Source α a b,∀ha:0<a,∀u:Id,Squarefree u→
      ∀(L:Finset α)(J:Finset {i//i∉Lᶜ})(Kslot:ℝ),1≤Kslot→(∀i,s.M i≤Kslot)→
      let q:=supplierData s ha u L J
      (∑x:activeFrozen q,rawSupplierCost q x.val (residualSeed q x))≤
        C*Kslot^(2*N)*(u.absNorm:ℝ)^δ/(u.absNorm:ℝ) := by
  obtain ⟨Cc,hCc,hcount⟩:=uniform_frozen_count N δ hδ
  refine ⟨Cc*(256*(512:ℝ)^N*(2:ℝ)^N),mul_pos hCc (by positivity),?_⟩
  intro α inst hcard a b s ha u hu L J Kslot hK hM
  let q:=supplierData s ha u L J
  have hu0:u≠0:=hu.ne_zero
  have hc:=hcount hcard q hu0
  have ht (x:activeFrozen q):rawSupplierCost q x.val (residualSeed q x)≤
      (256*(512:ℝ)^N*(2:ℝ)^N*Kslot^(2*N))/(u.absNorm:ℝ) :=
    actual_raw_supplier_cost s ha u L J N hcard Kslot hK hM x.val
      (Finset.mem_filter.mp x.property).2.2 _ (residualSeed_squarefree q hu x).ne_zero
      (residualSeed_spec q x)
  have hterm0:0≤(256*(512:ℝ)^N*(2:ℝ)^N*Kslot^(2*N))/(u.absNorm:ℝ):=by positivity
  calc
    _≤∑_x:activeFrozen q,(256*(512:ℝ)^N*(2:ℝ)^N*Kslot^(2*N))/(u.absNorm:ℝ):=
      Finset.sum_le_sum (fun x _=>ht x)
    _=((activeFrozen q).card:ℝ)*((256*(512:ℝ)^N*(2:ℝ)^N*Kslot^(2*N))/(u.absNorm:ℝ)) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    _≤(Cc*(u.absNorm:ℝ)^δ)*((256*(512:ℝ)^N*(2:ℝ)^N*Kslot^(2*N))/(u.absNorm:ℝ)):=
      mul_le_mul_of_nonneg_right hc hterm0
    _=_:=by ring

abbrev SupplierIndex (s:Source α a b)(ha:0<a)(u:Id)
    (J:(L:Finset α)→Finset {i//i∉Lᶜ}) :=
  (L:Finset α) × activeFrozen (supplierData s ha u L (J L))

/-- The full outer Cauchy count is included here, in addition to the
sum of frozen scalar costs. Both subpower exponents are paid together.
Thus callers must not introduce an additional unaccounted supplier count. -/
theorem uniform_raw_supplier_cauchy_mass (N:ℕ)(δ:ℝ)(hδ:0<δ) :
    ∃C:ℝ,0<C ∧ ∀{α:Type u}[Fintype α],Fintype.card α≤N→
      ∀a b:ℝ,∀s:Source α a b,∀ha:0<a,∀u:Id,Squarefree u→
      ∀J:(L:Finset α)→Finset {i//i∉Lᶜ},∀Kslot:ℝ,1≤Kslot→(∀i,s.M i≤Kslot)→
      (Fintype.card (SupplierIndex s ha u J):ℝ)*
        (∑L:Finset α,∑x:activeFrozen (supplierData s ha u L (J L)),
          rawSupplierCost (supplierData s ha u L (J L)) x.val
            (residualSeed (supplierData s ha u L (J L)) x))≤
      C*Kslot^(2*N)*(u.absNorm:ℝ)^δ/(u.absNorm:ℝ) := by
  obtain ⟨Cc,hCc,hcount⟩:=uniform_frozen_count N (δ/2) (half_pos hδ)
  obtain ⟨Cm,hCm,hmass⟩:=uniform_raw_supplier_mass N (δ/2) (half_pos hδ)
  refine ⟨((2:ℝ)^N)^2*Cc*Cm,by positivity,?_⟩
  intro α inst hcard a b s ha u hu J Kslot hK hM
  have hNu:0<(u.absNorm:ℝ):=zero_lt_one.trans_le (ideal_norm_one_le hu.ne_zero)
  have hshape:(Fintype.card (Finset α):ℝ)≤(2:ℝ)^N := by
    simp only [Fintype.card_finset,Nat.cast_pow,Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) hcard
  have hcountEq:(Fintype.card (SupplierIndex s ha u J):ℝ)=
      ∑L:Finset α,((activeFrozen (supplierData s ha u L (J L))).card:ℝ) := by
    simp only [SupplierIndex,Fintype.card_sigma,Fintype.card_coe,Nat.cast_sum]
  have htotal:(Fintype.card (SupplierIndex s ha u J):ℝ)≤(2:ℝ)^N*(Cc*(u.absNorm:ℝ)^(δ/2)) := by
    rw [hcountEq]
    calc
      _≤∑_L:Finset α,Cc*(u.absNorm:ℝ)^(δ/2):=
        Finset.sum_le_sum (fun L _=>hcount hcard (supplierData s ha u L (J L)) hu.ne_zero)
      _=(Fintype.card (Finset α):ℝ)*(Cc*(u.absNorm:ℝ)^(δ/2)):=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _≤_:=mul_le_mul_of_nonneg_right hshape (mul_nonneg hCc.le (Real.rpow_nonneg hNu.le _))
  have hsum:(∑L:Finset α,∑x:activeFrozen (supplierData s ha u L (J L)),
      rawSupplierCost (supplierData s ha u L (J L)) x.val
        (residualSeed (supplierData s ha u L (J L)) x))≤
      (2:ℝ)^N*(Cm*Kslot^(2*N)*(u.absNorm:ℝ)^(δ/2)/(u.absNorm:ℝ)) := by
    calc
      _≤∑_L:Finset α,Cm*Kslot^(2*N)*(u.absNorm:ℝ)^(δ/2)/(u.absNorm:ℝ):=
        Finset.sum_le_sum (fun L _=>hmass hcard a b s ha u hu L (J L) Kslot hK hM)
      _=(Fintype.card (Finset α):ℝ)*(Cm*Kslot^(2*N)*(u.absNorm:ℝ)^(δ/2)/(u.absNorm:ℝ)):=by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _≤_:=mul_le_mul_of_nonneg_right hshape (by positivity)
  have hsum0:0≤∑L:Finset α,∑x:activeFrozen (supplierData s ha u L (J L)),
      rawSupplierCost (supplierData s ha u L (J L)) x.val
        (residualSeed (supplierData s ha u L (J L)) x) :=
    Finset.sum_nonneg (fun L _=>Finset.sum_nonneg (fun x _=>
      rawSupplierCost_nonneg _ (fun i=>zero_lt_one.trans_le (s.hP i)) _ _))
  have hm:=mul_le_mul htotal hsum hsum0 (by positivity)
  apply hm.trans_eq
  have hp:(u.absNorm:ℝ)^(δ/2)*(u.absNorm:ℝ)^(δ/2)=(u.absNorm:ℝ)^δ:=by
    rw [←Real.rpow_add hNu,add_halves]
  calc
    _=(((2:ℝ)^N)^2*Cc*Cm)*Kslot^(2*N)*
        ((u.absNorm:ℝ)^(δ/2)*(u.absNorm:ℝ)^(δ/2))/(u.absNorm:ℝ):=by ring
    _=_:=by rw [hp]

/-- Exact first-reference factorization at the raw boundary. -/
theorem firstReference_factored (q:Data α)(τ:HeckeFamily.Character)(C:Id)(V:ℝ) :
    firstReference q τ C V=referenceBase τ C V/(frozenVolume q*(selectedVolume q)^2) := by
  unfold firstReference referenceBase
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The actual selected Cauchy/cardinality and padded scale are present.
There is NO sourceVolume(residual)/sourceVolume(first) factor here. -/
theorem raw_supplier_reference_identity (q:Data α)(x:Frozen q)(seed:Id)
    (τ:HeckeFamily.Character)(C:Id)(V:ℝ) :
    (‖MixedSupplierFourthRow.frozenWeight q x‖^2*(256*((activeSelected q).card:ℝ)))*
      (MixedSelectedVolume.scale q*firstReference q τ C V/(seed.absNorm:ℝ))=
      referenceBase τ C V*rawSupplierCost q x seed := by
  rw [firstReference_factored]
  unfold rawSupplierCost
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The profile numerator remaining after sharp support cancellation is
uniform over residual subsets. No volume or prefix is hidden in this bound. -/
theorem residual_rawProfileRoot (s:Source α a b)(ha:0<a)(cover:OriginalEnclosure s)
    (u:Id)(L:Finset α)(J:Finset {i//i∉Lᶜ})(x:Frozen (supplierData s ha u L J))
    (N:ℕ)(hcard:Fintype.card α≤N)(Kslot:ℝ)(hK:1≤Kslot)(hM:∀i,s.M i≤Kslot) :
    rawProfileRoot (unavoidedResidual s ha cover u L J x)≤Kslot^(4*N)*(2:ℝ)^N/a^2 := by
  let q:=supplierData s ha u L J
  let r:=unavoidedResidual s ha cover u L J x
  have hdim:Fintype.card (RestIndex q)≤N:=(rest_card_le q).trans hcard
  have hprod:(∏i:RestIndex q,r.M i)≤Kslot^N := by
    calc
      _≤∏_i:RestIndex q,Kslot:=Finset.prod_le_prod₀
        (fun i _=>zero_le_one.trans (r.hM i)) (fun i _=>hM i.val.val)
      _=Kslot^(Fintype.card (RestIndex q)):=by simp only [Finset.prod_const,Finset.card_univ]
      _≤_:=pow_le_pow_right₀ hK hdim
  have hp4:(∏i:RestIndex q,r.M i)^4≤Kslot^(4*N) := by
    apply (pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=>zero_le_one.trans (r.hM i))) hprod 4).trans_eq
    rw [←pow_mul]
    congr 1
    omega
  have hpow:(2:ℝ)^Fintype.card (RestIndex q)≤2^N:=pow_le_pow_right₀ (by norm_num) hdim
  unfold rawProfileRoot
  exact div_le_div_of_nonneg_right (mul_le_mul hp4 hpow (by positivity) (by positivity)) (sq_nonneg a)

theorem residual_profileCore (s:Source α a b)(ha:0<a)(cover:OriginalEnclosure s)
    (u:Id)(L:Finset α)(J:Finset {i//i∉Lᶜ})(x:Frozen (supplierData s ha u L J))
    (Kslot:ℝ)(N degree:ℕ)(control:Finset (ℕ×ℕ))(t₀ tp V:ℝ) :
    profileCore (unavoidedResidual s ha cover u L J x) Kslot N degree control t₀ tp V=
      profileCore s Kslot N degree control t₀ tp V := rfl

end
end Candidate.FourthPower.RepairedRawSupplier

