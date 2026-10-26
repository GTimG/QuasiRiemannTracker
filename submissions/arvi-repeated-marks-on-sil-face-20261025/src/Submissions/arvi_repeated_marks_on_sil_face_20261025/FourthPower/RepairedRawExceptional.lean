/- Copyright (c) 2026 Sil. Apache-2.0.
RAW exceptional supplier geometry and genuine first-allocation reference.
The original Source.L is unrestricted; in the repaired root it equals Z^ell.
All powers of selected volume are cancelled before the first raw consumer.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedGroupedExceptional
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedRawSupplier
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstExceptionalNormalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedRawExceptional
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion ActualEisensteinCubic
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentSectorLocalization CenteredMomentCanonicalFirst CenteredMomentCommonProfile
open CenteredMomentFirstScale
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalCentered MixedPrincipalWindow
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger MixedFirstExceptionalNormalization
open MixedFirstGeometricCaps MixedFirstChosenEnergy
open OuterFreshSource OuterFreshSelected OuterFreshSelectedWindow OuterFreshCutoffAllowance
open RepairedRawReference RepairedRawSupplier
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ:=Classical.decEq _
variable {ι:Type u}[Fintype ι]{a b:ℝ}

/-- One exact residual/source volume identity. It contains no ordinary
prefix cancellation, since the prefix is unchanged by supplier selection. -/
theorem residual_volume_partition (s:Source ι a b)(ha:0<a)(cover:OriginalEnclosure s)
    (u:Id)(L:Finset ι)(J:Finset {i//i∉Lᶜ})(x:Frozen (supplierData s ha u L J)) :
    let q:=supplierData s ha u L J
    sourceVolume (residualSource s ha cover u L J x)*frozenVolume q*selectedVolume q=sourceVolume s := by
  let q:=supplierData s ha u L J
  have hp:=volume_partition q
  change (∏i,s.P i)=frozenVolume q*selectedVolume q*(∏j:RestIndex q,s.P j.val.val) at hp
  change (s.X₁*s.X₂*(∏j:RestIndex q,s.P j.val.val))*frozenVolume q*selectedVolume q=
    s.X₁*s.X₂*(∏i,s.P i)
  rw [hp]
  ring

/-- W from grouped averaging and W from selected Cauchy are BOTH here.
They cancel against the residual volume, leaving the old shape at W=1. -/
theorem raw_selected_geometry (s:Source ι a b)(ha:0<a)(cover:OriginalEnclosure s)
    (u:Id)(L:Finset ι)(J:Finset {i//i∉Lᶜ})(x:Frozen (supplierData s ha u L J))
    (K:ℝ)(hK:0<K) :
    let q:=supplierData s ha u L J
    let r:=residualSource s ha cover u L J x
    (selectedVolume q)^2*sourceVolume r*commonPhysicalCost r K/
      ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ))=
    a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1/
      (frozenVolume q)^(4/3:ℝ) := by
  let q:=supplierData s ha u L J
  let r:=residualSource s ha cover u L J x
  have hP:∀i,0<q.P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have hf:=frozenVolume_pos q hP
  have hw:=selectedVolume_pos q hP
  have hv:=sourceVolume_pos r
  have hs:=sourceVolume_pos s
  have hp:=pairNorm_pos s.hd.1 s.hd.2
  have hh:=prefixNormMax_pos s.d s.hd
  have hl:=s.hL
  have hvol:=residual_volume_partition s ha cover u L J x
  have hlog:=congrArg Real.log hvol
  rw [Real.log_mul (mul_pos hv hf).ne' hw.ne',Real.log_mul hv.ne' hf.ne'] at hlog
  change (selectedVolume q)^2*sourceVolume r*
    ((sourceVolume r)^(1/3:ℝ)*K^(5/6:ℝ)*(a^2/pairNorm s.d)^(-2/3:ℝ)*
      (s.L/prefixNormMax s.d)^(-2/3:ℝ))/
      ((pairNorm s.d)^2*(selectedVolume q)^(2/3:ℝ))=_
  unfold shape
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi];positivity
  · simp only [Set.mem_Ioi];positivity
  · simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_pow,
      Real.log_rpow,Real.one_rpow,Real.log_one,mul_zero]
    linarith

private theorem seed_scalar (F f seed u T:ℝ)(hF:1≤F)(hf:0<f)(hs:0<seed)
    (hT:0≤T)(hu:u=f*seed)(hcap:f≤T*F) :
    1/(F^(4/3:ℝ)*seed)≤T/u := by
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hu0:0<u:=hu.symm ▸ mul_pos hf hs
  have hpow:F≤F^(4/3:ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hF (by norm_num : (1:ℝ)≤4/3)
  apply (div_le_div_iff₀ (mul_pos (Real.rpow_pos_of_pos hF0 _) hs) hu0).mpr
  rw [one_mul,hu]
  have he:=mul_le_mul_of_nonneg_right
    (hcap.trans (mul_le_mul_of_nonneg_left hpow hT)) hs.le
  convert he using 1 <;> ring

/-- The original artificial divisor is restored from the actual seed.
Only actual nonzero frozen amplitudes supply the annular upper edge. -/
theorem raw_selected_geometry_seed (s:Source ι a b)(ha:0<a)(cover:OriginalEnclosure s)
    (u:Id)(L:Finset ι)(J:Finset {i//i∉Lᶜ})(x:Frozen (supplierData s ha u L J))
    (hx:MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x≠0)
    (seed:Id)(hseed:seed≠0)(hu:u=frozenProduct (supplierData s ha u L J) x*seed)
    (N:ℕ)(hcard:Fintype.card ι≤N)(K:ℝ)(hK:0<K) :
    let q:=supplierData s ha u L J
    let r:=residualSource s ha cover u L J x
    (selectedVolume q)^2*sourceVolume r*commonPhysicalCost r K/
      ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))≤
      (2:ℝ)^N*a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1/
        (u.absNorm:ℝ) := by
  let q:=supplierData s ha u L J
  let r:=residualSource s ha cover u L J x
  have hF:1≤frozenVolume q:=Finset.one_le_prod₀ (fun i _=>s.hP i.val)
  have hdim:Fintype.card ↥Lᶜ≤N:=
    (Fintype.card_le_of_injective (fun i:↥Lᶜ=>i.val) Subtype.val_injective).trans hcard
  have hcap:((frozenProduct q x).absNorm:ℝ)≤(2:ℝ)^N*frozenVolume q:=
    (actual_frozen_window s ha u L J x hx).2.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hdim) (zero_le_one.trans hF))
  have hprod:(u.absNorm:ℝ)=((frozenProduct q x).absNorm:ℝ)*(seed.absNorm:ℝ) := by
    rw [hu]
    simp only [map_mul,Nat.cast_mul]
    rfl
  have hi:=seed_scalar (frozenVolume q) ((frozenProduct q x).absNorm:ℝ)
    (seed.absNorm:ℝ) (u.absNorm:ℝ) ((2:ℝ)^N) hF
    (zero_lt_one.trans_le (ideal_norm_one_le (frozen_nonzero q x)))
    (zero_lt_one.trans_le (ideal_norm_one_le hseed)) (by positivity) hprod hcap
  have hshape:0≤a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1 := by
    have hv:=sourceVolume_pos s
    have hp:=pairNorm_pos s.hd.1 s.hd.2
    have hh:=prefixNormMax_pos s.d s.hd
    have hl:=s.hL
    unfold shape
    positivity
  calc
    _=((selectedVolume q)^2*sourceVolume r*commonPhysicalCost r K/
        ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)))/(seed.absNorm:ℝ) := by ring
    _=(a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1)*
        (1/((frozenVolume q)^(4/3:ℝ)*(seed.absNorm:ℝ))) := by
      rw [raw_selected_geometry s ha cover u L J x K hK]
      ring
    _≤(a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1)*
        ((2:ℝ)^N/(u.absNorm:ℝ)):=mul_le_mul_of_nonneg_left hi hshape
    _=_:=by ring

/-- Actual selected cardinality is paid as well as grouped averaging.
The extra numerical256 in the original supplier Cauchy is a fixed factor;
the moving selected-volume dependence has now disappeared completely. -/
theorem raw_selected_cauchy_geometry (s:Source ι a b)(ha:0<a)(cover:OriginalEnclosure s)
    (u:Id)(L:Finset ι)(J:Finset {i//i∉Lᶜ})(x:Frozen (supplierData s ha u L J))
    (hx:MixedSupplierFourthRow.frozenWeight (supplierData s ha u L J) x≠0)
    (seed:Id)(hseed:seed≠0)(hu:u=frozenProduct (supplierData s ha u L J) x*seed)
    (N:ℕ)(hcard:Fintype.card ι≤N)(K:ℝ)(hK:0<K) :
    let q:=supplierData s ha u L J
    let r:=residualSource s ha cover u L J x
    ((activeSelected q).card:ℝ)*selectedVolume q*sourceVolume r*commonPhysicalCost r K/
      ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))≤
      (512:ℝ)^N*a^(-4/3:ℝ)*shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1/
        (u.absNorm:ℝ) := by
  let q:=supplierData s ha u L J
  let r:=residualSource s ha cover u L J x
  have hP:∀i,0<q.P i:=fun i=>zero_lt_one.trans_le (s.hP i)
  have hw:=selectedVolume_pos q hP
  have hj:Fintype.card q.J≤N:=(MixedSelectedVolume.selected_card_le q).trans hcard
  have hc:((activeSelected q).card:ℝ)≤(256:ℝ)^N*selectedVolume q :=
    (active_selected_annular_card q (fun i=>(hP i).le) (fun i I hI=>(s.hpn i I hI).2)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hw.le)
  have hc':((activeSelected q).card:ℝ)/selectedVolume q≤(256:ℝ)^N:=
    (div_le_iff₀ hw).mpr hc
  have he:=raw_selected_geometry_seed s ha cover u L J x hx seed hseed hu N hcard K hK
  have hinner:0≤(selectedVolume q)^2*sourceVolume r*commonPhysicalCost r K/
      ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ)) := by
    have hphys:=commonPhysicalCost_nonneg r K hK.le
    have hv:=sourceVolume_pos r
    positivity
  have hh:=mul_le_mul hc' he hinner (by positivity : (0:ℝ)≤256^N)
  calc
    _=(((activeSelected q).card:ℝ)/selectedVolume q)*
        ((selectedVolume q)^2*sourceVolume r*commonPhysicalCost r K/
          ((pairNorm r.d)^2*(selectedVolume q)^(2/3:ℝ)*(seed.absNorm:ℝ))) := by
      dsimp only [q,r] at hw ⊢
      field_simp [hw.ne']
      <;> ring
    _≤(256:ℝ)^N*((2:ℝ)^N*a^(-4/3:ℝ)*
        shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1/(u.absNorm:ℝ)):=hh
    _=_:=by
      have hp:(256:ℝ)^N*(2:ℝ)^N=(512:ℝ)^N:=by rw [←mul_pow];norm_num
      calc
        _=((256:ℝ)^N*(2:ℝ)^N)*a^(-4/3:ℝ)*
            shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K 1/(u.absNorm:ℝ):=by ring
        _=_:=by rw [hp]

/-- Genuine weighted first-allocation estimate, not a bound for a
normalized live energy. The full existing common allowance remains. -/
theorem raw_allocation_reference_seed (root:Source ι a b)(η τ:Character)(C D:Id)
    (hC:Supported C)(hD:Supported D)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations (tuplePools root) C)
    (K Z Tfirst Cfirst ξ padding:ℝ)(hK:0<K)(hZ:1<Z)(hCf:1≤Cfirst)(hξ:0≤ξ)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hfirst:Tfirst≤Cfirst*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (sourceVolume root))
    (n:ℤ)(hn:Retained (frequencyRadius Tfirst Z ξ) n)(u:Id) :
    allocationShape root C B (nominalChildScale C D E K (sourceVolume root) Z padding n) 1/
      (reference τ C D (sourceVolume root) Z*(u.absNorm:ℝ))≤
    slotCost root/(u.absNorm:ℝ)*
      Z^(Real.logb Z (sourceVolume root)-5*inputWidth η K Z/6-
        2*(Real.logb Z root.L-Real.logb Z (prefixNormMax root.d))/3+
        5*(frequencyLoss Z Cfirst ξ+padding)/6) := by
  have he:=actual_allocation_reference root η τ C D hC hD hCD E B
    K Z Tfirst Cfirst ξ padding 1 hK hZ (by norm_num) hCf hξ hmod hfirst n hn
  simp only [Real.logb_one,mul_zero,zero_div,add_zero] at he
  have hu0:0≤1/(u.absNorm:ℝ):=by positivity
  have hh:=mul_le_mul_of_nonneg_right he hu0
  convert hh using 1 <;> (try dsimp only [inputWidth]) <;> ring

/-- Moving genuine root minimum. The only numerical premises are the
literal root volume, unit prefix and radial lower bound, supplied upstream. -/
theorem moving_root_reference (root:Source ι a b)(hunit:root.d=(1,1))
    (η τ:Character)(C D:Id)(hC:Supported C)(hD:Supported D)(hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E:Finset (CommonIndex C D))(B:actualAllocations (tuplePools root) C)
    (K Z Tfirst Cfirst ξ padding v ell:ℝ)(hZ:1<Z)(hK:Z≤K)(hCf:1≤Cfirst)(hξ:0≤ξ)
    (hL:root.L=Z^ell)(hV:Real.logb Z (sourceVolume root)≤v)
    (hmod:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hfirst:Tfirst≤Cfirst*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E}) K (sourceVolume root))
    (n:ℤ)(hn:Retained (frequencyRadius Tfirst Z ξ) n)(u:Id) :
    allocationShape root C B (nominalChildScale C D E K (sourceVolume root) Z padding n) 1/
      (reference τ C D (sourceVolume root) Z*(u.absNorm:ℝ))≤
    slotCost root/(u.absNorm:ℝ)*Z^(v-5/6-2*ell/3+5*(frequencyLoss Z Cfirst ξ+padding)/6) := by
  have hz:=zero_lt_one.trans hZ
  have hk:0<K:=hz.trans_le hK
  have he:=raw_allocation_reference_seed root η τ C D hC hD hCD E B K Z Tfirst Cfirst ξ padding
    hk hZ hCf hξ hmod hfirst n hn u
  have hR:1 ≤ inputWidth η K Z := by
    have hh:1≤Real.logb Z K:=by
      simpa only [Real.logb_self_eq_one hZ] using Real.logb_le_logb_of_le hZ hz hK
    have hη:=Real.logb_nonneg hZ (ideal_norm_one_le η.modulus_ne_bot)
    have hf:=Real.logb_nonneg hZ fixed_presentation_one_le
    unfold inputWidth
    linarith
  have hmin:Real.logb Z root.L=ell:=by rw [hL,Real.logb_rpow hz hZ.ne']
  have hprefix:Real.logb Z (prefixNormMax root.d)=0 := by
    simp only [hunit,prefixNormMax,map_one,Nat.cast_one,max_self,Real.logb_one]
  apply he.trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by rw [hmin,hprefix];linarith))
    (div_nonneg (slotCost_nonneg root) (Nat.cast_nonneg _))

end
end Candidate.FourthPower.RepairedRawExceptional

