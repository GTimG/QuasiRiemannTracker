/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Missing-norm floor intervals and exact finite-family collection. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedLowSourceReindex
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins
noncomputable section
open scoped Classical BigOperators

def missingBin (width Z norm : ℝ) : ℕ := ⌊Real.logb Z norm/width⌋₊
def missingBinCount (width bound : ℝ) : ℕ := ⌊bound/width⌋₊+1

theorem missing_bin_bounds (width Z norm bound x : ℝ)
    (hw : 0<width) (hZ : 1<Z) (hn : 1≤norm)
    (hbound : norm≤Z^bound) (hx : norm≤Z^x) :
    missingBin width Z norm<missingBinCount width bound ∧
    0≤(missingBin width Z norm:ℝ)*width ∧
    Z^((missingBin width Z norm:ℝ)*width)≤norm ∧
    norm≤Z^(((missingBin width Z norm:ℝ)+1)*width) ∧
    ((missingBin width Z norm:ℝ)+1)*width≤bound+width ∧
    ((missingBin width Z norm:ℝ)+1)*width≤x+width := by
  have hn0:0<norm:=zero_lt_one.trans_le hn
  have hlog0:0≤Real.logb Z norm:=Real.logb_nonneg hZ hn
  have hlogB:Real.logb Z norm≤bound:=(Real.logb_le_iff_le_rpow hZ hn0).mpr hbound
  have hlogx:Real.logb Z norm≤x:=(Real.logb_le_iff_le_rpow hZ hn0).mpr hx
  have hlo:(missingBin width Z norm:ℝ)*width≤Real.logb Z norm:=
    (le_div_iff₀ hw).mp (Nat.floor_le (div_nonneg hlog0 hw.le))
  have hhi:Real.logb Z norm<((missingBin width Z norm:ℝ)+1)*width:=
    (div_lt_iff₀ hw).mp (Nat.lt_floor_add_one (Real.logb Z norm/width))
  refine ⟨Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right hlogB hw.le)),
    mul_nonneg (Nat.cast_nonneg _) hw.le,?_,?_,by linarith only [hlo,hlogB],by linarith only [hlo,hlogx]⟩
  · calc
      _≤Z^(Real.logb Z norm):=Real.rpow_le_rpow_of_exponent_le hZ.le hlo
      _=norm:=Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn0
  · calc
      norm=Z^(Real.logb Z norm):=(Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn0).symm
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le hhi.le

theorem missing_bin_upper_le (width bound:ℝ)(hw:0<width)(hbound:0≤bound)
    (k:ℕ)(hk:k<missingBinCount width bound):
    ((k:ℝ)+1)*width≤bound+width:=by
  have hk':k≤⌊bound/width⌋₊:=Nat.le_of_lt_succ hk
  have hfloor:(⌊bound/width⌋₊:ℝ)≤bound/width:=Nat.floor_le (div_nonneg hbound hw.le)
  have he:(k:ℝ)*width≤bound:=(le_div_iff₀ hw).mp ((Nat.cast_le.mpr hk').trans hfloor)
  linarith only [he]

theorem finite_bin_collection {κ:Type} [Fintype κ] [DecidableEq κ]
    (index:κ→ℕ)(count:ℕ)(f:κ→ℝ)(E:ℝ)
    (hindex:∀r,index r<count)
    (hbin:∀k<count,(∑r:Finset.univ.filter (fun r:κ=>index r=k),f r.val)≤E):
    (∑r:κ,f r)≤(count:ℝ)*E:=by
  have hp: (∑r:κ,f r)=∑k∈Finset.range count,∑r∈Finset.univ.filter (fun r:κ=>index r=k),f r:=
    (Finset.sum_fiberwise_of_maps_to (fun r _=>Finset.mem_range.mpr (hindex r)) f).symm
  rw [hp]
  calc
    _≤∑_k∈Finset.range count,E:=by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [Finset.sum_coe_sort] using hbin k (Finset.mem_range.mp hk)
    _=(count:ℝ)*E:=by simp
end
end QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins
#print axioms QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins.missing_bin_bounds
#print axioms QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins.finite_bin_collection

#print axioms QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins.missing_bin_upper_le
