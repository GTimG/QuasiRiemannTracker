/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform bounded-buffer height gates before all moving source data. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedLowSourceMissingBins
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.RegularRetainedNaturalBins
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowBufferedSource
noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths Cycle61InitialMass

theorem buffered_height_interval (Z τ v:ℝ)(i:ℕ)(hv:|v|≤Z^τ)(hZ:0≤Z^τ):
    |v|+Z^τ/2≤(3*i+2:ℕ)*Z^τ:=by
  have hi:(2:ℝ)≤(3*i+2:ℕ):=by exact_mod_cast (show 2≤3*i+2 by omega)
  have hm:=mul_le_mul_of_nonneg_right hi hZ
  linarith only [hv,hm,hZ]

theorem eventually_buffered_height (τ d η:ℝ)(I:ℕ)(hτ:0<τ)(hgap:2*τ<d*η):
    ∀ᶠZ:ℝ in atTop,1≤Z^τ ∧ ∀i:ℕ,i≤I→(3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η:=by
  let c:ℝ:=3+(3*I+2:ℕ)
  have hδ:0<d*η-2*τ:=sub_pos.mpr hgap
  filter_upwards [(tendsto_rpow_atTop hτ).eventually (eventually_ge_atTop (1:ℝ)),
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (c^2)),eventually_gt_atTop (0:ℝ)] with Z hbig hpow hZ
  refine ⟨hbig,?_⟩
  intro i hi
  have hcoeff:(3*i+2:ℕ)≤3*I+2:=by omega
  have hy:3+(3*i+2:ℕ)*Z^τ≤c*Z^τ:=by
    have hc:((3*i+2:ℕ):ℝ)≤(3*I+2:ℕ):=by exact_mod_cast hcoeff
    have hm:=mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZ.le τ)
    dsimp only [c]
    nlinarith only [hm,hbig]
  calc
    _≤(c*Z^τ)^2:=pow_le_pow_left₀ (by positivity) hy 2
    _=c^2*Z^(2*τ):=by rw [mul_pow]; congr 1; rw [←Real.rpow_natCast (Z^τ) 2,←Real.rpow_mul hZ.le]; congr 1; norm_num; ring
    _≤Z^(d*η-2*τ)*Z^(2*τ):=mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hZ.le _)
    _=(Z^d)^η:=by rw [←Real.rpow_add hZ,←Real.rpow_mul hZ.le]; congr 1; ring
end
end QRH.Record1252270103Source.Admission.SelectedLowBufferedSource
#print axioms QRH.Record1252270103Source.Admission.SelectedLowBufferedSource.buffered_height_interval
#print axioms QRH.Record1252270103Source.Admission.SelectedLowBufferedSource.eventually_buffered_height
