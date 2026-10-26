/- Adapted from Zhongpai Gao, accepted PR63 gao-balanced-marked-20261017,
Apache-2.0; tracker snapshot 9c0e14f985041e397f71c574028193ee595a0f98,
accepted source head 52419a826d4a8465cdeb56aaa2d471c489221d1d.
Underlying canonical source interfaces: OpenAI/math and Hailey Collet,
Apache-2.0. This development overlay reuses pinned Cycle61 definitions. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Natural.HighBins

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open scoped Classical BigOperators
namespace QRH.Record1252270103Source.High.Geometry
open OAI OAI.SevenEighths
open OAI.SevenEighths.Record12518109Natural.JointHigh
open Cycle61InitialMass

theorem high_exponent_bin_payment (width δ : ℝ) (hw : 0<width)
    (hδ : 1/2≤δ ∧ δ≤3/4) (x : Fin 4→ℝ) :
    highExponentValue δ (exponentBinUpper width (exponentBin width x))≤
      highExponentValue δ x+4*width := by
  have hd0 : 0≤δ := by linarith [hδ.1]
  have hden : 0 < 3*(5-2*δ) := by linarith [hδ.2]
  have hquot : 0 ≤ 10*δ/(3*(5-2*δ)) := div_nonneg (by positivity) hden.le
  have hquot' : 10*δ/(3*(5-2*δ)) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith [hδ.2]
  have hρ0 : 0≤LocalMoment.unmarkedDensity δ := by
    unfold LocalMoment.unmarkedDensity
    linarith
  have hρ1 : LocalMoment.unmarkedDensity δ≤1 := by
    unfold LocalMoment.unmarkedDensity
    linarith
  have h0 := (exponent_bin_enclosure width hw x 0).2
  have h1 := (exponent_bin_enclosure width hw x 1).2
  have h2 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 2).2 hρ0
  have h3 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 3).2 hd0
  have hρw := mul_le_mul_of_nonneg_right hρ1 hw.le
  have hdw := mul_le_mul_of_nonneg_right hδ.2 hw.le
  unfold highExponentValue
  nlinarith

theorem retained_high_bin_payment (width δ : ℝ) (hw : 0<width)
    (hδ : 1/2≤δ ∧ δ≤3/4)
    (gain : ℝ→ℝ) (hg : Monotone gain) (x : Fin 4→ℝ) :
    retainedHighExponent δ gain (exponentBinUpper width (exponentBin width x))≤
      retainedHighExponent δ gain x+4*width := by
  have hp:=high_exponent_bin_payment width δ hw hδ x
  have hg':=hg (exponent_bin_enclosure width hw x 2).1
  unfold retainedHighExponent
  linarith

/-- The same four coordinates suffice for the refined joint amplitude count.
Upward frequency rounding only improves the monotone retained saving. -/
theorem retained_high_binned_sum {κ : Type*} (rows : Finset κ) (x : κ→Fin 4→ℝ)
    (energy : κ→ℝ) (width B δ Z C target reserve : ℝ)
    (hw : 0<width) (hZ : 1≤Z) (hC : 0≤C)
    (hδ : 1/2≤δ ∧ δ≤3/4)
    (gain : ℝ→ℝ) (hg : Monotone gain)
    (hx : ∀k∈rows,∀i,-B≤x k i ∧ x k i≤B)
    (hpoint : ∀k∈rows,retainedHighExponent δ gain (x k)≤target-reserve)
    (hbin : ∀key∈rows.image (fun k=>exponentBin width (x k)),
      (∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k)≤
        C*Z^(retainedHighExponent δ gain (exponentBinUpper width key))) :
    (∑k∈rows,energy k)≤
      ((Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^4:ℕ)*
        (C*Z^(target-reserve+4*width)) := by
  let keys:=rows.image (fun k=>exponentBin width (x k))
  have hsplit : (∑k∈rows,energy k)=
      ∑key∈keys,∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k := by
    exact (Finset.sum_fiberwise_of_maps_to (fun k hk=>Finset.mem_image.mpr ⟨k,hk,rfl⟩) _).symm
  have hcard:=exponent_bins_card rows x width B hw hx
  rw [hsplit]
  calc
    _≤∑_key∈keys,C*Z^(target-reserve+4*width) := by
      apply Finset.sum_le_sum
      intro key hk
      have hh:=hbin key hk
      obtain ⟨k,hrow,rfl⟩:=Finset.mem_image.mp hk
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hZ
      exact (retained_high_bin_payment width δ hw hδ gain hg (x k)).trans (by linarith [hpoint k hrow])
    _=(keys.card:ℝ)*(C*Z^(target-reserve+4*width)) := by simp
    _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)


end QRH.Record1252270103Source.High.Geometry
#print axioms QRH.Record1252270103Source.High.Geometry.retained_high_binned_sum
