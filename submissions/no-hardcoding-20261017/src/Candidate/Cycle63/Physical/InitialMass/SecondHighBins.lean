import Candidate.Cycle63.Physical.InitialMass.SecondHighPayment
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators

/-- Fixed-width exponent bins. Their width is chosen from the strict
reserve before the moving source, and their number is independent of Z. -/
def exponentBin {n : ℕ} (width : ℝ) (x : Fin n→ℝ) : Fin n→ℤ :=
  fun i=>⌊x i/width⌋

def exponentBinUpper {n : ℕ} (width : ℝ) (key : Fin n→ℤ) : Fin n→ℝ :=
  fun i=>((key i:ℝ)+1)*width

theorem exponent_bin_enclosure {n : ℕ} (width : ℝ) (hw : 0<width) (x : Fin n→ℝ) (i : Fin n) :
    x i≤exponentBinUpper width (exponentBin width x) i ∧
      exponentBinUpper width (exponentBin width x) i≤x i+width := by
  have hlo := mul_le_mul_of_nonneg_right (Int.floor_le (x i/width)) hw.le
  have hhi := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x i/width)) hw
  rw [div_mul_cancel₀ _ hw.ne'] at hlo hhi
  dsimp [exponentBinUpper,exponentBin]
  constructor <;> linarith

/-- A uniform finite bin count from a fixed box of exponent coordinates. -/
theorem exponent_bins_card {κ : Type*} {n : ℕ} (rows : Finset κ)
    (x : κ→Fin n→ℝ) (width B : ℝ) (hw : 0<width)
    (hx : ∀k∈rows,∀i,-B≤x k i ∧ x k i≤B) :
    (rows.image (fun k=>exponentBin width (x k))).card≤
      (Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^n := by
  let box := Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋
  let Box := Fin n→↥box
  have hsub : rows.image (fun k=>exponentBin width (x k))⊆
      Finset.univ.image (fun b : Box=>fun i=>(b i).val) := by
    intro v hv
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
    let b : Box := fun i=>⟨exponentBin width (x k) i,Finset.mem_Icc.mpr
      ⟨Int.floor_mono (div_le_div_of_nonneg_right (hx k hk i).1 hw.le),
       Int.floor_mono (div_le_div_of_nonneg_right (hx k hk i).2 hw.le)⟩⟩
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
  have hc : (rows.image (fun k=>exponentBin width (x k))).card≤Fintype.card Box :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by rw [Finset.card_univ]))
  simpa only [Box,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,box] using hc

def highExponentValue (δ : ℝ) (x : Fin 4→ℝ) : ℝ :=
  x 0+x 1+OAI.SevenEighths.LocalMoment.unmarkedDensity δ*x 2+δ*x 3

/-- Rounding the scalar, missing radical, frequency and raw-volume
coordinates upward costs at most four bin widths throughout the high range. -/
theorem high_exponent_bin_payment (width δ : ℝ) (hw : 0<width)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (x : Fin 4→ℝ) :
    highExponentValue δ (exponentBinUpper width (exponentBin width x))≤
      highExponentValue δ x+4*width := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  have hρ := Cycle63.Physical.high_density_bounds hδ
  have hρ0 : 0≤LocalMoment.unmarkedDensity δ := by linarith [hρ.1]
  have hρ1 : LocalMoment.unmarkedDensity δ≤1 := by
    have hh:=hρ.2.1
    linarith [Cycle63.Arithmetic.rho0_bounds.2]
  have hd0 : 0≤δ := by linarith [hδ.1, hq0b.1]
  have h0 := (exponent_bin_enclosure width hw x 0).2
  have h1 := (exponent_bin_enclosure width hw x 1).2
  have h2 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 2).2 hρ0
  have h3 := mul_le_mul_of_nonneg_left (exponent_bin_enclosure width hw x 3).2 hd0
  have hρw := mul_le_mul_of_nonneg_right hρ1 hw.le
  have hdw := mul_le_mul_of_nonneg_right hδ.2 hw.le
  unfold highExponentValue
  nlinarith

theorem high_bin_reserve_transfer (width δ target reserve : ℝ) (hw : 0<width)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4) (x : Fin 4→ℝ)
    (hbound : highExponentValue δ x≤target-reserve) :
    highExponentValue δ (exponentBinUpper width (exponentBin width x))≤
      target-reserve+4*width := (high_exponent_bin_payment width δ hw hδ x).trans (by linarith)

/-- Sum estimates proved on fixed exponent bins, charging only the fixed
number of bins. No additional count of the source rows appears. -/
theorem high_binned_sum {κ : Type*} (rows : Finset κ) (x : κ→Fin 4→ℝ)
    (energy : κ→ℝ) (width B δ Z C target reserve : ℝ)
    (hw : 0<width) (hZ : 1≤Z) (hC : 0≤C)
    (hδ : Cycle63.Arithmetic.q0≤δ ∧ δ≤3/4)
    (hx : ∀k∈rows,∀i,-B≤x k i ∧ x k i≤B)
    (hpoint : ∀k∈rows,highExponentValue δ (x k)≤target-reserve)
    (hbin : ∀key∈rows.image (fun k=>exponentBin width (x k)),
      (∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k)≤
        C*Z^(highExponentValue δ (exponentBinUpper width key))) :
    (∑k∈rows,energy k)≤
      ((Finset.Icc (⌊-B/width⌋:ℤ) ⌊B/width⌋).card^4:ℕ)*
        (C*Z^(target-reserve+4*width)) := by
  have hq0b := Cycle63.Arithmetic.q0_bounds
  let keys := rows.image (fun k=>exponentBin width (x k))
  have hsplit : (∑k∈rows,energy k)=
      ∑key∈keys,∑k∈rows.filter (fun k=>exponentBin width (x k)=key),energy k := by
    exact (Finset.sum_fiberwise_of_maps_to (fun k hk=>Finset.mem_image.mpr ⟨k,hk,rfl⟩) _).symm
  have hcard := exponent_bins_card rows x width B hw hx
  rw [hsplit]
  calc
    _≤∑_key∈keys,C*Z^(target-reserve+4*width) := by
      apply Finset.sum_le_sum
      intro key hk
      have hh := hbin key hk
      obtain ⟨k,hrow,rfl⟩ := Finset.mem_image.mp hk
      exact hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ
          (high_bin_reserve_transfer width δ target reserve hw hδ (x k) (hpoint k hrow))) hC)
    _=(keys.card:ℝ)*(C*Z^(target-reserve+4*width)) := by simp
    _≤_ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.exponent_bin_enclosure
#print axioms OAI.SevenEighths.Cycle63InitialMass.exponent_bins_card
#print axioms OAI.SevenEighths.Cycle63InitialMass.high_exponent_bin_payment
#print axioms OAI.SevenEighths.Cycle63InitialMass.high_bin_reserve_transfer
#print axioms OAI.SevenEighths.Cycle63InitialMass.high_binned_sum
