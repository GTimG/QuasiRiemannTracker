/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatchConcrete
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Qrh.JointDetector.RepeatedMarks.RootedRescaling
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set Filter OAI OAI.SevenEighths HeckeInverseAmplification

def width (U Z w : ℝ) : ℝ := Real.logb U (Z^w)

theorem radius_eq {U Z : ℝ} (hU : 1<U) (hZ : 0<Z) (w : ℝ) :
    U^(width U Z w)=Z^w :=
  Real.rpow_logb (zero_lt_one.trans hU) (ne_of_gt hU) (Real.rpow_pos_of_pos hZ _)

theorem width_nonneg {U Z w : ℝ} (hU : 1<U) (hZ : 1≤Z) (hw : 0≤w) :
    0≤width U Z w := Real.logb_nonneg hU (Real.one_le_rpow hZ hw)

theorem width_upper {U Z w mesh dmin : ℝ} (hU : 1<U) (hZ : 1<Z)
    (hd : 0<dmin) (hcore : Z^dmin≤U) (hw : 0≤w) (hwm : w≤mesh) :
    width U Z w≤mesh/dmin := by
  apply (Real.logb_le_iff_le_rpow hU (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)).2
  have hmesh : 0≤mesh := hw.trans hwm
  calc Z^w ≤ Z^mesh := Real.rpow_le_rpow_of_exponent_le hZ.le hwm
    _ = (Z^dmin)^(mesh/dmin) := by
      rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
      congr 1
      exact (mul_div_cancel₀ mesh hd.ne').symm
    _ ≤ U^(mesh/dmin) := Real.rpow_le_rpow
      (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hcore (div_nonneg hmesh hd.le)

theorem width_lower {U Z w D : ℝ} (hU : 1<U) (hZ : 1<Z)
    (hD : 0<D) (hupper : U≤Z^D) (hw : 0≤w) :
    w/D≤width U Z w := by
  apply (Real.le_logb_iff_rpow_le hU (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)).2
  calc U^(w/D) ≤ (Z^D)^(w/D) :=
        Real.rpow_le_rpow (zero_lt_one.trans hU).le hupper (div_nonneg hw hD.le)
    _ = Z^w := by
      rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
      congr 1
      exact mul_div_cancel₀ w hD.ne'

theorem sum_width_lower {Slot : Type*} (slots : Finset Slot) (w : Slot→ℝ)
    {U Z D smin : ℝ} (hU : 1<U) (hZ : 1<Z) (hD : 0<D)
    (hupper : U≤Z^D) (hw : ∀s∈slots,0≤w s) (hs : smin≤∑s∈slots,w s) :
    smin/D≤∑s∈slots,width U Z (w s) := by
  calc smin/D ≤ (∑s∈slots,w s)/D := div_le_div_of_nonneg_right hs hD.le
    _ = ∑s∈slots,w s/D := Finset.sum_div ..
    _ ≤ _ := Finset.sum_le_sum (fun s hs=>width_lower hU hZ hD hupper (hw s hs))

theorem sum_width_eq {Slot : Type*} (slots : Finset Slot) (w : Slot→ℝ)
    {U Z : ℝ} (hZ : 0<Z) :
    (∑s∈slots,width U Z (w s))=(∑s∈slots,w s)*Real.logb U Z := by
  simp only [width,Real.logb_rpow_eq_mul_logb_of_pos hZ,Finset.sum_mul]

theorem amplitude_radius_eq {Slot : Type*} (slots : Finset Slot) (w : Slot→ℝ)
    {U Z : ℝ} (hU : 1<U) (hZ : 0<Z) (δ : ℝ) :
    U^(δ*(∑s∈slots,width U Z (w s)))=Z^(δ*(∑s∈slots,w s)) := by
  have heq : δ*(∑s∈slots,width U Z (w s))=width U Z (δ*(∑s∈slots,w s)) := by
    rw [sum_width_eq slots w hZ]
    simp only [width,Real.logb_rpow_eq_mul_logb_of_pos hZ]
    ring
  rw [heq,radius_eq hU hZ]

/-- Fixed conductor constants are absorbed only into the ambient radius.
The physical prime radii and all imaginary shifts are left unchanged. -/
theorem eventually_ambient (Ccond bΦ Mcap dmin : ℝ)
    (hC : 1≤Ccond) (hd : 0<dmin) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀Y : ℝ,
      Z^dmin≤Y → Y≤bΦ*Z^Mcap →
      1<Ccond*Y ∧ Z^dmin≤Ccond*Y ∧ Ccond*Y≤Z^(Mcap+2) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (Ccond*bΦ)] with Z hZ hconst
  refine ⟨hZ,?_⟩
  intro Y hY hYupper
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hY1 : 1<Y := (Real.one_lt_rpow hZ hd).trans_le hY
  have hCY : Y≤Ccond*Y := le_mul_of_one_le_left (by linarith) hC
  refine ⟨hY1.trans_le hCY,hY.trans hCY,?_⟩
  calc Ccond*Y ≤ Ccond*(bΦ*Z^Mcap) := mul_le_mul_of_nonneg_left hYupper (by linarith)
    _ = (Ccond*bΦ)*Z^Mcap := by ring
    _ ≤ Z*Z^Mcap := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hZp.le _)
    _ = Z^(1:ℝ)*Z^Mcap := by rw [Real.rpow_one]
    _ = Z^((1:ℝ)+Mcap) := (Real.rpow_add hZp _ _).symm
    _ ≤ Z^(Mcap+2) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)


/-- Root caps are uniform in the enlarged conductor radius. A deliberately
loose ambient exponent avoids any dependence on the later slot count. -/
theorem root_norm_upper (root : NonzeroIdeal) {Z U bΦ Mcap dmin Aroot : ℝ}
    (hZ : 1<Z) (hd : 0<dmin) (hM : 0≤Mcap) (hPhi : bΦ≤Z)
    (hcore : Z^dmin≤U) (hAr : (Mcap+2)/dmin≤Aroot)
    (hroot : (root.val.absNorm:ℝ)^6≤bΦ*Z^Mcap) :
    (root.val.absNorm:ℝ)≤U^Aroot := by
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hA : 0≤Aroot := (div_nonneg (by linarith) hd.le).trans hAr
  have hnat : 0<root.val.absNorm := by
    have hp := HeckeDyadic.norm_pos root
    change (0:ℝ)<(root.val.absNorm:ℝ) at hp
    exact_mod_cast hp
  have hn : 1≤(root.val.absNorm:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hnat)
  have hpow : (root.val.absNorm:ℝ)≤(root.val.absNorm:ℝ)^6 := le_self_pow₀ hn (by norm_num)
  have hDA : Mcap+2≤dmin*Aroot := (div_le_iff₀ hd).mp hAr |>.trans_eq (mul_comm _ _)
  calc (root.val.absNorm:ℝ) ≤ (root.val.absNorm:ℝ)^6 := hpow
    _ ≤ bΦ*Z^Mcap := hroot
    _ ≤ Z*Z^Mcap := mul_le_mul_of_nonneg_right hPhi (Real.rpow_nonneg hZp.le _)
    _ = Z^(1:ℝ)*Z^Mcap := by rw [Real.rpow_one]
    _ = Z^((1:ℝ)+Mcap) := (Real.rpow_add hZp _ _).symm
    _ ≤ Z^(dmin*Aroot) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = (Z^dmin)^Aroot := Real.rpow_mul hZp.le _ _
    _ ≤ U^Aroot := Real.rpow_le_rpow (Real.rpow_nonneg hZp.le _) hcore hA

end
end Qrh.JointDetector.RepeatedMarks.RootedRescaling

#print axioms Qrh.JointDetector.RepeatedMarks.RootedRescaling.eventually_ambient
#print axioms Qrh.JointDetector.RepeatedMarks.RootedRescaling.sum_width_lower
#print axioms Qrh.JointDetector.RepeatedMarks.RootedRescaling.root_norm_upper
