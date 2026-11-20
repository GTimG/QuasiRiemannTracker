/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed ambient dilation absorbs the Fourier/dyadic factor three even at
the closed source edge. Every actual slot size and row radius is unchanged. -/
import Candidate.C092.transport.NativeStrip
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Filter
namespace QRH.Cycle092.FixedBaseCollar

def factor : ℝ := 64
def base (U:ℝ) := factor*U
def coord (U t:ℝ) := Real.logb (base U) (U^t)

theorem one_lt_base {U:ℝ} (hU:1<U) : 1<base U := by unfold base factor;linarith

theorem reconstruct {U:ℝ} (hU:1<U) (t:ℝ) : (base U)^(coord U t)=U^t :=
  Real.rpow_logb (zero_lt_one.trans (one_lt_base hU)) (one_lt_base hU).ne'
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)

theorem coord_range {U:ℝ} (hU:1<U) {t:ℝ} (ht:0  ≤  t) : 0  ≤  coord U t ∧ coord U t  ≤  t := by
  have hb:=one_lt_base hU
  refine ⟨Real.logb_nonneg hb (Real.one_le_rpow hU.le ht),?_⟩
  have h:U  ≤  base U := by unfold base factor;linarith
  calc
    _  ≤  Real.logb (base U) ((base U)^t) := Real.logb_le_logb_of_le hb
      (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_le_rpow (zero_lt_one.trans hU).le h ht)
    _ = _ := Real.logb_rpow (zero_lt_one.trans hb) hb.ne'

theorem three_le {x:ℝ} (hx:(1/3:ℝ)  ≤  x) : 3  ≤  factor^x := by
  have h : (4:ℝ) = factor^(1/3:ℝ) := by
    rw [show factor = (4:ℝ)^3 by norm_num [factor],←Real.rpow_natCast_mul (by norm_num)]
    norm_num
  exact (by norm_num : (3:ℝ) ≤ 4).trans (h ▸ Real.rpow_le_rpow_of_exponent_le (by norm_num [factor] : 1  ≤  factor) hx)

theorem component {U X X' n:ℝ} (hU:1<U) (hn:(1/3:ℝ) ≤ n) (hX:X ≤ U^n) (hX':X'  ≤  3*X) :
    X'  ≤  (base U)^n := by
  rw [base,Real.mul_rpow (by norm_num [factor]) (zero_lt_one.trans hU).le]
  exact hX'.trans ((mul_le_mul_of_nonneg_left hX (by norm_num : (0:ℝ) ≤ 3)).trans
    (mul_le_mul_of_nonneg_right (three_le hn) (Real.rpow_nonneg (zero_lt_one.trans hU).le _)))

theorem retained_width {ι:Type*} (T:Finset ι) (w:ι→ℝ) {U cap mesh:ℝ} (hU:1<U)
    (hw:∀i,0 ≤ w i) (hm:∀i,w i ≤ mesh) (hq:(∑i∈T,w i) ≤ cap) :
    (∀i,0 ≤ coord U (w i) ∧ coord U (w i) ≤ mesh) ∧ (∑i∈T,coord U (w i)) ≤ cap :=
  ⟨fun i=>⟨(coord_range hU (hw i)).1,(coord_range hU (hw i)).2.trans (hm i)⟩,
    (Finset.sum_le_sum (fun i _=>(coord_range hU (hw i)).2)).trans hq⟩

/-- The positive-part surcharge increases by at most a fixed power of 64,
independent of the varying radius, labels, original scale or heights. -/
theorem radial_cost {U V H e:ℝ} (hU:1<U) (hH:0 ≤ H) :
    (base U)^(coord U V+e+(5/6)*max 0 (H-coord U V))  ≤ 
      factor^(e+(5/6)*H)*U^(V+e+(5/6)*max 0 (H-V)) := by
  have hb:=one_lt_base hU
  have b0:=zero_lt_one.trans hb
  have u0:=zero_lt_one.trans hU
  have f0:0<factor:=by norm_num [factor]
  have hs:base U^((5/6:ℝ)*max 0 (H-coord U V))  ≤  factor^((5/6:ℝ)*H)*U^((5/6:ℝ)*max 0 (H-V)) := by
    have hmax:base U^(max 0 (H-coord U V))  ≤  factor^H*U^(max 0 (H-V)) := by
      by_cases h : H ≤ coord U V
      · rw [max_eq_left (by linarith),Real.rpow_zero]
        apply one_le_mul_of_one_le_of_one_le
        · apply Real.one_le_rpow (by norm_num [factor]) hH
        · apply Real.one_le_rpow hU.le (le_max_left _ _)
      · rw [max_eq_right (by linarith),Real.rpow_sub b0,reconstruct hU,base,Real.mul_rpow f0.le u0.le,
          mul_div_assoc,←Real.rpow_sub u0]
        apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le (le_max_right _ _)) (Real.rpow_nonneg f0.le _)
    have hpow:=Real.rpow_le_rpow (Real.rpow_nonneg b0.le _) hmax (by norm_num : (0:ℝ) ≤ 5/6)
    rw [←Real.rpow_mul b0.le,Real.mul_rpow (Real.rpow_nonneg f0.le _) (Real.rpow_nonneg u0.le _),
      ←Real.rpow_mul f0.le,←Real.rpow_mul u0.le] at hpow
    convert hpow using 2 <;> ring
  rw [Real.rpow_add b0,Real.rpow_add b0,reconstruct hU,Real.rpow_add f0,Real.rpow_add u0,Real.rpow_add u0]
  have he:(base U)^e=factor^e*U^e:=Real.mul_rpow f0.le u0.le
  rw [he]
  convert mul_le_mul_of_nonneg_left hs (by positivity : 0  ≤  U^V*(factor^e*U^e)) using 1 <;> ring

#print axioms reconstruct
#print axioms component
#print axioms radial_cost
end QRH.Cycle092.FixedBaseCollar
