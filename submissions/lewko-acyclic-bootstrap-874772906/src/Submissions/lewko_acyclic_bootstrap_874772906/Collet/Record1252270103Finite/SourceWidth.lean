/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SeedSourceFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section

def WidthAffine (f:ℝ→ℝ) : Prop := ∀ x y t,
 f ((1-t)*x+t*y)=(1-t)*f x+t*f y

theorem width_affine_positive {f:ℝ→ℝ} (hf:WidthAffine f) {l r b:ℝ}
 (hb:b∈Set.Icc l r) (hl:0<f l) (hr:0<f r) : 0<f b := by
 rcases eq_or_lt_of_le (le_trans hb.1 hb.2) with he | he
 · have h : b=l := by linarith [hb.1,hb.2]
   simpa [h] using hl
 let t := (b-l)/(r-l)
 have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hb.1) (le_of_lt (sub_pos.mpr he))
 have ht1 : t≤1 := (div_le_one (sub_pos.mpr he)).mpr (by linarith [hb.2])
 have ht : t*(r-l)=b-l := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr he))
 have hx : (1-t)*l+t*r=b := by nlinarith only [ht]
 rw [←hx,hf]
 rcases eq_or_lt_of_le ht0 with hzero | hpos
 · rw [←hzero]
   simpa using hl
 · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt hl)) (mul_pos hpos hr)

theorem width_affine_nonnegative {f:ℝ→ℝ} (hf:WidthAffine f) {l r b:ℝ}
 (hb:b∈Set.Icc l r) (hl:0≤f l) (hr:0≤f r) : 0≤f b := by
 rcases eq_or_lt_of_le (le_trans hb.1 hb.2) with he | he
 · have h : b=l := by linarith [hb.1,hb.2]
   simpa [h] using hl
 let t := (b-l)/(r-l)
 have ht0 : 0≤t := div_nonneg (sub_nonneg.mpr hb.1) (le_of_lt (sub_pos.mpr he))
 have ht1 : t≤1 := (div_le_one (sub_pos.mpr he)).mpr (by linarith [hb.2])
 have ht : t*(r-l)=b-l := div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr he))
 have hx : (1-t)*l+t*r=b := by nlinarith only [ht]
 rw [←hx,hf]
 exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hl) (mul_nonneg ht0 hr)

def sourceTReal (n:Source) (b:ℝ) : ℝ := (n.B:ℝ)-(n.L:ℝ)*(b-(n.allowance:ℝ))
def sourceAReal (n low:Source) (b:ℝ) : ℝ :=
 ((n.q:ℝ)*(b+(sourceTReal n b-(low.B:ℝ))/(low.L:ℝ))+(n.lowFee:ℝ))/(sourceDen n low:ℝ)
def sourceFReal (n low:Source) (b:ℝ) : ℝ := 1-6*sourceAReal n low b

theorem sourceTReal_rat (n:Source) (b:ℚ) : sourceTReal n (b:ℝ)=(sourceT n b:ℝ) := by
 simp [sourceTReal,sourceT]
theorem sourceAReal_rat (n low:Source) (b:ℚ) : sourceAReal n low (b:ℝ)=(sourceA n low b:ℝ) := by
 simp [sourceAReal,sourceA,sourceTReal_rat]
theorem sourceFReal_rat (n low:Source) (b:ℚ) : sourceFReal n low (b:ℝ)=(sourceF n low b:ℝ) := by
 simp [sourceFReal,sourceF,sourceAReal_rat]

theorem sourceTReal_affine (n:Source) : WidthAffine (sourceTReal n) := by
 intro x y t
 dsimp [sourceTReal]
 ring
theorem sourceAReal_affine (n low:Source) : WidthAffine (sourceAReal n low) := by
 intro x y t
 dsimp [sourceAReal,sourceTReal]
 ring
theorem sourceFReal_affine (n low:Source) : WidthAffine (sourceFReal n low) := by
 intro x y t
 dsimp [sourceFReal]
 rw [sourceAReal_affine n low x y t]
 ring

def sourceScalarReal (K:ℚ) (n low:Source) (b:ℝ) (j:Fin 16) : ℝ :=
 let a := sourceAReal n low b
 let t := sourceTReal n b
 let T := t+b
 let F := sourceFReal n low b
 let e : ℝ := n.allowance
 let Lref := 49/100-(K:ℝ)*b
 ![(sourceDen n low:ℝ),b-2*e,a,1/75-a,F-T/2-4*e,
 (low.B:ℝ)*F-t-b-4*e,1-(n.q:ℝ)*(low.cap:ℝ),
 (n.lowFee:ℝ)-((n.q:ℝ)*(low.B:ℝ)/(low.L:ℝ)+(n.q:ℝ)*(low.cap:ℝ)+4)*e-10*e,
 a-20*e,Lref,1-Lref-1/2-(K:ℝ)*b-10*e,
 5/6+(499/1000)*Lref-T-9*a-(n.highFee:ℝ),
 1-T-5*a-(n.highFee:ℝ),1-1/50-T-4*a-(n.highFee:ℝ),
 1-1/50-T-(9/2)*a-(n.highFee:ℝ),Lref-7*a-(n.highFee:ℝ)] j

def sourceWeakReal (n low:Source) (b:ℝ) : ℝ :=
 (low.cap:ℝ)*sourceFReal n low b-((low.B:ℝ)*sourceFReal n low b-sourceTReal n b)/(low.L:ℝ)

theorem sourceScalarReal_rat (n low:Source) (b:ℚ) (j:Fin 16) :
 sourceScalarReal (11243277/2500000) n low (b:ℝ) j=(scalarGate n low b j:ℝ) := by
 fin_cases j <;> simp [sourceScalarReal,scalarGate,sourceAReal_rat,sourceTReal_rat,sourceFReal_rat] <;> ring

theorem seedScalarReal_rat (n low:Source) (b:ℚ) (j:Fin 16) :
 sourceScalarReal (112445673/25000000) n low (b:ℝ) j=(seedScalarGate n low b j:ℝ) := by
 fin_cases j <;> simp [sourceScalarReal,seedScalarGate,sourceAReal_rat,sourceTReal_rat,sourceFReal_rat] <;> ring

theorem sourceWeakReal_rat (n low:Source) (b:ℚ) : sourceWeakReal n low (b:ℝ)=(weakCap n low b:ℝ) := by
 simp [sourceWeakReal,weakCap,sourceFReal_rat,sourceTReal_rat]

theorem sourceScalarReal_affine (K:ℚ) (n low:Source) (j:Fin 16) :
 WidthAffine (fun b => sourceScalarReal K n low b j) := by
 intro x y t
 fin_cases j <;> norm_num [sourceScalarReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring

theorem sourceWeakReal_affine (n low:Source) : WidthAffine (sourceWeakReal n low) := by
 intro x y t
 dsimp [sourceWeakReal]
 rw [sourceFReal_affine n low x y t,sourceTReal_affine n x y t]
 ring
end
end Record1252270103Finite
