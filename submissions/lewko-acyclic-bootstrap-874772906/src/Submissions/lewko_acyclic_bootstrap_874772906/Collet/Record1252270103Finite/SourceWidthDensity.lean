/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Finite.SourceWidth
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section
def sourceDensityWidthReal (n low : Source) (high : Option Source) (b : ℝ) (ν : ℝ) (j : Fin 9) : ℝ :=
 let a : ℝ := sourceAReal n low b
 let T : ℝ := sourceTReal n b+b
 let S : ℝ := b-2*(n.allowance:ℝ)
 let F : ℝ := sourceFReal n low b-(n.allowance:ℝ)
 let fee : ℝ := n.highFee
 let br : ℝ := b
 let t := 15-6*ν
 let w := 5-6*ν
 let H := (a-ν*T)*t+(10-60*a)*ν
 let fixed := H+(ν*F/2-(1-ν)*br-fee)*t
 let core := H+((5/6)*F-(1-ν)*br-fee)*t-10*ν*F
 let tiny := H+(ν*(F-1/50)/2-(1-ν)*br-fee)*t-10*ν*(1/50)
 match high with
 | none =>
   let D2 := 115-54*ν
   let D3 := 185-138*ν
   ![H+3*ν*w*S-fee*t,
     H*D2+14*ν*w*S*t+2*ν*w*w*F-fee*t*D2,
     H*D3+16*ν*w*w*F-fee*t*D3,fixed,core,tiny,1,1,1] j
 | some h =>
   let B : ℝ := h.B
   let L : ℝ := h.L
   let cap : ℝ := h.cap
   let D13 := L*t-10
   let D4 := 10+3*w
   let D23 := L*(10+3*w)-(10+2*w)
   ![H+3*ν*w*S-fee*t,
     H+(2*ν*w*S+ν*w*cap*F)-fee*t,
     H*D13+2*ν*w*(L-1)*S*t+ν*w*(B*t-10)*F-fee*t*D13,
     H*D4+ν*w*S*t+2*ν*w*w*F-fee*t*D4,
     H*D4+(2*ν*w*w+ν*w*cap*t)*F-fee*t*D4,
     H*D23+ν*w*(2*w*(L-1)+B*t-10)*F-fee*t*D23,
     fixed,core,tiny] j

theorem sourceDensityWidthReal_rat (n low:Source) (high:Option Source) (b:ℚ) (ν:ℝ) (j:Fin 9) :
 sourceDensityWidthReal n low high (b:ℝ) ν j=sourceDensityReal n low high b ν j := by
 cases high <;> fin_cases j <;>
  norm_num [sourceDensityWidthReal,sourceDensityReal,sourceAReal_rat,sourceTReal_rat,sourceFReal_rat]
theorem sourceDensityWidthReal_none_0_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 0) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_1_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 1) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_2_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 2) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_3_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 3) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_4_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 4) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_5_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 5) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_6_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 6) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_7_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 7) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_none_8_affine (n low:Source)  (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low none b ν 8) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_0_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 0) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_1_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 1) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_2_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 2) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_3_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 3) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_4_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 4) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_5_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 5) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_6_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 6) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_7_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 7) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_some_8_affine (n low:Source) (h:Source) (ν:ℝ) :
 WidthAffine (fun b => sourceDensityWidthReal n low (some h) b ν 8) := by
 intro x y t
 norm_num [sourceDensityWidthReal,sourceAReal_affine n low x y t,
  sourceTReal_affine n x y t,sourceFReal_affine n low x y t] <;> ring
theorem sourceDensityWidthReal_affine (n low:Source) (high:Option Source) (ν:ℝ) (j:Fin 9) :
 WidthAffine (fun b => sourceDensityWidthReal n low high b ν j) := by
 cases high with
 | none =>
  fin_cases j
  · exact sourceDensityWidthReal_none_0_affine n low ν
  · exact sourceDensityWidthReal_none_1_affine n low ν
  · exact sourceDensityWidthReal_none_2_affine n low ν
  · exact sourceDensityWidthReal_none_3_affine n low ν
  · exact sourceDensityWidthReal_none_4_affine n low ν
  · exact sourceDensityWidthReal_none_5_affine n low ν
  · exact sourceDensityWidthReal_none_6_affine n low ν
  · exact sourceDensityWidthReal_none_7_affine n low ν
  · exact sourceDensityWidthReal_none_8_affine n low ν
 | some h =>
  fin_cases j
  · exact sourceDensityWidthReal_some_0_affine n low h ν
  · exact sourceDensityWidthReal_some_1_affine n low h ν
  · exact sourceDensityWidthReal_some_2_affine n low h ν
  · exact sourceDensityWidthReal_some_3_affine n low h ν
  · exact sourceDensityWidthReal_some_4_affine n low h ν
  · exact sourceDensityWidthReal_some_5_affine n low h ν
  · exact sourceDensityWidthReal_some_6_affine n low h ν
  · exact sourceDensityWidthReal_some_7_affine n low h ν
  · exact sourceDensityWidthReal_some_8_affine n low h ν

theorem cubic_cast_positive_closed (f:ℚ→ℚ) {l r:ℚ} {ν:ℝ}
 (hlr:l≤r) (hν:ν∈Set.Icc (l:ℝ) (r:ℝ))
 (hc:∀ i,0<cubicBernstein f l r i) :
 0<cubicEval (fun i => (cubicCoeffs f i:ℝ)) ν := by
 rcases lt_or_eq_of_le hlr with he | he
 · exact cubic_cast_positive f he hν hc
 · have hx : ν=(l:ℝ) := by
    have hu : ν≤(l:ℝ) := by simpa [←he] using hν.2
    exact le_antisymm hu hν.1
   rw [hx]
   have h := hc 0
   have hid : cubicEval (fun i => (cubicCoeffs f i:ℝ)) (l:ℝ) =
    (cubicBernstein f l r 0:ℝ) := by
    subst r
    simp [cubicEval,cubicBernstein]
   rw [hid]
   exact_mod_cast h

theorem source_density_endpoint_positive_closed (n low:Source) (high:Option Source)
 (hv:SourceValid n low high) {b:ℚ} (hb:b∈[crossing n low,n.cap]) {ν:ℝ}
 (hν:ν∈Set.Icc (n.q:ℝ) (3/4)) (j:Fin 9) :
 0<sourceDensityWidthReal n low high (b:ℝ) ν j := by
 have hq := hv.2.2.2.2.2.2.1
 have hcert := hv.2.2.2.2.2.2.2.2.2.2.2.2 b hb
 rw [sourceDensityWidthReal_rat,source_density_cubic_identity]
 apply cubic_cast_positive_closed _ hq (by simpa using hν)
 exact hcert.2.2 j

theorem source_full_width_gates (n low:Source) (high:Option Source)
 (hv:SourceValid n low high) {b ν:ℝ}
 (hb:b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
 (hν:ν∈Set.Icc (n.q:ℝ) (3/4)) :
 (∀ j,0<sourceScalarReal (11243277/2500000) n low b j) ∧
 0≤sourceWeakReal n low b ∧ ∀ j,0<sourceDensityWidthReal n low high b ν j := by
 have hleft := hv.2.2.2.2.2.2.2.2.2.2.2.2 (crossing n low) (by simp)
 have hright := hv.2.2.2.2.2.2.2.2.2.2.2.2 n.cap (by simp)
 constructor
 · intro j
   apply width_affine_positive (sourceScalarReal_affine (11243277/2500000) n low j) hb
   · rw [sourceScalarReal_rat]
     exact_mod_cast hleft.1 j
   · rw [sourceScalarReal_rat]
     exact_mod_cast hright.1 j
 constructor
 · apply width_affine_nonnegative (sourceWeakReal_affine n low) hb
   · rw [sourceWeakReal_rat]
     exact_mod_cast hleft.2.1
   · rw [sourceWeakReal_rat]
     exact_mod_cast hright.2.1
 · intro j
   apply width_affine_positive (sourceDensityWidthReal_affine n low high ν j) hb
   · exact source_density_endpoint_positive_closed n low high hv (by simp) hν j
   · exact source_density_endpoint_positive_closed n low high hv (by simp) hν j

theorem seed_full_width_gates (n low:Source) (hv:SeedSourceValid n low) {b ν:ℝ}
 (hb:b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ))
 (hν:ν∈Set.Icc (n.q:ℝ) (3/4)) :
 (∀ j,0<sourceScalarReal (112445673/25000000) n low b j) ∧
 0≤sourceWeakReal n low b ∧ ∀ j:Fin 6,
 0<sourceDensityWidthReal n low none b ν (Fin.castLE (by decide) j) := by
 have hleft := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (crossing n low) (by simp)
 have hright := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2 n.cap (by simp)
 constructor
 · intro j
   apply width_affine_positive (sourceScalarReal_affine (112445673/25000000) n low j) hb
   · rw [seedScalarReal_rat]
     exact_mod_cast hleft.1 j
   · rw [seedScalarReal_rat]
     exact_mod_cast hright.1 j
 constructor
 · apply width_affine_nonnegative (sourceWeakReal_affine n low) hb
   · rw [sourceWeakReal_rat]
     exact_mod_cast hleft.2.1
   · rw [sourceWeakReal_rat]
     exact_mod_cast hright.2.1
 · intro j
   apply width_affine_positive (sourceDensityWidthReal_affine n low none ν (Fin.castLE (by decide) j)) hb
   · rw [sourceDensityWidthReal_rat]
     exact seed_density_endpoint_positive n low hv (by simp) hν j
   · rw [sourceDensityWidthReal_rat]
     exact seed_density_endpoint_positive n low hv (by simp) hν j
#print axioms source_full_width_gates
#print axioms seed_full_width_gates
end
end Record1252270103Finite
