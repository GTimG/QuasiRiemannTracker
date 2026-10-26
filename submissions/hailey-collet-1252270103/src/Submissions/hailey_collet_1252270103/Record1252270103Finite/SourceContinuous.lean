/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceFormulas
set_option autoImplicit false
namespace Record1252270103Finite
noncomputable section

def cubicEval (c : Fin 4 → ℝ) (ν : ℝ) : ℝ := c 0+c 1*ν+c 2*ν^2+c 3*ν^3

def cubicBernReal (c : Fin 4 → ℝ) (l r : ℝ) (i : Fin 4) : ℝ :=
 let a0 := cubicEval c l
 let a1 := (r-l)*(c 1+2*c 2*l+3*c 3*l^2)
 let a2 := (r-l)^2*(c 2+3*c 3*l)
 let a3 := (r-l)^3*c 3
 ![a0,a0+a1/3,a0+2*a1/3+a2/3,a0+a1+a2+a3] i

theorem cubic_positive (c : Fin 4 → ℝ) {l r ν : ℝ}
 (hlr : l<r) (hν : ν∈Set.Icc l r) (hc : ∀ i, 0<cubicBernReal c l r i) :
 0<cubicEval c ν := by
 have h1 : 0≤ν-l := sub_nonneg.mpr hν.1
 have h2 : 0≤r-ν := sub_nonneg.mpr hν.2
 have hc1 := hc (1:Fin 4)
 have hc2 := hc (2:Fin 4)
 have hp0 : 0≤cubicBernReal c l r 0*(r-ν)^3 := mul_nonneg (le_of_lt (hc 0)) (by positivity)
 have hp1 : 0≤3*cubicBernReal c l r 1*(ν-l)*(r-ν)^2 := by positivity
 have hp2 : 0≤3*cubicBernReal c l r 2*(ν-l)^2*(r-ν) := by positivity
 have hp3 : 0≤cubicBernReal c l r 3*(ν-l)^3 := mul_nonneg (le_of_lt (hc 3)) (by positivity)
 have hid : (r-l)^3*cubicEval c ν =
  cubicBernReal c l r 0*(r-ν)^3+3*cubicBernReal c l r 1*(ν-l)*(r-ν)^2+
  3*cubicBernReal c l r 2*(ν-l)^2*(r-ν)+cubicBernReal c l r 3*(ν-l)^3 := by
  norm_num [cubicBernReal,cubicEval]
  ring
 have hp : 0<(r-l)^3*cubicEval c ν := by
  rw [hid]
  rcases eq_or_lt_of_le hν.1 with he | he
  · have ht : 0<cubicBernReal c l r 0*(r-ν)^3 := by
     apply mul_pos (hc 0)
     apply pow_pos
     linarith
    linarith
  · have ht : 0<cubicBernReal c l r 3*(ν-l)^3 := mul_pos (hc 3) (pow_pos (sub_pos.mpr he) 3)
    linarith
 exact (mul_pos_iff_of_pos_left (pow_pos (sub_pos.mpr hlr) 3)).mp hp

theorem cubic_cast_positive (f : ℚ→ℚ) {l r : ℚ} {ν : ℝ}
 (hlr : l<r) (hν : ν∈Set.Icc (l:ℝ) (r:ℝ))
 (hc : ∀ i, 0<cubicBernstein f l r i) :
 0<cubicEval (fun i => (cubicCoeffs f i:ℝ)) ν := by
 apply cubic_positive _ (by exact_mod_cast hlr) hν
 intro i
 have h := hc i
 have he : cubicBernReal (fun k => (cubicCoeffs f k:ℝ)) (l:ℝ) (r:ℝ) i =
  (cubicBernstein f l r i:ℝ) := by
  fin_cases i <;> simp [cubicBernReal,cubicBernstein,cubicEval] <;> ring
 rw [he]
 exact_mod_cast h

/-- The real polynomial with exactly the cleared NF12/NF13 formulas. -/
def sourceDensityReal (n low : Source) (high : Option Source) (b : ℚ) (ν : ℝ) (j : Fin 9) : ℝ :=
 let a : ℝ := (sourceA n low b:ℚ)
 let T : ℝ := (sourceT n b+b:ℚ)
 let S : ℝ := (b-2*n.allowance:ℚ)
 let F : ℝ := (sourceF n low b-n.allowance:ℚ)
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

theorem source_density_none_0_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 0 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 0) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_1_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 1 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 1) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_2_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 2 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 2) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_3_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 3 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 3) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_4_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 4 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 4) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_5_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 5 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 5) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_6_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 6 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 6) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_7_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 7 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 7) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_none_8_identity (n low : Source)  (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low none b ν 8 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low none b z 8) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_0_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 0 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 0) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_1_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 1 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 1) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_2_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 2 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 2) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_3_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 3 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 3) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_4_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 4 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 4) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_5_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 5 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 5) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_6_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 6 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 6) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_7_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 7 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 7) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_some_8_identity (n low : Source) (h:Source) (b : ℚ) (ν : ℝ) :
 sourceDensityReal n low (some h) b ν 8 =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low (some h) b z 8) i:ℝ)) ν := by
 norm_num [sourceDensityReal,densityGate,cubicEval,cubicCoeffs] <;> ring
theorem source_density_cubic_identity (n low : Source) (high : Option Source) (b : ℚ) (ν : ℝ) (j : Fin 9) :
 sourceDensityReal n low high b ν j =
 cubicEval (fun i => (cubicCoeffs (fun z => densityGate n low high b z j) i:ℝ)) ν := by
 cases high with
 | none =>
  fin_cases j
  · exact source_density_none_0_identity n low b ν
  · exact source_density_none_1_identity n low b ν
  · exact source_density_none_2_identity n low b ν
  · exact source_density_none_3_identity n low b ν
  · exact source_density_none_4_identity n low b ν
  · exact source_density_none_5_identity n low b ν
  · exact source_density_none_6_identity n low b ν
  · exact source_density_none_7_identity n low b ν
  · exact source_density_none_8_identity n low b ν
 | some h =>
  fin_cases j
  · exact source_density_some_0_identity n low h b ν
  · exact source_density_some_1_identity n low h b ν
  · exact source_density_some_2_identity n low h b ν
  · exact source_density_some_3_identity n low h b ν
  · exact source_density_some_4_identity n low h b ν
  · exact source_density_some_5_identity n low h b ν
  · exact source_density_some_6_identity n low h b ν
  · exact source_density_some_7_identity n low h b ν
  · exact source_density_some_8_identity n low h b ν

/-- Full closed density interval at either certified width endpoint. -/
theorem source_density_endpoint_positive (n low : Source) (high : Option Source)
 (hv : SourceValid n low high) (hq : n.q<3/4) {b : ℚ}
 (hb : b∈[crossing n low,n.cap]) {ν : ℝ}
 (hν : ν∈Set.Icc (n.q:ℝ) (3/4)) (j : Fin 9) :
 0<sourceDensityReal n low high b ν j := by
 have hcert := hv.2.2.2.2.2.2.2.2.2.2.2.2 b hb
 rw [source_density_cubic_identity]
 apply cubic_cast_positive (fun z => densityGate n low high b z j) hq (by simpa using hν)
 exact hcert.2.2 j
#print axioms cubic_positive
#print axioms source_density_cubic_identity
#print axioms source_density_endpoint_positive
end
end Record1252270103Finite
