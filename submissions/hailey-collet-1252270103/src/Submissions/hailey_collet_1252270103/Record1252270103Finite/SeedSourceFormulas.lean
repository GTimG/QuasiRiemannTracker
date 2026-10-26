/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Finite.SourceContinuous
set_option autoImplicit false
namespace Record1252270103Finite

def seedNatural : Source := ⟨1,112445673/25000000,11/200,0,1/10^12,1/10^8,1/10^7⟩
def seedScalarGate (n low : Source) (b : ℚ) (j : Fin 16) : ℚ :=
 let a := sourceA n low b
 let t := sourceT n b
 let T := t+b
 let F := sourceF n low b
 let e := n.allowance
 let Lref := 49/100-(112445673/25000000)*b
 ![sourceDen n low,b-2*e,a,1/75-a,F-T/2-4*e,
 low.B*F-t-b-4*e,1-n.q*low.cap,
 n.lowFee-(n.q*low.B/low.L+n.q*low.cap+4)*e-10*e,
 a-20*e,Lref,1-Lref-1/2-(112445673/25000000)*b-10*e,
 5/6+(499/1000)*Lref-T-9*a-n.highFee,
 1-T-5*a-n.highFee,1-1/50-T-4*a-n.highFee,
 1-1/50-T-(9/2)*a-n.highFee,Lref-7*a-n.highFee] j

def SeedSourceValid (n low : Source) : Prop :=
 0<n.B ∧ n.B≤1 ∧ 1<n.L ∧ 0≤n.cap ∧ n.cap<1 ∧
 1/2≤n.q ∧ n.q<3/4 ∧ n.L<low.L ∧
 0≤crossing n low ∧ crossing n low≤n.cap ∧ crossing n low≤low.cap ∧
 n.allowance=1/10^12 ∧ n.lowFee=1/10^8 ∧ n.highFee=1/10^7 ∧
 (∀ b ∈ [crossing n low,n.cap],
  (∀ j : Fin 16, 0<seedScalarGate n low b j) ∧ 0≤weakCap n low b ∧
  ∀ j : Fin 6, ∀ i : Fin 4, 0<cubicBernstein (fun ν => densityGate n low none b ν (Fin.castLE (by decide) j)) n.q (3/4) i)
instance (n low : Source) : Decidable (SeedSourceValid n low) := by
 unfold SeedSourceValid
 infer_instance

theorem seed_density_endpoint_positive (n low : Source) (hv : SeedSourceValid n low)
 {b : ℚ} (hb : b∈[crossing n low,n.cap]) {ν : ℝ}
 (hν : ν∈Set.Icc (n.q:ℝ) (3/4)) (j : Fin 6) :
 0<sourceDensityReal n low none b ν (Fin.castLE (by decide) j) := by
 have hq := hv.2.2.2.2.2.2.1
 have hcert := hv.2.2.2.2.2.2.2.2.2.2.2.2.2.2 b hb
 rw [source_density_cubic_identity]
 apply cubic_cast_positive _ hq (by simpa using hν)
 exact hcert.2.2 j
#print axioms seed_density_endpoint_positive
end Record1252270103Finite
