/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B024
import Candidate.Bundles.B031
import OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
import OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorArithmetic
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
import OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobal
import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CubeSlotExponent; sha256 52ac8aee806e99c324b9bc70560d9e197661f6b07f1718d05cb6b64bc57895e2 -/
section
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                             
                                                            
                                                                  

/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=Cycle61.Arithmetic.ell) :
    (∑j∈slots,ell j/d)=Cycle61.Arithmetic.ell/d := by
  rw [←Finset.sum_div,hell]

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=Cycle61.Arithmetic.ell) :
    weightedMean slots (fun j=>ell j/d) g= (1/Cycle61.Arithmetic.ell)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=Cycle61.Arithmetic.ell) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(Cycle61.Arithmetic.ell*(4/25))+weightedMean slots (fun j=>ell j/d) g*Cycle61.Arithmetic.ell+mesh*Cycle61.Arithmetic.ell) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  field_simp [Cycle61.Arithmetic.ell_pos.ne']

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end SevenEighths.Cycle61HighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CubeSlotExponent -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CubeFloorArithmetic; sha256 1113f428775daf83be2d434c07619d0861aade5f479e9eb5bbc08fa583ca6d21 -/
section
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                                
                                                  
                                                           

/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem floorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=Cycle61.Arithmetic.ell) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let α : ℝ := 1/100+12*e+eps*(N+8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)
  have hAA : 0≤AA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  refine ⟨256*C*(AA+1),by positivity,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=>floorPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤D*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi (51/100) i hi le_rfl (by norm_num) (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) ((51/100:ℝ)-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hellpos (j : Fin N) : 0≤ell j := by
      exact (mul_nonneg hdmax hrmin.le).trans (hello j)
    have hq := weightedMean_bounds Finset.univ (fun j=>ell j/d) g (1/50)
      (fun j _=>div_nonneg (hellpos j) hd0.le)
      (by rw [source_slot_length_sum _ _ _ hellsum]; exact div_pos Cycle61.Arithmetic.ell_pos hd0)
      (fun j _=>⟨(hh.1 j).1,by have hhj := (hh.1 j).2.1;dsimp [g,Y,z];norm_num at hhj ⊢;exact hhj⟩)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))≤Z^(-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(Cycle61.Arithmetic.ell*(4/25))+weightedMean Finset.univ (fun j=>ell j/d) g*Cycle61.Arithmetic.ell+mesh*Cycle61.Arithmetic.ell) from
        source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      have hmul := mul_le_mul_of_nonneg_right hq.2 Cycle61.Arithmetic.ell_pos.le
      linarith
    have hN : 0≤rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
    have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    convert h using 1 ; dsimp [F,D,α,Y,z,g] ; norm_num ; ring
  have hh := dyadic_weighted_rows α (17/50) D (Z^v) hD (Real.one_le_rpow hZ hv) rows hnorm
    F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  apply (hsum.trans hh).trans
  have hpow : Z^loss*Z^(-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)*(Z^v)^(1+α-17/50)=
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell) := by
    rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ 256*D*(AA+1)*(Z^v)^(1+α-17/50) := by change 256*D*AA*_≤_;gcongr;linarith
    _ = _ := by
      dsimp [D]
      calc
        _ = (256*C*(AA+1))*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^loss*Z^(-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)*(Z^v)^(1+α-17/50)) := by ring
        _ = _ := by rw [hpow]

end SevenEighths.Cycle61HighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CubeFloorArithmetic -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.FloorExponent; sha256 00280bd528f4f7c3431c4b9bdb6af2e62a20adb759b39eb0011ee3703233ed57 -/
section
/- Ported from Cycle25 transport and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                           
noncomputable section
namespace Cycle61.Transport
def centralScale (a e : ℝ) : ℝ := lx*(4/25)+(a+16*e-33/50)+ly*(-a-6*e)
lemma physical_scale_identity (Z a e : ℝ) (hZ : 0<Z) :
    (Z^lx)^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^ly)^(-a-6*e)=Z^(centralScale a e) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ, ←Real.rpow_add hZ]
  rfl
def floorSourceExponent (v : ℝ) : ℝ := centralScale (51/100) 0+v*(67/100)-3*ell/20
def floorRealLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16-6*ly)*e+v*(12*e+eps*(N+8))+loss+mesh*ell
lemma floor_source_margin {v : ℝ} (hv : v≤h+rowExtension) :
    floorSourceExponent v≤signal theta-1/100 := by
  norm_num [floorSourceExponent, centralScale, signal, Cycle61.Assembly.signal,
    Cycle61.Assembly.signalShift, rowExtension, h, theta, lx, ly, ell,
    Cycle61.Arithmetic.x, Cycle61.Arithmetic.y, Cycle61.Arithmetic.ell,
    Cycle61.Arithmetic.h, Cycle61.Arithmetic.theta] at *
  linarith
lemma floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ} (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    floorRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+mesh*ell := by
  have hp := mul_le_mul_of_nonneg_right hv (show 0≤12*e+eps*(N+8) by positivity)
  dsimp [floorRealLoss]
  nlinarith [Cycle61.Transport.ly_coarse, mul_nonneg he (by linarith [Cycle61.Transport.ly_coarse] : 0≤ly-1/3)]
end Cycle61.Transport

end
/- END ORIGINAL Cycle61.Assembly.Transport.FloorExponent -/

/- BEGIN ORIGINAL Cycle61.Assembly.Transport.CubeFloorGlobal; sha256 4ac5f492adf003b3757d1499494834fe4157d8f14483710a2dccba177d20872b -/
section
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
                                               
                                                            
                                               
                                      
                                                     
                                                            
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.Cycle61HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem globalFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_global_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0 < dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0 < mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=Cycle61.Arithmetic.ell) :
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (globalFloorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell) := by
  obtain ⟨C,hC,hbound⟩ := actual_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  let θ : ℝ := 67/100+12*e+eps*(N+8)
  have hθ : 0<θ := by dsimp [θ];positivity
  obtain ⟨Cg,hCg,hgeom⟩ := bounded_dyadic_power_sum θ hθ
  refine ⟨C*Cg,mul_pos hC hCg,?_⟩
  intro η
  filter_upwards [hbound η,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0 < Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Rn : ℕ→Finset FreeRow := fun k=>rows∩dyadicRows 1 k
  let term : FreeRow→ℂ := fun u=>frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=>globalFloorPoolOutside M H S N c b Y j _ (P j).property) W Y
      (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)
  have hD : 0≤D := by dsimp [D];positivity
  have hdyad (k : ℕ) : ‖∑u∈Rn k,term u‖≤D*((2:ℝ)^k)^θ := by
    let vk := Real.logb Z ((2:ℝ)^k)
    have hvk : 0≤vk := Real.logb_nonneg hZ (one_le_pow₀ (by norm_num))
    have heq : Z^vk=(2:ℝ)^k := Real.rpow_logb hZp hZ.ne' (by positivity)
    have hsub : Rn k⊆rows := Finset.inter_subset_left
    have hn : ∀u∈Rn k,Z^vk≤rowNorm u ∧ rowNorm u≤2*Z^vk := by
      intro u hu
      have h := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [heq,one_mul] using And.intro h.1 h.2.le
    have hh := hb d hd hd' vk hvk (Rn k) (fun u hu=>hrows u (hsub hu)) hn i hi
      (fun u hu=>hbin u (hsub hu)) t ht
    change ‖∑u∈Rn k,term u‖≤_ at hh
    apply hh.trans_eq
    have hp : Z^(vk*θ+loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)=Z^(loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)*((2:ℝ)^k)^θ := by
      rw [show vk*θ+loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell=(loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)+vk*θ by ring,Real.rpow_add hZp,
        Real.rpow_mul hZp.le,heq]
    change C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(vk*θ+loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)=_
    rw [hp]
    dsimp [D]
    ring
  have hpart := retained_dyadic_sum rows (Z^v) (fun u hu=>⟨(hrows u hu).1,hnorm u hu⟩) term
  change ‖∑u∈rows,term u‖≤_
  rw [hpart]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^v),‖∑u∈Rn k,term u‖ := norm_sum_le _ _
    _ ≤ ∑k∈smallDyadicIndices (Z^v),D*((2:ℝ)^k)^θ := Finset.sum_le_sum (fun k _=>hdyad k)
    _ = D*∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^θ := (Finset.mul_sum _ _ _).symm
    _ ≤ D*(Cg*(Z^v)^θ) := mul_le_mul_of_nonneg_left
      (hgeom (Z^v) (by positivity) (smallDyadicIndices (Z^v)) (fun k hk=>mem_smallDyadicIndices.mp hk)) hD
    _ = _ := by
      have hp : Z^(loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)*(Z^v)^θ=Z^(v*θ+loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell) := by
        rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp]
        congr 1
        ring
      dsimp [D]
      calc
        _ = (C*Cg)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^(loss-(3*Cycle61.Arithmetic.ell/20)+mesh*Cycle61.Arithmetic.ell)*(Z^v)^θ) := by ring
        _ = _ := by rw [hp]

end SevenEighths.Cycle61HighRowFamily

end

end OAI

end
/- END ORIGINAL Cycle61.Assembly.Transport.CubeFloorGlobal -/
