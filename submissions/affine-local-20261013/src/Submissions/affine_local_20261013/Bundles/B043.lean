/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.affine_local_20261013.Bundles.B006
import Submissions.affine_local_20261013.Bundles.B014
import Submissions.affine_local_20261013.Bundles.B030
import Submissions.affine_local_20261013.Bundles.B033
import Submissions.affine_local_20261013.Bundles.B036
import Submissions.affine_local_20261013.Bundles.B037
import Submissions.affine_local_20261013.Bundles.B038
import Submissions.affine_local_20261013.Bundles.B039
import Submissions.affine_local_20261013.Bundles.B040
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorArithmetic
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.GeometricTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.PhysicalSmallTail
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrincipalSlotEstimate

/- BEGIN ORIGINAL MODULE Global.Transport.CubeFloorArithmetic ; sha256 3510e24a5905a8b1a508b978f939beed2fd7eb24fc9436dc3b0b8bd552682fe3 -/
section
/- Adapted from weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/





/-! Adapted from pinned OpenAI/math source; only physical slot geometry changes.
Original analytic inputs remain explicit and unchanged. -/

open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem floorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=Submission20261012.Global.ell) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let α : ℝ := 1/100+12*e+eps*(N+8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)
  have hAA : 0≤ AA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  refine ⟨256*C*(AA+1),by positivity,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=> floorPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell)
  have hD : 0≤ D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤ D*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi (51/100) i hi le_rfl (by norm_num) (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) ((51/100:ℝ)-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hellpos (j : Fin N) : 0≤ ell j := by
      exact (mul_nonneg hdmax hrmin.le).trans (hello j)
    have hq := weightedMean_bounds Finset.univ (fun j=> ell j/d) g (1/50)
      (fun j _=> div_nonneg (hellpos j) hd0.le)
      (by rw [source_slot_length_sum _ _ _ hellsum]; exact div_pos Submission20261012.Global.ell_pos hd0)
      (fun j _=>⟨(hh.1 j).1,by have hhj := (hh.1 j).2.1;dsimp [g,Y,z];norm_num at hhj ⊢;exact hhj⟩)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))≤ Z^(-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(Submission20261012.Global.ell*(4/25))+weightedMean Finset.univ (fun j=> ell j/d) g*Submission20261012.Global.ell+mesh*Submission20261012.Global.ell) from
        source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      have hmul := mul_le_mul_of_nonneg_right hq.2 Submission20261012.Global.ell_pos.le
      linarith
    have hN : 0≤ rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
    have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    convert h using 1 ; dsimp [F,D,α,Y,z,g] ; norm_num ; ring
  have hh := dyadic_weighted_rows α (17/50) D (Z^v) hD (Real.one_le_rpow hZ hv) rows hnorm
    F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  apply (hsum.trans hh).trans
  have hpow : Z^loss*Z^(-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell)*(Z^v)^(1+α-17/50)=
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell) := by
    rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ 256*D*(AA+1)*(Z^v)^(1+α-17/50) := by change 256*D*AA*_≤_;gcongr;linarith
    _ = _ := by
      dsimp [D]
      calc
        _ = (256*C*(AA+1))*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^loss*Z^(-(3*Submission20261012.Global.ell/20)+mesh*Submission20261012.Global.ell)*(Z^v)^(1+α-17/50)) := by ring
        _ = _ := by rw [hpow]

end Submission20261012.Global.HighRowFamily

end


end
/- END ORIGINAL MODULE Global.Transport.CubeFloorArithmetic -/

/- BEGIN ORIGINAL MODULE Global.Transport.GeometricTail ; sha256 8fc330b3ec4cfd0e3891306d3bce8458a9663a5ab1f4e18bc3c092546e7b9a93 -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/



open OAI OAI.SevenEighths

noncomputable section
open scoped BigOperators
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily

lemma large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0 < Z) (n : ℕ) :
    Z^((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+(Submission20261012.Global.h:ℝ)*r)*(Z^((Submission20261012.Global.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+((Submission20261012.Global.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0 < Z) (hr : 8/5+δ < r) :
    Summable (fun n : ℕ=> Z^((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+(Submission20261012.Global.h:ℝ)*r)*(Z^((Submission20261012.Global.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0 < Z) (hr : 8/5+δ < r) :
    (∑'n : ℕ,Z^((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+(Submission20261012.Global.h:ℝ)*r)*(Z^((Submission20261012.Global.h:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+((Submission20261012.Global.h:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤ r ∧ 8/5+δ < r ∧
      (1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+((Submission20261012.Global.h:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((1+Submission20261012.Global.lx/2+Submission20261012.Global.ly)+((Submission20261012.Global.h:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end Submission20261012.Global.HighRowFamily
end


end
/- END ORIGINAL MODULE Global.Transport.GeometricTail -/

/- BEGIN ORIGINAL MODULE Global.Transport.PhysicalSmallTail ; sha256 2d1dbdcd5faa198aefe5d4f48b263c22e34ac9efac3d2f9138fe4eaaf7b203cf -/
section
/- Adapted from WeightedQRH (weighted upstream PR6), preserving the original proof structure. -/




open OAI OAI.SevenEighths

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace Submission20261012.Global.HighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0 < a) (hb : 0 < b) (hB : 0≤ B) (hβ : HeckeZeroSupremum.beta≤(7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀(η : Character) (Z : ℝ),1≤ Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤ Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤ length i) → (∑i,length i)=(Submission20261012.Global.ell:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤ B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖)
      ≤ C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤ N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=> absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=> Z^(length i)) W0 W1
    (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z ((7/8:ℝ)+8*e) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=> Z^(length i)) W0 W1
        (Z^(Submission20261012.Global.lx:ℝ)) (Z^(Submission20261012.Global.ly:ℝ)) Z‖≤ N*g n := norm_finitePhysicalRows_le_absolute
    e ((7/8:ℝ)+8*e) (1/2) (17/50) he he' (by linarith) (by linarith)
    (by linarith [HeckeZeroSupremum.beta_le_one]) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^((7/8:ℝ)-(4+Submission20261012.Global.b)/6-(Submission20261012.Global.ly/2-Submission20261012.Global.h*(17/50-1/6)-1/50)+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end Submission20261012.Global.HighRowFamily
end


end
/- END ORIGINAL MODULE Global.Transport.PhysicalSmallTail -/

/- BEGIN ORIGINAL MODULE Global.Transport.PrincipalSlots ; sha256 925b1211636e15adc4e9d4473f03998f8fa1597f5157d0d3dffafb40753374d8 -/
section
/- Adapted from Submission20261012.Global.Transport weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/




/-!
Principal slot bounds for the original compensated Euler factors at the new
boundary. Adapted from the original OpenAI PrincipalSlotEstimate proofs;
all slot definitions are imported unchanged.
-/
noncomputable section
open scoped Classical BigOperators
open Complex OAI OAI.SevenEighths
namespace Submission20261012.Global.Transport.PrincipalSlots
open Submission20261012.Global.LowCorrection
open ProbeEuler ProbeLocal PrincipalSlotEstimate

theorem principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := weighted_unramified_bound Q A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) hs (by norm_num) (by norm_num)
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have h := principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (principal_correction_lower_bound hQ hA hη hs)

theorem principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hl := principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-theta) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-theta) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by
    have h := coordW_norm_le Q hQ0 (1 : ℂ) 1 (by simp)
    norm_num at h
    exact h.trans (by simpa using hpow (-1) 0 (by norm_num))
  have hR : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖coordD Q η 1 s‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hK : ‖coordK Q η s 1‖ ≤ Q ^ (-s.re) := by
    convert coordK_norm_le Q hQ1 η s 1 hη.le using 1
    norm_num
  have hB := principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-theta) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds]))
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-theta) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-theta) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds]))
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-theta) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := principal_marked_error_bounds hQ hA hη hs
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-theta) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hn := principal_correction_ne_zero hQ hA hη.le hs
  have he := principal_replacement_error hQ hA hη hs
  have hi := principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-theta)) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : theta ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-theta)) * ∑ i ∈ S, w i := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  apply weighted_slot_error S w _ _ hw
  intro i hi
  apply (principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds]))

theorem weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : theta ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-theta)) ^ S.card - 1 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  apply fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

theorem principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by norm_num)
  refine ⟨hV, ?_, ?_⟩
  · rw [principal_W, ← principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : theta ≤ s.re)
    (hsmall : 1440 * P ^ (-theta) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-theta)) :=
  (weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (product_error_linear S.card (by positivity) hsmall)

theorem region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) :=
      weighted_unramified_bound Q A η 1 s w z (by linarith) hA hη (by simp) hs hw hz
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have h := region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (region_correction_lower_bound hQ hA hη hs hw hz)

theorem region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hl := region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
  linarith

theorem region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-theta) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-theta) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := principal_B_norm hQ0 η s hη
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-theta) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-theta) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-theta) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-theta) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-theta) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := region_marked_error_bounds hQ hA hη hs hw hz
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-theta) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have hn := region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := region_replacement_error hQ hA hη hs hw hz
  have hi := region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-theta)) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : theta ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-theta) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  have he := region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : theta ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-theta)) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  have hθ := Submission20261012.Global.Transport.theta_bounds
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-theta)) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-theta) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by first | (solve | norm_num) | (linarith [Submission20261012.Global.Transport.theta_bounds]))
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

end Submission20261012.Global.Transport.PrincipalSlots
end
end
/- END ORIGINAL MODULE Global.Transport.PrincipalSlots -/

/- BEGIN ORIGINAL MODULE Global.Weighted.FullWCellInput ; sha256 58e48d5f854528bb1d69531b0387b946adcc23399cb047ccb945028362d99f2a -/
section




namespace Submission20261012.Global
open OAI OAI.SevenEighths
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set
namespace ProbeAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

/-- The precise remaining analytic estimate, on literal original finite full-w rows.
This definition is an input interface and asserts no unproved bound. -/
def FullWCellsAt {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character)
    (Z τ : ℝ) (n : ℕ) (weightedC C0 : ℝ) : Prop :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∀idx grid : FreeRow→ℕ,
    let rows := supportedNonfloorRows F.S F.maximal
      (rowBand (Z^(1/100:ℝ)) (Z^(Submission20261012.Global.h+D.t))) grid
    (∀u∈rows,idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/D.e⌋₊ ∧
      (51/100:ℝ)+D.e*grid u ≤ 7/8) →
    (∀u∈rows,detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(idx u+1:ℕ)*Z^τ) < 51/100+D.e*grid u+2*D.e) →
    (∀u∈rows,(51/100:ℝ)+D.e*grid u ≤ detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*idx u:ℕ)*Z^τ)) →
    ∀k∈smallDyadicIndices (Z^(Submission20261012.Global.h+D.t)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
      let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
      let Y : Fin D.N→ℝ := fun j=> Z^(D.ell j)
      let T := fun j=> pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
      let hT := nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Y
      let normer := sourceResidueConstant F.W F.W (∏P∈F.S,P)*
        (Probe.principalScalar Finset.univ Z Submission20261012.Global.ell
          (slotMass T (residueWeights (fun _=> F.w) Y)) : ℂ)
      rows'.Nonempty → (1/2:ℝ) < sourceDyadConductor Z D.t k →
      (1/3:ℝ) < 2*(51/100+D.e*j)-1 →
      sourceDyadConductor Z D.t k ≤ Submission20261012.Global.h+3*D.t →
      ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η rows' T hT
          (fun _ y=>(F.w y:ℂ)) Y F.W F.W (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z D.e
          (fun _=>51/100+D.e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖ ≤
        weightedC*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          Z^(Submission20261012.Global.weightedTarget+D.t/8)

end ProbeAssembly
end
end Submission20261012.Global
end
/- END ORIGINAL MODULE Global.Weighted.FullWCellInput -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional ; sha256 0f52159a2929e7b20646f8394589d25a1a637c2f78746ad9d1447871577af615 -/
section




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

namespace SevenEighths.ProbeFinalAssemblyUnconditional
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentEnergyCertifiedExistence CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile

theorem detector_certified_bands:DetectorCertifiedBands:=by
  intro hβ D _hfine F bΦ hbΦ
  have hp:=fixed_parameters D
  apply terminal_certificate (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=> conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1.le
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

theorem dirichlet_nonzero (q:ℕ)(hq:q≠0)(χ:DirichletCharacter ℂ q)(s:ℂ)
    (hs:(7/8:ℝ)< s.re)(hexc:¬(χ=1 ∧ s=1)):
    letI:NeZero q:=⟨hq⟩
    DirichletCharacter.LFunction χ s≠0:=
  dirichlet_of_certified detector_certified_bands q hq χ s hs hexc

theorem zeta_nonzero (s:ℂ)(hs:(7/8:ℝ)< s.re):riemannZeta s≠0:=
  zeta_of_certified detector_certified_bands s hs

end SevenEighths.ProbeFinalAssemblyUnconditional

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional -/
