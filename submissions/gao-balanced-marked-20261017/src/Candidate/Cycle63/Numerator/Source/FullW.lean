/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Numerator.Source.Actual
import Candidate.Cycle25.Numerator.FullWBound
noncomputable section
set_option maxHeartbeats 2400000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle63.FinalAssembly
theorem source_height_absorption (J t τ : ℝ) (n : ℕ)
    (hJ : 0 ≤ J) (_ht : 0 < t) (hτ : 0 < τ) (hbudget : 2*τ*(1+J) ≤ t) :
    ∀ᶠZ : ℝ in atTop,∀i : ℕ,i ≤ n →
      (3+((3*i+1:ℕ):ℝ)*Z^τ)^J ≤ Z^t := by
  filter_upwards [HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+4) τ hτ,
    eventually_ge_atTop (1:ℝ)] with Z hn hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ.le
  intro i hi
  have hhi : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hheight : 3+((3*i+1:ℕ):ℝ)*Z^τ ≤ Z^(2*τ) := by
    calc
      _ ≤ (3*(n:ℝ)+4)*Z^τ := by push_cast;nlinarith
      _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by rw [←Real.rpow_add hZpos];congr 1;ring
  calc
    _ ≤ (Z^(2*τ))^J := Real.rpow_le_rpow (by positivity) hheight hJ
    _ = Z^(2*τ*J) := (Real.rpow_mul hZpos.le _ _).symm
    _ ≤ Z^t := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith only [hbudget,hτ])

/-- Absorb the single fixed height degree after every amplitude class has
already been placed below the common numerical target. -/
theorem source_absorb_height (V : ℂ) (Z C H J E t : ℝ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hheight : (3+H)^J ≤ Z^t)
    (hV : ‖V‖ ≤ C*(3+H)^J*Z^(E-t)) :
    ‖V‖ ≤ C*Z^E := by
  calc
    _ ≤ C*(3+H)^J*Z^(E-t) := hV
    _ ≤ C*Z^t*Z^(E-t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hheight hC) (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hZ];congr 2;ring

def FullWCellBound (A : ChosenData) (η : Character) (Z τ : ℝ) (n : ℕ)
    (C C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤d → d≤dPlus →
  51/100<a → a≤7/8 → i≤n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*A.D.e) →
  (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W A.F.W (Z^x) (Z^y) Z A.D.e
    (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/
      Cycle63HighTransport.actualNormalizer A.F.modulus ⊤ A.F.S A.D.length 1 2 (fun _=>A.F.w) A.F.W A.F.W Z‖≤
    C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget+A.D.t/8)

/-- The two remaining Mellin integrals and literal source normalization cost
only the displayed normalizer reserve, after the fixed degree is absorbed. -/
theorem actual_fullW_cells (hgap : theta<HeckeZeroSupremum.beta) (A : ChosenData)
    (hAffine : ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀n : ℕ,∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1≤C0 →
    SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ (C0*Z^A.D.t) (Z^(2*τ)) →
    FullWCellBound A η Z τ n C C0 := by
  obtain ⟨J,hJ,hraw⟩ := actual_raw_source hgap A hAffine
  obtain ⟨Ci,hCi,hi⟩ := Cycle25.Weighted.FullWContour.finiteFullW_uniform_norm_bound A.F.W 1 2
    (by norm_num) A.F.complex_support
  obtain ⟨Cn,hCn,hn⟩ := source_normalizer_bound A.D A.F
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  obtain ⟨Cw,hCw,hw⟩ := hraw τ hheight n η
  refine ⟨Ci*Cn*Cw,by positivity,?_⟩
  filter_upwards [hw,hn,source_height_absorption J A.D.t τ n hJ A.D.t_pos hheight.1 hheight.2.2.2.2.2,
    (tendsto_rpow_atTop hheight.1).eventually (eventually_gt_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with Z hw hn hheight hT hZ
  intro C0 hC0 hmom
  have hraw := hw C0 hC0 hmom
  unfold FullWCellBound
  intro rows d a i hd hdmax ha hatop hiidx hsource hrows hrow hfreq hnext hcurrent
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  let B : ℝ := Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget-kernelExponent a A.D.e)
  have hB : 0≤B := by dsimp [B];positivity
  have hintegrated : ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
        (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
        (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W (Z^y)
        ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤B := by
    intro q hq
    have hh := hraw rows d a i hd hdmax ha hatop hiidx hsource hrows hrow hfreq hnext hcurrent q hq
    rw [source_real_profile_eq A.F]
    exact source_absorb_height _ Z (Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps))
      (((3*i+1:ℕ):ℝ)*Z^τ) J (sourceTarget-kernelExponent a A.D.e) A.D.t hZ0
      (by positivity) (hheight i hiidx) (by simpa only [sub_sub,add_comm] using hh)
  have hh := hi A.D.e a (Z^τ) (((3*i+1:ℕ):ℝ)*Z^τ) i A.D.e_pos A.D.e_small ha.le
    (by linarith) hT (by push_cast;have hp:=Real.rpow_nonneg hZ0.le τ;nlinarith)
    A.F.S A.F.exclusions A.F.maximal A.F.first η rows (fun u hu=>(hsource u hu).1)
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (rayCubeFamily A.F.modulus ⊤ le_top) hnext (fun _ y=>(A.F.w y:ℂ))
    (fun j=>Z^(A.D.length j)) A.F.W 1 2 (by norm_num) A.F.complex_support
    (Z^x) (Z^y) Z B (by positivity) (by positivity) hZ0 hB hintegrated
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)).trans_eq
  dsimp only [B]
  rw [←Real.rpow_mul hZ0.le]
  have hp : Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
      Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)=Z^(sourceTarget+A.D.t/8) := by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    unfold kernelExponent
    ring
  calc
    _ = (Ci*Cn*Cw)*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*
        (Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
          Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)) := by ring
    _ = _ := by rw [hp]
end Cycle63.Numerator.Source
