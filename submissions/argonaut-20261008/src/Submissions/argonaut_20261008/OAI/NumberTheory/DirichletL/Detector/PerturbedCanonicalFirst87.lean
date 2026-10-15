import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedCanonicalFrontier
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedSelectedTupleFirst87
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set MeasureTheory

namespace SevenEighths.PerturbedCanonicalFirst87

open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open CanonicalQuadraticSieve
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open SevenEighths.ProbeHighRowFamily SevenEighths.ProbeFinalAssembly
open SevenEighths.PerturbedCentral
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.HighFrontierTargets
open SevenEighths.Parameters

local notation "O" => HeckeFamily.O


/-- The actual high-parent contradiction premise supplies the sufficient selected strip. -/
theorem selected_floor_from_parent (hbeta : boundary < HeckeZeroSupremum.beta)
    {e : ℝ} (he : 0 < e) {x : ℂ}
    (hxBeta : HeckeZeroSupremum.beta + 8 * e ≤ x.re) :
    (87 / 100 : ℝ) ≤ x.re := by
  have hb : (87 / 100 : ℝ) < boundary := by
    norm_num [boundary, rho0]
  linarith

theorem selected_gap_from_parent (hbeta : boundary < HeckeZeroSupremum.beta)
    {e : ℝ} (he : 0 < e) {x w : ℂ}
    (hxBeta : HeckeZeroSupremum.beta + 8 * e ≤ x.re)
    (hw : (1 / 2 : ℝ) ≤ w.re) :
    1 + 4 * e ≤ x.re + w.re := by
  have hb : (1 / 2 : ℝ) < boundary := by
    norm_num [boundary, rho0]
  linarith

theorem calibrated_physical_tuple_sum_first87
    (K : ℕ) (e delta a b r B : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hr : (17 / 50 : ℝ) ≤ r)
    (hB : 0 ≤ B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S, P.IsMaximal) (hfirst : FirstTail (4 * e) S) :
    ∃C : ℝ, 0 < C ∧ ∀(eta : Character) (u : FreeRow), u.val ≠ 1 →
      ∀(T : Fin K → Finset PrimeIdeal) (hTout : ∀i P, P ∈ T i → P.val ∉ S),
      (∀P : (∀i, T i), Function.Injective (fun i => (P i).val)) →
      ∀(Y : Fin K → ℝ), (∀i, 1 ≤ Y i) →
      ∀(W : Fin K → ℝ → ℂ),
      (∀i, Function.support (W i) ⊆ Icc a b) →
      (∀i y, ‖W i y‖ ≤ B) →
      ∀(x w z : ℂ), (87 / 100 : ℝ) ≤ x.re →
      HeckeZeroSupremum.beta + 8 * e ≤ x.re →
      (1 / 2 : ℝ) ≤ w.re → z.re = r →
      1 + 4 * e ≤ x.re + w.re →
      (∑P : (∀i, T i), ‖calibratedTupleValue S hS hmax eta u
        (fun i => (P i).val) (fun i => hTout i (P i).val (P i).property)
        W Y x w z‖) ≤
      C * (eta.modulus.absNorm : ℝ) ^ delta *
        ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ (3 / 5 + delta) *
        (∏i, (Y i) ^ r) * (3 + |x.im|) ^ 2 * (3 + |w.im|) ^ 2 := by
  obtain ⟨CL, hCL, hL⟩ := calibrated_scalar_growth e (delta / 2)
    he he1 (by linarith) (by linarith) S hS hmax
  obtain ⟨CG, hCG, hG⟩ := continued_selected_tuple_with_correction_first87 K (delta / 2) a b r B
    (by linarith) ha hb hr hB
  refine ⟨CL * CG, mul_pos hCL hCG, ?_⟩
  intro eta u hu T hTout hdis Y hY W hWS hWB x w z hx hxBeta hw hz hxw
  let N : ℝ := ((Ideal.span {u.val} : Ideal O).absNorm : ℝ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hT : ∀i P, P ∈ T i → Supported P.val ∧ (4 : ℝ) ≤ P.val.absNorm := by
    intro i P hP
    exact ⟨outside_prime_supported S hS.bad P (hTout i P hP),
      by exact_mod_cast hS.tail.norm_four P (hTout i P hP)⟩
  let L : ℂ := star ((calibrationForSet S hmax).residueMonoid u.val) *
    (LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
      HeckeOrigin.continued (rowCharacter S hS.prime u) w *
      HeckeReciprocal.reciprocal
        ((targetRow eta u).excludePrimes S hS.prime) x)
  let G : (∀i, T i) → ℂ := fun P => continuedCorrection
    (markExclusions S (Finset.univ.image (fun i => (P i).val)))
    (markedSourceExclusions S hS
      (Finset.univ.image (fun i => (P i).val))) eta u x w z *
    ∏i, W i (((P i).val.val.absNorm : ℝ) / Y i) *
      ((P i).val.val.absNorm : ℂ) ^ (z - 1) *
      continuedCompensatedLocal eta u (P i).val
        (hT i (P i).val (P i).property).1 x w z
        (star (idealCoeff eta (P i).val.val) *
          ((P i).val.val.absNorm : ℂ) ^ x)
        (((P i).val.val.absNorm : ℂ) ^ (-w))
  have heq (P : ∀i, T i) : calibratedTupleValue S hS hmax eta u
      (fun i => (P i).val) (fun i => hTout i (P i).val (P i).property)
      W Y x w z = L * G P :=
    calibratedTupleValue_factor S hS hmax eta u _ (hdis P) _ W Y x w z
  have hLb : ‖L‖ ≤ CL * (eta.modulus.absNorm : ℝ) ^ (delta / 2) *
      N ^ (3 / 5 + delta / 2) * (3 + |x.im|) ^ 2 *
      (3 + |w.im|) ^ 2 :=
    hL eta u hu x w z hxBeta hw (by rw [hz]; exact hr)
  have hGb : (∑P : (∀i, T i), ‖G P‖) ≤
      CG * N ^ (delta / 2) * ∏i, (Y i) ^ r := by
    exact hG (4 * e) S hS hfirst eta u T hT Y hY W hWS hWB x w z
      hx (by linarith) hz hxw
  have heta : (eta.modulus.absNorm : ℝ) ^ (delta / 2) ≤
      (eta.modulus.absNorm : ℝ) ^ delta :=
    Real.rpow_le_rpow_of_exponent_le
      (HeckeLogarithmicInput.modulus_norm_ge_one eta) (by linarith)
  have hYP : 0 ≤ ∏i, (Y i) ^ r :=
    Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by linarith [hY i]) _
  simp_rw [heq, norm_mul]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (CL * (eta.modulus.absNorm : ℝ) ^ (delta / 2) *
          N ^ (3 / 5 + delta / 2) * (3 + |x.im|) ^ 2 *
          (3 + |w.im|) ^ 2) *
        (CG * N ^ (delta / 2) * ∏i, (Y i) ^ r) :=
      mul_le_mul hLb hGb
        (Finset.sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ ≤ (CL * (eta.modulus.absNorm : ℝ) ^ delta *
          N ^ (3 / 5 + delta / 2) * (3 + |x.im|) ^ 2 *
          (3 + |w.im|) ^ 2) *
        (CG * N ^ (delta / 2) * ∏i, (Y i) ^ r) := by gcongr
    _ = (CL * CG) * (eta.modulus.absNorm : ℝ) ^ delta *
        N ^ (3 / 5 + delta) * (∏i, (Y i) ^ r) *
        (3 + |x.im|) ^ 2 * (3 + |w.im|) ^ 2 := by
      have hp : N ^ (3 / 5 + delta / 2) * N ^ (delta / 2) =
          N ^ (3 / 5 + delta) := by
        rw [← Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (CL * CG) * (eta.modulus.absNorm : ℝ) ^ delta *
            (N ^ (3 / 5 + delta / 2) * N ^ (delta / 2)) *
            (∏i, (Y i) ^ r) * (3 + |x.im|) ^ 2 *
            (3 + |w.im|) ^ 2 := by ring
        _ = _ := by rw [hp]

/- Threshold-free dyadic summation proof adapted from official DyadBound.
   The per-row input retains this file's actual first-region domain. -/
private theorem calibrated_physical_row_dyad_first87 (K : ℕ) (e δ a b r B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (U : ℝ),1≤U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(87/100:ℝ)≤x.re → HeckeZeroSupremum.beta+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r → 1+4*e≤x.re+w.re →
      (∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_tuple_sum_first87 K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  let A : ℝ := ProbeSelectedPrimeSums.annularPower 1 2 (3/5+δ-r)
  have hA : 0<A := by
    have hh := le_max_left ((1:ℝ)^(3/5+δ-r)) ((2:ℝ)^(3/5+δ-r))
    rw [Real.one_rpow] at hh
    simpa only [A,ProbeSelectedPrimeSums.annularPower,Real.one_rpow] using (lt_of_lt_of_le zero_lt_one hh)
  refine ⟨256*C*A,by positivity,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz hxw
  let F : FreeRow→ℝ := fun u=>∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
    (fun i=>hT i (P i).val (P i).property) W Y x w z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^δ*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈R) : F u≤D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ) := by
    have hh := hmain η u (hR u hu).1 T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz hxw
    apply hh.trans_eq
    dsimp [D]
    ring
  have heq (u : FreeRow) :
      (∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)=
      ‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    simp only [norm_mul,Finset.mul_sum,F]
  simp_rw [heq]
  apply (dyadic_weighted_rows (3/5+δ) r D U hD hU R (fun u hu=>(hR u hu).2) F hF z hz).trans_eq
  change 256*D*A*U^(1+(3/5+δ)-r)=_
  rw [show (1:ℝ)+(3/5+δ)-r=8/5+δ-r by ring]
  dsimp [D]
  ring

/-- The corresponding First-strip dyadic integral, conditional only on the leaf above. -/

theorem calibrated_physical_dyad_integral_first87
    (K : ℕ) (e delta a b r B sigma upsilon : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hr : (17 / 50 : ℝ) ≤ r)
    (hB : 0 ≤ B) (hsigma : (87 / 100 : ℝ) ≤ sigma)
    (hsigmaBeta : HeckeZeroSupremum.beta + 8 * e ≤ sigma)
    (hupsilon : (1 / 2 : ℝ) ≤ upsilon)
    (hgap : 1 + 4 * e ≤ sigma + upsilon)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S, P.IsMaximal) (hfirst : FirstTail (4 * e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) :
    ∃C : ℝ, 0 < C ∧ ∀(eta : Character) (U : ℝ), 1 ≤ U →
      ∀R : Finset FreeRow,
      (∀u∈R, u.val ≠ 1 ∧ U ≤ ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ∧
        ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ≤ 2 * U) →
      ∀(T : Fin K → Finset PrimeIdeal) (hT : ∀i P, P ∈ T i → P.val ∉ S),
      (∀P : (∀i, T i), Function.Injective (fun i => (P i).val)) →
      ∀(Y : Fin K → ℝ), (∀i, 1 ≤ Y i) →
      ∀(W : Fin K → ℝ → ℂ),
      (∀i, Function.support (W i) ⊆ Icc a b) →
      (∀i y, ‖W i y‖ ≤ B) →
      ∀X Y0 Z : ℝ, 0 < X → 0 < Y0 → 0 < Z →
      Integrable (fun p : HeightSpace => ‖sourceMellinWeight W0 W1 X Y0 Z
        ((sigma : ℂ) + p.1.1 * Complex.I)
        ((upsilon : ℂ) + p.2 * Complex.I)
        ((r : ℂ) + p.1.2 * Complex.I)‖ *
        physicalDyadNorm S hS hmax eta R T hT W Y
          ((sigma : ℂ) + p.1.1 * Complex.I)
          ((upsilon : ℂ) + p.2 * Complex.I)
          ((r : ℂ) + p.1.2 * Complex.I)) heightMeasure ∧
      (∫p : HeightSpace, ‖sourceMellinWeight W0 W1 X Y0 Z
        ((sigma : ℂ) + p.1.1 * Complex.I)
        ((upsilon : ℂ) + p.2 * Complex.I)
        ((r : ℂ) + p.1.2 * Complex.I)‖ *
        physicalDyadNorm S hS hmax eta R T hT W Y
          ((sigma : ℂ) + p.1.1 * Complex.I)
          ((upsilon : ℂ) + p.2 * Complex.I)
          ((r : ℂ) + p.1.2 * Complex.I) ∂heightMeasure) ≤
        C * (eta.modulus.absNorm : ℝ) ^ delta * U ^ (8 / 5 + delta - r) *
          (∏i, (Y i) ^ r) * (X ^ (1 / 2 - r) * Z ^ (sigma + r - 1) *
            Y0 ^ (upsilon - 1)) := by
  obtain ⟨C, hC, htuple⟩ := calibrated_physical_row_dyad_first87
    K e delta a b r B he he1 hdelta hdelta1 ha hb hr hB
    S hS hmax hfirst
  obtain ⟨D, hDpos, hprofile⟩ := source_profile_integral_bound W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1
    sigma sigma r r upsilon upsilon (by linarith)
  refine ⟨D * C, mul_pos hDpos hC, ?_⟩
  intro eta U hU R hR T hT hdis Y hY W hWS hWB X Y0 Z hX hY0 hZ
  let A : ℝ := C * (eta.modulus.absNorm : ℝ) ^ delta *
    U ^ (8 / 5 + delta - r) * (∏i, (Y i) ^ r)
  have hYP : 0 ≤ ∏i, (Y i) ^ r :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (zero_le_one.trans (hY i)) _)
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbnd (p : HeightSpace) : physicalDyadNorm S hS hmax eta R T hT W Y
      ((sigma : ℂ) + p.1.1 * Complex.I)
      ((upsilon : ℂ) + p.2 * Complex.I)
      ((r : ℂ) + p.1.2 * Complex.I) ≤
      A * (3 + |p.1.1|) ^ 2 * (3 + |p.2|) ^ 2 := by
    have hh := htuple eta U hU R hR T hT hdis Y hY W hWS hWB
      ((sigma : ℂ) + p.1.1 * Complex.I)
      ((upsilon : ℂ) + p.2 * Complex.I)
      ((r : ℂ) + p.1.2 * Complex.I)
      (by simpa using hsigma) (by simpa using hsigmaBeta)
      (by simpa using hupsilon) (by simp) (by simpa using hgap)
    simpa only [A, physicalDyadNorm, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      mul_one, mul_zero, add_zero, zero_add] using hh
  obtain ⟨hi, hb⟩ := hprofile sigma ⟨le_rfl, le_rfl⟩
    r ⟨le_rfl, le_rfl⟩ upsilon ⟨le_rfl, le_rfl⟩
    X Y0 Z hX hY0 hZ A hA _
    (physicalDyadNorm_onLines_aestronglyMeasurable S hS hmax eta R T hT W Y
      sigma upsilon r)
    (fun p => physicalDyadNorm_nonneg S hS hmax eta R T hT W Y _ _ _) hbnd
  refine ⟨hi, hb.trans_eq ?_⟩
  dsimp [A]
  ring

/-! ## Shifted total-mass scale identities -/

end SevenEighths.PerturbedCanonicalFirst87
end
end OAI
