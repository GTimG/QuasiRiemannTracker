import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedFloorRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.XBoundary

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set MeasureTheory

namespace SevenEighths.PerturbedCanonicalFrontier

open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open ProbeRaySlots
open OAI.CanonicalQuadraticSieve (Supported)
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open SevenEighths.ProbeHighRowFamily SevenEighths.ProbeFinalAssembly
open SevenEighths.PerturbedCentral
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.Parameters

local notation "O" => HeckeFamily.O

private theorem canonicalPoolOutside
    {M : Ideal O} (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (N : ℕ) (a b : ℝ) (Y : Fin N → ℝ) :
    ∀j P, P ∈ pool (RayQuotient.identityClass M H) S a b (Y j) → P.val ∉ S :=
  fun j P hP => (mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

/-!
# First-region frontier for canonical-minus-central

The total-mass and shifted-scale algebra closes at the new geometry.  The first
unavailable analytic declaration is a selected-tuple estimate in the First
region.  The proposition below states that leaf with the actual OAI factors;
it is strictly smaller than a canonical-probe, transport, or high-probe
assumption.
-/

/--
First-region replacement for
`continued_selected_tuple_with_correction`.  No inhabitant is asserted here.
The conclusion deliberately retains the old sharp `N^delta * prod Y^r` cost;
the currently available crude `selectedFirstBound` does not imply it.
-/
def FirstSelectedTupleInput : Prop :=
  ∀(K : ℕ) (delta a b r B : ℝ),
    0 < delta → 0 < a → 0 < b → (17 / 50 : ℝ) ≤ r → 0 ≤ B →
    ∃C : ℝ, 0 < C ∧
    ∀(eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S),
      FirstTail eps S → ∀(eta : Character) (u : FreeRow)
      (T : Fin K → Finset PrimeIdeal)
      (hT : ∀i P, P ∈ T i → Supported P.val ∧ (4 : ℝ) ≤ P.val.absNorm)
      (Y : Fin K → ℝ), (∀i, 1 ≤ Y i) →
      ∀(W : Fin K → ℝ → ℂ),
      (∀i, Function.support (W i) ⊆ Icc a b) →
      (∀i y, ‖W i y‖ ≤ B) →
      ∀(x w z : ℂ), (51 / 100 : ℝ) ≤ x.re →
      -(1 / 100 : ℝ) ≤ w.re → z.re = r →
      1 + eps ≤ x.re + w.re →
      (∑P : (∀i, T i), ‖continuedCorrection
        (markExclusions S (Finset.univ.image (fun i => (P i).val)))
        (markedSourceExclusions S hS
          (Finset.univ.image (fun i => (P i).val))) eta u x w z *
        ∏i, W i (((P i).val.val.absNorm : ℝ) / Y i) *
          ((P i).val.val.absNorm : ℂ) ^ (z - 1) *
          continuedCompensatedLocal eta u (P i).val
            (hT i (P i).val (P i).property).1 x w z
            (star (idealCoeff eta (P i).val.val) *
              ((P i).val.val.absNorm : ℂ) ^ x)
            (((P i).val.val.absNorm : ℂ) ^ (-w))‖) ≤
        C * ((Ideal.span {u.val} : Ideal O).absNorm : ℝ) ^ delta *
          ∏i, (Y i) ^ r

/--
Assuming only the selected-tuple leaf, the full calibrated tuple estimate in
the First strip follows.  The reciprocal/numerator factor is the already
proved `calibrated_scalar_growth`; no principal main-term estimate enters.
-/
theorem calibrated_physical_tuple_sum_first_of_selected
    (hselected : FirstSelectedTupleInput)
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
      ∀(x w z : ℂ), (51 / 100 : ℝ) ≤ x.re →
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
  obtain ⟨CG, hCG, hG⟩ := hselected K (delta / 2) a b r B
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
private theorem calibrated_physical_row_dyad_first_of_selected (hselected : FirstSelectedTupleInput) (K : ℕ) (e δ a b r B : ℝ)
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
      ∀(x w z : ℂ),(51/100:ℝ)≤x.re → HeckeZeroSupremum.beta+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r → 1+4*e≤x.re+w.re →
      (∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_tuple_sum_first_of_selected hselected K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
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
theorem calibrated_physical_dyad_integral_first_of_selected
    (hselected : FirstSelectedTupleInput)
    (K : ℕ) (e delta a b r B sigma upsilon : ℝ)
    (he : 0 < e) (he1 : e < 1 / 1000)
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hr : (17 / 50 : ℝ) ≤ r)
    (hB : 0 ≤ B) (hsigma : (51 / 100 : ℝ) ≤ sigma)
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
  obtain ⟨C, hC, hTuple⟩ := calibrated_physical_row_dyad_first_of_selected
    hselected K e delta a b r B he he1 hdelta hdelta1 ha hb hr hB
    S hS hmax hfirst
  obtain ⟨D, hD, hprofile⟩ := source_profile_integral_bound W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1
    sigma sigma r r upsilon upsilon (by linarith)
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro eta U hU R hR T hT hdis Y hY W hWS hWB X Y0 Z hX hY0 hZ
  let A : ℝ := C * (eta.modulus.absNorm : ℝ) ^ delta *
    U ^ (8 / 5 + delta - r) * (∏i, (Y i) ^ r)
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hprod : 0 ≤ ∏i, (Y i) ^ r :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (zero_le_one.trans (hY i)) _)
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg hU0 _)) hprod
  have hbnd (p : HeightSpace) : physicalDyadNorm S hS hmax eta R T hT W Y
      ((sigma : ℂ) + p.1.1 * Complex.I)
      ((upsilon : ℂ) + p.2 * Complex.I)
      ((r : ℂ) + p.1.2 * Complex.I) ≤
      A * (3 + |p.1.1|) ^ 2 * (3 + |p.2|) ^ 2 := by
    have hh := hTuple eta U hU R hR T hT hdis Y hY W hWS hWB
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

lemma physical_scale_power_totalE {K : ℕ}
    (Z : ℝ) (hZ : 0 < Z) (ell : Fin K → ℝ)
    (hsum : ∑i, ell i = totalE) (sigma upsilon r : ℝ) :
    (∏i, (Z ^ (ell i)) ^ r) *
      ((Z ^ sourceLx) ^ (1 / 2 - r) * Z ^ (sigma + r - 1) *
        (Z ^ sourceLy) ^ (upsilon - 1)) =
      Z ^ (sigma - 1 + sourceLx / 2 + sourceLy * (upsilon - 1) +
        (1 - sourceLx + totalE) * r) := by
  rw [ProbeHighRowFamily.physical_scale_power Z hZ, hsum]

lemma small_source_scale_totalE {K : ℕ}
    (Z : ℝ) (hZ : 0 < Z) (ell : Fin K → ℝ)
    (hsum : ∑i, ell i = totalE) (beta e : ℝ) :
    (∏i, (Z ^ (ell i)) ^ (17 / 50 : ℝ)) *
      ((Z ^ sourceLx) ^ (1 / 2 - (17 / 50 : ℝ)) *
        Z ^ (beta + 8 * e + (17 / 50 : ℝ) - 1) *
        (Z ^ sourceLy) ^ ((1 / 2 : ℝ) - 1)) =
      Z ^ (beta - 11 / 16 - 79 / 800 + 8 * e + 51 * rho0 / 100) := by
  rw [physical_scale_power_totalE Z hZ ell hsum]
  unfold sourceLx sourceLy totalE rho0
  congr 1
  ring

lemma small_row_scale_bound_totalE {K : ℕ}
    (Z U delta : ℝ) (hZ : 1 ≤ Z) (hU : 1 ≤ U)
    (hUsmall : U ≤ Z ^ (1 / 100 : ℝ))
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1 / 2)
    (ell : Fin K → ℝ) (hsum : ∑i, ell i = totalE) (beta e : ℝ) :
    U ^ (8 / 5 + delta - (17 / 50 : ℝ)) *
      (∏i, (Z ^ (ell i)) ^ (17 / 50 : ℝ)) *
      ((Z ^ sourceLx) ^ (1 / 2 - (17 / 50 : ℝ)) *
        Z ^ (beta + 8 * e + (17 / 50 : ℝ) - 1) *
        (Z ^ sourceLy) ^ ((1 / 2 : ℝ) - 1)) ≤
      Z ^ (beta - 11 / 16 - 63 / 800 + 8 * e) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hrow : U ^ (8 / 5 + delta - (17 / 50 : ℝ)) ≤
      Z ^ (11 / 625 : ℝ) := by
    calc
      _ ≤ U ^ (44 / 25 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z ^ (1 / 100 : ℝ)) ^ (44 / 25 : ℝ) :=
        Real.rpow_le_rpow (zero_le_one.trans hU) hUsmall (by norm_num)
      _ = Z ^ (11 / 625 : ℝ) := by
        rw [← Real.rpow_mul hZ0.le]
        norm_num
  rw [mul_assoc, small_source_scale_totalE Z hZ0 ell hsum beta e]
  calc
    _ ≤ Z ^ (11 / 625 : ℝ) *
        Z ^ (beta - 11 / 16 - 79 / 800 + 8 * e + 51 * rho0 / 100) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = Z ^ ((11 / 625 : ℝ) +
        (beta - 11 / 16 - 79 / 800 + 8 * e + 51 * rho0 / 100)) := by
      rw [← Real.rpow_add hZ0]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le hZ
      norm_num [rho0] <;> linarith

lemma large_source_scale_totalE {K : ℕ}
    (Z : ℝ) (hZ : 0 < Z) (ell : Fin K → ℝ)
    (hsum : ∑i, ell i = totalE) (r : ℝ) :
    (∏i, (Z ^ (ell i)) ^ r) *
      ((Z ^ sourceLx) ^ (1 / 2 - r) * Z ^ (2 + r - 1) *
        (Z ^ sourceLy) ^ ((2 : ℝ) - 1)) =
      Z ^ ((53 / 32 : ℝ) + (13 / 16 : ℝ) * r +
        rho0 * (3 * r / 2 - 3 / 4)) := by
  rw [physical_scale_power_totalE Z hZ ell hsum]
  unfold sourceLx sourceLy totalE rho0
  congr 1
  ring

/-- Fixed rho surcharge in the large-tail geometric exponent. -/
def largeRhoCost (delta : ℝ) : ℝ := rho0 * (33 / 20 + 3 * delta / 2)

lemma largeRhoCost_nonneg {delta : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ largeRhoCost delta := by
  unfold largeRhoCost rho0
  positivity

lemma large_geometric_exponent_totalE (delta zeta r : ℝ) :
    (53 / 32 : ℝ) + (13 / 16 : ℝ) * r +
        rho0 * (3 * r / 2 - 3 / 4) +
      (physicalHeight + zeta) * (8 / 5 + delta - r) =
    (53 / 32 : ℝ) + ((13 / 16 : ℝ) + zeta) *
        (8 / 5 + delta) - zeta * r + largeRhoCost delta := by
  unfold physicalHeight largeRhoCost
  ring

/-! ## Exact canonical output and the first failed old premise -/

/--
Canonical-minus-central output on the exact shifted probe.  This is the
non-Euler interface still to be produced from `FirstSelectedTupleInput` and
the remaining finite/large-tail adaptations.
-/
def SameDataCanonicalPhysicalAt
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (theta : ℝ) : Prop :=
  letI : NeZero (∏P∈F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∃n : ℕ, 0 < n ∧ ∀eta : Character, ∃C : ℝ, 0 < C ∧
    ∀ᶠZ : ℝ in atTop,
      let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
      let T : Fin D.N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
      let hT := canonicalPoolOutside (M := F.modulus) (⊤) F.S D.N 1 2 Y
      let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
      normer ≠ 0 ∧ ∃idx grid : FreeRow → ℕ,
      (∀u, 1 ≤ idx u ∧ idx u ≤ n ∧
        grid u ≤ ⌊(49 / 100 : ℝ) / D.e⌋₊ ∧
        ((3 * idx u + 1 : ℕ) : ℝ) * Z ^ theta + Z ^ theta / 2 ≤
          (3 * idx u + 2 : ℕ) * Z ^ theta) ∧
      (∀u, let alpha : ℝ := 51 / 100 + D.e * grid u
        (51 / 100 : ℝ) ≤ alpha ∧ alpha ≤ 1 ∧
        alpha ≤ detectorMaximum
          (sourceDetectorFamily F.S F.exclusions.prime eta u
            (rayCubeFamily F.modulus ⊤ le_top u))
          (3 * idx u * Z ^ theta) ∧
        detectorMaximum
          (sourceDetectorFamily F.S F.exclusions.prime eta u
            (rayCubeFamily F.modulus ⊤ le_top u))
          (3 * idx u * Z ^ theta) < alpha + D.e ∧
        detectorMaximum
          (sourceDetectorFamily F.S F.exclusions.prime eta u
            (rayCubeFamily F.modulus ⊤ le_top u))
          (3 * (idx u + 1 : ℕ) * Z ^ theta) < alpha + 2 * D.e ∧
        ((51 / 100 : ℝ) < alpha → ∃j s,
          LFunction
            (sourceDetectorFamily F.S F.exclusions.prime eta u
              (rayCubeFamily F.modulus ⊤ le_top u) j) s = 0 ∧
          ¬((sourceDetectorFamily F.S F.exclusions.prime eta u
              (rayCubeFamily F.modulus ⊤ le_top u) j).residue = 1 ∧ s = 1) ∧
          alpha ≤ s.re ∧ s.re < alpha + D.e ∧
          |s.im| ≤ 3 * idx u * Z ^ theta)) ∧
      (∀u∈rowBand (Z ^ (1 / 100 : ℝ)) (Z ^ (physicalHeight + D.t)),
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 →
        (∀chi, (rayCubeFamily F.modulus ⊤ le_top u chi).residue ≠ 1) ∧
        (∀chi, (rayCubeFamily F.modulus ⊤ le_top u chi).modulus.absNorm ≤
          conductorConstant * F.modulus.absNorm *
            (Ideal.span {u.val} : Ideal O).absNorm) ∧
        ∀hnp : ∀chi, (rayCubeFamily F.modulus ⊤ le_top u chi).residue ≠ 1,
          HeckeDetectorZeros.zeroMaximum (rayCubeFamily F.modulus ⊤ le_top u) hnp
            (3 * (idx u + 1 : ℕ) * Z ^ theta) <
              51 / 100 + D.e * grid u + 2 * D.e) ∧
      let rows := rowBand (Z ^ (1 / 100 : ℝ)) (Z ^ (physicalHeight + D.t))
      let alpha : FreeRow → ℝ := fun u => 51 / 100 + D.e * grid u
      let height : FreeRow → ℝ := fun u => (3 * idx u + 1 : ℕ) * Z ^ theta
      ‖HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
          F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W
          totalE sourceLx sourceLy eta Z -
        principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
          F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z / normer -
        finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T hT
          (fun _ y => (F.w y : ℂ)) Y F.W F.W
          (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer‖ ≤
        C * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)

/-- A concrete admissible point below `7/8` for which the old small-tail premise fails. -/
def oldSmallTailBetaCounter : ℝ := 7 / 8 - rho0 / 8

def oldSmallTailECounter : ℝ := rho0 / 128

theorem old_small_tail_premise_counterexample :
    boundary < oldSmallTailBetaCounter ∧
      0 < oldSmallTailECounter ∧ oldSmallTailECounter < 1 / 1000 ∧
      oldSmallTailBetaCounter + 8 * oldSmallTailECounter < 7 / 8 := by
  norm_num [boundary, rho0, oldSmallTailBetaCounter, oldSmallTailECounter]

end SevenEighths.PerturbedCanonicalFrontier

end

end OAI
