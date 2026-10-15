import Submissions.argonaut_20261008.PrincipalRegionSlotBoundsV2
import Submissions.argonaut_20261008.PrincipalSameSCutoffsV2
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized

namespace OAI.SevenEighths.LocalPrincipalSharpWindowV2
noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter Set MeasureTheory Asymptotics
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open ProbeRaySlots ProbePrincipalPhysical ProbePrincipalNormalized
open PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open ProbeMellinBoundary ProbePrincipalContours
open LocalPrincipalGeometryV2 LocalPrincipalCutoffsV2
local notation "Id" => Ideal HeckeFamily.O

/- Correct Sigma tail and b0 slot constant, independent of the raw B0 finite-product module. NOT_RUN. -/
def slotConstantV2 {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3 / 2) * ∏ _j ∈ J,
    (1 + 1440 * (480 : ℝ) ^ (-analyticBoundaryB0)) * (128 * d * B * c ^ (ξ - 1))

theorem slot_norm_bound_sharp_v2 {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : analyticBoundaryB0≤ s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1+1440*Pmin^(-(analyticBoundaryB0 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  simp only [slotMultiplier,local_eq_regionSlot,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc,Complex.ofReal_natCast] using LocalPrincipalRegionSlotV2.weighted_region_slot_norm_v2 (T j) (b j)
    (fun P => (Ideal.absNorm P.val : ℝ)) (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
    (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem combined_slot_bound_sharp_v2 {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTailSigma S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀j∈J,∀P∈T j,0≤b j P)
    (hQ : ∀j∈J,∀P∈T j,Pmin≤(Ideal.absNorm P.val : ℝ))
    (hη : ∀j∈J,∀P∈T j,‖idealCoeff η P.val‖=1) (s w z : ℂ)
    (hs : analyticBoundaryB0≤ s.re) (hw : 19/20≤w.re) (hz : 33/200≤z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3/2) * ∏ j ∈ J, (1+1440*Pmin^(-(analyticBoundaryB0 : ℝ))) *
        ∑ P ∈ T j, b j P*(Ideal.absNorm P.val : ℝ)^(z.re-1) := by
  rw [norm_mul]
  exact mul_le_mul (LocalPrincipalCutoffsV2.global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (slot_norm_bound_sharp_v2 η J T b Pmin hPmin hb hQ hη s w z hs hw hz) (norm_nonneg _) (by norm_num)

lemma active_prime_sum_bound_v2 (T : Finset PrimeIdeal) (W : ℝ→ℝ)
    (c d B P ξ : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hP : 0<P)
    (hthreshold : 480≤c*P) (hξ : ξ≤1)
    (hW : ∀x,0≤W x ∧ W x≤B) (hsupp : Function.support W⊆Icc c d) :
    (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))
      ≤(128*d*B*c^(ξ-1))*P^ξ := by
  let A := T.filter (fun p=>W ((Ideal.absNorm p.val:ℝ)/P)≠0)
  have hA (p : PrimeIdeal) (hp : p∈A) :
      c*P≤(Ideal.absNorm p.val:ℝ) ∧ (Ideal.absNorm p.val:ℝ)≤d*P := by
    have h := hsupp (Finset.mem_filter.mp hp).2
    exact ⟨(le_div_iff₀ hP).mp h.1,(div_le_iff₀ hP).mp h.2⟩
  have he : (∑p∈T,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1))=
      ∑p∈A,W ((Ideal.absNorm p.val:ℝ)/P)*(Ideal.absNorm p.val:ℝ)^(ξ-1) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hw : W ((Ideal.absNorm p.val:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hp,hh⟩)
    simp [hw]
  have hcount : (A.card:ℝ)≤128*(d*P) := by
    have h := DescentFiberCost.finite_ideal_count_real (A.image Subtype.val) (d*P)
      (by nlinarith) (by
        intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact p.property.ne_zero)
      (by intro I hI; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI; exact (hA p hp).2)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h
  have hp (p : PrimeIdeal) (hp : p∈A) : (Ideal.absNorm p.val:ℝ)^(ξ-1)≤c^(ξ-1)*P^(ξ-1) := by
    rw [←Real.mul_rpow hc.le hP.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hP) (hA p hp).1 (by linarith)
  rw [he]
  calc
    _≤∑_p∈A,B*(c^(ξ-1)*P^(ξ-1)) := Finset.sum_le_sum (fun p hpA=>
      mul_le_mul (hW _).2 (hp p hpA) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB)
    _=(A.card:ℝ)*(B*(c^(ξ-1)*P^(ξ-1))) := by simp
    _≤(128*(d*P))*(B*(c^(ξ-1)*P^(ξ-1))) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _=(128*d*B*c^(ξ-1))*P^ξ := by
      have heP : P*P^(ξ-1)=P^ξ := by
        calc
          _=P^(1:ℝ)*P^(ξ-1) := by rw [Real.rpow_one]
          _=P^ξ := by rw [←Real.rpow_add hP];congr 1;ring
      calc
        _=(128*d*B*c^(ξ-1))*(P*P^(ξ-1)) := by ring
        _=_ := by rw [heP]

lemma slotConstantV2_nonneg_v2 {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) : 0≤ slotConstantV2 J c d B ξ := by
  have hd0 : 0≤d := hc.le.trans hd
  unfold slotConstantV2
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _=>by positivity)

theorem window_sharp_bound_v2 {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTailSigma S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hξ : ξ≤1)
    (W : ι→ℝ→ℝ) (hW : ∀j∈J,∀x,0≤W j x ∧ W j x≤B)
    (hsupp : ∀j∈J,Function.support (W j)⊆Icc c d)
    (P : ι→ℝ) (hP : ∀j∈J,0<P j)
    (hthreshold : ∀j∈J,480≤c*P j)
    (hmod : ∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*P j)
    (T : ι→Finset PrimeIdeal) (s w z : ℂ)
    (hs : analyticBoundaryB0≤ s.re) (hw : 19/20≤w.re) (hz : z.re=ξ) (hzlo : 33/200≤ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z‖≤
      slotConstantV2 J c d B ξ * ∏j∈J,(P j)^ξ := by
  let A (j : ι) := (T j).filter (fun p=>W j ((Ideal.absNorm p.val:ℝ)/P j)≠0)
  have hA (j : ι) (hj : j∈J) (p : PrimeIdeal) (hp : p∈A j) : c*P j≤(Ideal.absNorm p.val:ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x=>(W j x:ℂ)) P s w z =
      slotMultiplier η J A (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/P j):ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val:ℝ)/P j)=0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp,h⟩)
    simp [hh]
  rw [he]
  have h := combined_slot_bound_sharp_v2 η S hS J A
    (fun j p=>W j ((Ideal.absNorm p.val:ℝ)/P j)) 480 (by norm_num)
    (fun j hj p _=>(hW j hj _).1)
    (fun j hj p hp=>(hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp=>PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz];exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _≤(3/2)*∏j∈J,(1+1440*(480:ℝ)^(-(analyticBoundaryB0:ℝ)))*((128*d*B*c^(ξ-1))*(P j)^ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro j hj; apply mul_nonneg (by positivity);exact Finset.sum_nonneg (fun p _=>by
          exact mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (active_prime_sum_bound_v2 (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _=_ := by simp only [slotConstantV2,←mul_assoc,Finset.prod_mul_distrib]

end
end OAI.SevenEighths.LocalPrincipalSharpWindowV2
