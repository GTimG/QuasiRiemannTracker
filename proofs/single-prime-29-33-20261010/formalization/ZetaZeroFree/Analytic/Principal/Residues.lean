import ZetaZeroFree.Analytic.Principal.Signal
import OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds
import OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical

namespace ZetaZeroFree.Analytic.Principal

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open ProbeEuler ProbePhysical CompletedGauss ProbeFiniteProductBounds ProbeRaySlots HeckeSignal

lemma normalized_source_double_residue {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0<Z) (s : ℂ) (H B : ℂ→ℂ→ℂ)
    (S : Finset κ) (T : κ→Finset ι) (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hc : sourceResidueConstant W0 W1 M≠0)
    (hB : B 1 (1/6)=slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M^2/6*
      sourceMultiplier W0 W1 (Z^(13/33:ℝ)) Y Z χ s H B 1 (1/6)) /
      (sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z (5/33) (slotMass T w):ℂ))=
      (Z:ℂ)^(s-67/99)*Complex.exp ((s-5/6)^2)*H 1 (1/6)/LFunction χ s*
        slotRatio S T w Q A η s := by
  rw [source_double_residue,source_normalizer_cast S T w hZ,hB,source_power_identity hZ s]
  have hz : (Z:ℂ)^(((-(5/33:ℝ)/6:ℝ):ℂ))≠0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  simp only [slotRatio,div_eq_mul_inv,mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M*(sourceResidueConstant W0 W1 M)⁻¹)*
      ((Z:ℂ)^(((-(5/33:ℝ)/6:ℝ):ℂ))*((Z:ℂ)^(((-(5/33:ℝ)/6:ℝ):ℂ)))⁻¹)*
      ((Z:ℂ)^(s-67/99)*Complex.exp ((s-5/6)^2)*H 1 (1/6)*
      (LFunction χ s)⁻¹*(slotProduct S T w Q A η s*
      (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc,mul_inv_cancel₀ hz]; ring_nf

lemma normalized_residue_integral {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal HeckeFamily.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0<Z)
    (H B : ℂ→ℂ→ℂ→ℂ) (S : Finset κ) (T : κ→Finset ι)
    (w Q : κ→ι→ℝ) (A η : κ→ι→ℂ)
    (hc : sourceResidueConstant W0 W1 M≠0)
    (hB : ∀t : ℝ,B ((a:ℂ)+t*I) 1 (1/6)=slotProduct S T w Q A η ((a:ℂ)+t*I)) :
    sourceResidueIntegral W0 W1 M χ a (Z^(13/33:ℝ)) Y Z H B /
      (sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z (5/33) (slotMass T w):ℂ))=
      (Z:ℂ)^((11/16:ℂ)-67/99)*slotResidue χ (fun s=>H s 1 (1/6)) a Z S T w Q A η := by
  unfold sourceResidueIntegral verticalIntegral slotResidue
  norm_num only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_one,Complex.ofReal_ofNat]
  rw [mul_div_assoc,←integral_div]
  conv_rhs => rw [mul_left_comm,←integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [normalized_source_double_residue W0 W1 M χ Y Z hZ _ (H _) (B _) S T w Q A η hc (hB t)]
  have hp : (Z:ℂ)^((11/16:ℂ)-67/99)*(Z:ℂ)^(((a:ℂ)+t*I)-11/16)=
      (Z:ℂ)^(((a:ℂ)+t*I)-67/99) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hZ.ne')]
    congr 1
    ring_nf
  rw [←hp]
  norm_num only [show (11/16:ℂ)-67/99=17/1584 by norm_num]
  ring_nf

/-- Actual double residue, with the new normalization and selected-prime error. -/
theorem actual_residue_estimate {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 7/8<a) (ha2 : a≤2) (hβ : HeckeZeroSupremum.beta<a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ,0≤D ∧ ∀(W0 W1 : SchwartzMap ℝ ℂ) (T : κ→Finset PrimeIdeal)
      (w : κ→PrimeIdeal→ℝ) (P Y Z : ℝ) (B : ℂ→ℂ→ℂ→ℂ),
      480≤P → 1440*P^(-(7/8:ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤w j p) → (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val:ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) → (∀j∈S,0<slotMass T w j) → 1≤Z →
      sourceResidueConstant W0 W1 (∏p∈E,p)≠0 →
      (∀t : ℝ,B ((a:ℂ)+t*I) 1 (1/6)=slotProduct S T w (fun _ p=>Ideal.absNorm p.val)
        (fun _ p=>actualAPhase η (primaryGenerator p.val)) (fun _ p=>idealCoeff η p.val) ((a:ℂ)+t*I)) →
      let N := sourceResidueConstant W0 W1 (∏p∈E,p)*
        (Probe.principalScalar S Z (5/33) (slotMass T w):ℂ)
      N≠0 ∧ ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
        a (Z^(13/33:ℝ)) Y Z (globalClosedCorrection η E) B/N-
        HeckeSignal.signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-67/99) Z‖≤
        D*Z^(a-67/99)*P^(-(7/8:ℝ)) := by
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := exists_actualSlotResidue_bound η E hE ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have hZ0 : 0<Z := by linarith
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ0 hmass),?_⟩
  rw [normalized_residue_integral W0 W1 _ _ a Y Z hZ0 _ B S T w _ _ _ hc hB,
    signal_scale _ _ hZ0,←mul_sub,norm_mul]
  have hb := hbound T w P Z hP hsmall hw hnorm hcop hmass hZ
  change ‖(Z:ℂ)^((11/16:ℂ)-67/99)‖*‖actualSlotResidue η E hE a Z S T w-
    HeckeSignal.signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖≤_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ0]
  norm_num only [show ((17/1584:ℂ).re:ℝ)=17/1584 by norm_num]
  rw [neg_div] at hb 
  calc
    _ ≤ Z^(17/1584:ℝ)*(D*Z^(a-11/16)*P^(-(7/8:ℝ))) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZ0.le _)
    _ = D*Z^(a-67/99)*P^(-(7/8:ℝ)) := by rw [show a-67/99=(17/1584:ℝ)+(a-11/16) by ring_nf,Real.rpow_add hZ0];ring_nf

lemma source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=5/33) (Z a ξ υ : ℝ) (hZ : 0<Z) :
    ProbePrincipalRemainderBounds.scalePower (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z a ξ υ*
      (∏j∈J,(Z^(ell j))^ξ)=
      Z^(a-67/99+(25/33)*(ξ-1/6)+(15/33)*(υ-1)) := by
  have hp : (∏j∈J,(Z^(ell j))^ξ)=Z^((5/33)*ξ) := by
    simp only [←Real.rpow_mul hZ.le]
    rw [←Real.rpow_sum_of_pos hZ,←Finset.sum_mul,hell]
  rw [hp,ProbePrincipalRemainderBounds.scalePower,←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring_nf

/-- Existing wider contours save y/20 and h/600; these replace the manuscript's narrower contours. -/
lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=5/33) (Z a e : ℝ) (hZ : 0<Z) :
    ProbePrincipalRemainderBounds.scalePower (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z a (1/6+e) (19/20)*
      (∏j∈J,(Z^(ell j))^(1/6+e))=Z^(a-67/99+(25/33)*e-1/44) := by
  rw [source_scale_identity J ell hell Z a (1/6+e) (19/20) hZ]
  congr 1
  ring_nf

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι→ℝ)
    (hell : ∑j∈J,ell j=5/33) (Z a : ℝ) (hZ : 0<Z) :
    ProbePrincipalRemainderBounds.scalePower (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z a (33/200) 1*
      (∏j∈J,(Z^(ell j))^(33/200:ℝ))=Z^(a-67/99-1/792) := by
  rw [source_scale_identity J ell hell Z a (33/200) 1 hZ]
  congr 1
  ring_nf

theorem source_remainders_power_bound {ι : Type*}
    (η : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (a e : ℝ) (ha : a∈Set.Icc (7/8:ℝ) 2) (hβ : HeckeZeroSupremum.beta<a)
    (he : 0<e) (hehi : e≤5/6) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=5/33) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Set.Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,0<Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s=>verticalIntegral (1/6+e) (fun z=>verticalIntegral (19/20)
      (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(a-67/99+(25/33)*e-1/44)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s=>verticalIntegral (33/200)
      (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤C*Z^(a-67/99-1/792)) := by
  obtain ⟨C,hC,hbound⟩ := ProbePrincipalRemainderBounds.ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a e ha hβ he hehi
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound W hW hsupp (fun j=>Z^(ell j)) (fun _ _=>Real.rpow_pos_of_pos hZ _)
    hthreshold hmod T hT (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hZ
  dsimp only at hh
  rw [source_w_scale_identity J ell hell Z a e hZ,source_z_scale_identity J ell hell Z a hZ] at hh
  exact hh

lemma source_w_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-67/99+(25/33)*e-1/44≤β-67/99-1/4000 := by linarith

lemma source_z_strict_exponent (β e : ℝ) (he : e≤1/1000) :
    (β+e)-67/99-1/792≤β-67/99-1/4000 := by linarith

theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : HeckeZeroSupremum.beta+e∈Set.Icc (7/8:ℝ) 2) :
    ∃C : ℝ,0<C ∧ ∀(ell : ι→ℝ),(∑j∈J,ell j=5/33) → ∀(W : ι→ℝ→ℝ),
    (∀j∈J,∀x,0≤W j x ∧ W j x≤B) →
    (∀j∈J,Function.support (W j)⊆Set.Icc c d) → ∀T : ι→Finset PrimeIdeal,
    (∀j∈J,∀p∈T j,p.val∉S) → ∀Z : ℝ,1≤Z→
    (∀j∈J,480≤c*Z^(ell j)) → (∀j∈J,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    let K0 := fun s=>sourceMultiplier W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>verticalIntegral (1/6+e)
      (fun z=>verticalIntegral (19/20) (fun w=>K0 s w z*LFunction π (6*z)*LFunction π w)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-67/99-1/4000)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta+e)
      (fun s=>verticalIntegral (33/200) (fun z=>K0 s 1 z*LFunction π (6*z)))‖≤
      C*Z^(HeckeZeroSupremum.beta-67/99-1/4000)) := by
  obtain ⟨C,hC,hbound⟩ := source_remainders_power_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta+e) e ha (by linarith) he (by linarith)
  refine ⟨C,hC,?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hh := hbound ell hell W hW hsupp T hT Z (by linarith) hthreshold hmod
  dsimp only at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)


theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=5/33 → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤W j x ∧ W j x≤B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤Z → (∀j,480≤c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-67/99-1/4000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith
  have hb := hbound ell hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := ProbePrincipalPhysical.principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    simp only [mul_comm]
    ring_nf
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-67/99-1/4000)
  apply hn.trans
  have hCe : C≤C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤Z^(HeckeZeroSupremum.beta-67/99-1/4000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring_nf
  rw [htwo]
  nlinarith

theorem normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal HeckeFamily.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 7/8<a) (ha2 : a≤2) (hβ : HeckeZeroSupremum.beta<a) (S : Finset κ) :
    letI : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃D : ℝ, 0≤D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0<a0 → 0<a1 → Function.support W0⊆Set.Icc a0 b0 →
      Function.support W1⊆Set.Icc a1 b1 →
      (∀y,(W0 y).im=0) → (∀y,(W1 y).im=0) →
      (∀y,0≤(W0 y).re) → (∀y,0≤(W1 y).re) → W0≠0 → W1≠0 →
      ∀ (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480≤P → 1440*P^(-(7/8 : ℝ))≤1 →
      (∀j∈S,∀p∈T j,0≤W j ((Ideal.absNorm p.val : ℝ)/scale j)) →
      (∀j∈S,∀p∈T j,P≤(Ideal.absNorm p.val : ℝ)) →
      (∀j∈S,∀p∈T j,IsCoprime p.val η.modulus) →
      (∀j∈S,0<slotMass T (residueWeights W scale) j) → 1≤Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏p∈E,p) *
        (Probe.principalScalar S Z (5/33) (slotMass T (residueWeights W scale)) : ℂ)
      normer≠0 ∧
      ‖sourceResidueIntegral W0 W1 (∏p∈E,p) (η.excludePrimes E hE.prime)
          a (Z^(13/33 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-67/99) Z‖ ≤
        D*Z^(a-67/99)*P^(-(7/8 : ℝ)) := by
  dsimp only
  let : NeZero (∏p∈E,p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D,hD,hbound⟩ := actual_residue_estimate E hE η ha ha2 hβ S
  refine ⟨D,hD,?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏p∈E,p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _


lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤c) (hA : ‖A-R‖≤c) (hN : ‖N⁻¹‖≤v)
    (hR : ‖R/N-F‖≤d) : ‖A/N-F‖≤c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring_nf
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Ideal HeckeFamily.O) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=5/33)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (5/33)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-67/99) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-67/99-1/4000+nu)+
        Z^(HeckeZeroSupremum.beta-67/99+e-(7/8)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(7/8:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) ell (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (5/33)
    (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(ell j)) (c*Z^ellMin) (Z^(15/33:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2
  have hpw : (c*Z^ellMin)^(-(7/8:ℝ))=c^(-(7/8:ℝ))*Z^(-(7/8:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring_nf
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-67/99-1/4000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-67/99-1/4000+nu) := by
    rw [Real.rpow_add hZ0];ring_nf
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-67/99)*(c*Z^ellMin)^(-(7/8:ℝ))=
      (D*c^(-(7/8:ℝ)))*Z^(HeckeZeroSupremum.beta-67/99+e-(7/8)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-67/99+e-(7/8)*ellMin=
      (HeckeZeroSupremum.beta+e-67/99)+(-(7/8:ℝ)*ellMin) by ring_nf,Real.rpow_add hZ0]
    ring_nf
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤C := by
    dsimp [C]
    have : 0≤D*c^(-(7/8:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(7/8:ℝ))≤C := by
    dsimp [C]
    have : 0≤C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-67/99-1/4000+nu)+
        C*Z^(HeckeZeroSupremum.beta-67/99+e-(7/8)*ellMin) := by gcongr
    _ = _ := by ring_nf

theorem one_prime_principal_comparison
    (M : Ideal HeckeFamily.O) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset (Ideal HeckeFamily.O)) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W : ℝ→ℝ) (hW : ContDiff ℝ ∞ W)
    (hcompact : HasCompactSupport W)
    (hsupp : Function.support W⊆Set.Ioo c d)
    (hWbounds : ∀y,0≤W y ∧ W y≤B) (hne : W≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun (_ : Fin 1)=>pool (RayQuotient.identityClass M H) S c d (Z^(5/33:ℝ))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (5/33)
          (slotMass T (residueWeights (fun (_ : Fin 1)=>W) (fun _=>Z^(5/33:ℝ)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W ((Ideal.absNorm (P j).val.val:ℝ)/Z^(5/33:ℝ)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(13/33:ℝ)) (Z^(15/33:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-67/99) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-67/99-1/4000+nu)+
        Z^(HeckeZeroSupremum.beta-67/99+e-(7/8)*(5/33))) := by
  simpa using actual_ray_principal_comparison (K:=1) M H hH η S hS c d B (5/33) hc hd hB
    (by norm_num) (fun _=>(5/33:ℝ)) (fun _=>le_rfl) (fun _ _ _=>Subsingleton.elim _ _)
    (by simp) (fun _=>W) (fun _=>hW) (fun _=>hcompact) (fun _=>hsupp)
    (fun _=>hWbounds) (fun _=>hne) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    e nu he hehi hnu ha ha2

end
end ZetaZeroFree.Analytic.Principal
