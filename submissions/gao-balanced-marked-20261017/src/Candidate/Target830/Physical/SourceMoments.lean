/- Adapted from OpenAI, Hailey Collet, DaysSky and accepted PR60. Apache-2.0.
Private .874836 assembly; the new affine analytic input remains explicit. -/
import Candidate.Target830.Physical.InverseFields
import Candidate.Target830.Physical.SourceCountInitial
import Candidate.Target830.Physical.AffineFamily
/- Copyright (c) 2026. Released under Apache 2.0. -/
import Candidate.Cycle25.Energy.Endpoint
import Candidate.Cycle25.Assembly.Count.PlainInput
import Candidate.Cycle25.Assembly.Mesh
import Candidate.Cycle25.Assembly.Count.ActualMoments
import Candidate.Affine.SourceCount
import Candidate.Affine.Mesh

/-! Source moments at the region-aware cutoff. The original MI/MP fields are
re-used verbatim (they hold for every cutoff); the affine marked plain moment
is an explicit input, proved in `Candidate.Affine.Supply`. -/

namespace OAI.SevenEighths.Target830.Physical.SourceMoments
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local instance : Fintype Count.Plane :=
  ⟨{.PR62,.PR60,.A,.C,.oldWeak},by intro P; cases P <;> simp⟩
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentEnergyBands ProbeHighRowFamily
open Cycle25ProbeFinalAssembly ProbeFinalAssembly Cycle25ProbeFinalAssemblyCertifiedBands CenteredMomentEnergyCappedWidthInduction
open Cycle25ProbeDetectorPlainMarkedFineField Cycle25ProbeDetectorPlainUnmarkedField
open CenteredMomentNaturalFixedRaySource Cycle25CenteredMomentNaturalFixedRaySource
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbePhysical

/-- `weighted_SourceMomentBound` at the region-aware cutoff with the affine field. -/
def weighted_SourceMomentBoundA {D : Cycle25.Weighted.MomentData} (F : WeightedSourceData D)
    (κplain : ℝ) (counts : Target830.Physical.DetectorCount.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100<a → a ≤ 7/8 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im| ≤ height →
    Target830.Physical.SourceCount.SourceMomentsAtA F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
      (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z κplain counts.c counts.k C height D.t

theorem weighted_source_moments_A {D:Cycle25.Weighted.MomentData}(F:WeightedSourceData D)
    (κplain:ℝ)(hk1:κplain≤3/4)(counts:Target830.Physical.DetectorCount.CountParameters F.modulus ⊤ D.t)(fineMesh:ℝ)(hmesh:(0:ℝ)<fineMesh)
    (hfine:∀j,D.ell j ≤ fineMesh/200)
    (hpositive:weighted_PositiveFineSourceInput F κplain fineMesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (weighted_sourceFixedIdeal F) η₀) (1/4) (9/4) weighted_radialSupportUpper
        0 1 2 (D.t/4) U degree control A)
    (haffine:∀P : Count.Plane, InitialTransport.weighted_AffineFineInputAt P F):
    ∀η:Character,∃J:ℝ,0 ≤ J ∧ ∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ ≤ 1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBoundA F κplain counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=Target830.Physical.InverseFields.weighted_source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=weighted_source_batch_plain_marked_fine F κplain fineMesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=Cycle25ProbeDetectorPlainUnmarkedRestrictedField.weighted_source_batch_plain_unmarked D F hzero
  intro η
  choose Ja Ca hCa ha using (fun P : Count.Plane => haffine P η)
  let JaSum : ℕ := ∑P,Ja P
  let CaSum : ℝ := 1+∑P,Ca P
  have hCaSum : 0<CaSum := by
    have hh := Finset.sum_nonneg (fun P (_:P∈Finset.univ)=>(hCa P).le)
    dsimp [CaSum]; linarith
  have hCaLe (P : Count.Plane) : Ca P≤CaSum := by
    have hh := Finset.single_le_sum (fun P (_:P∈Finset.univ)=>(hCa P).le) (Finset.mem_univ P)
    dsimp [CaSum]; linarith
  have hJaLe (P : Count.Plane) : Ja P≤JaSum := Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ P)
  refine ⟨(Ji+Jm+Ju+JaSum:ℕ),by positivity,?_⟩
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu+CaSum,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu,Filter.eventually_all.mpr ha] with Z hi hm hu ha
  have hZ:0<Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0 ≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1 ≤ 1+height:=by linarith
  have hCi':Ci*(1+height)^Ji ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCa' (P : Count.Plane) : Ca P*(1+height)^(Ja P) ≤ (Ci+Cm+Cu+CaSum)*(1+height)^(Ji+Jm+Ju+JaSum):=by
    apply mul_le_mul (by linarith [hCaLe P]) (pow_le_pow_right₀ hbase (by have := hJaLe P; omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha' hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ) ≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im| ≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0 ≤ Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · apply Cycle25DetectorRawFiber.Moments.of_fields (B.fiber bin label left right hne) hk1
    · constructor
      · intro n hn σ hσ t ht
        exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
          rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
      · intro selected hselected hfirst hsecond n hn σ hσ t ht
        exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
          (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
      · intro j k hjk σ hσ t ht
        exact (hunmarked j k hjk σ hσ t ht).1.trans
          (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))
    · intro selected hselected hcap j k hjk σ hσ t ht
      exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
        (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro P hmlo hmhi selected hsel h1 h2 h3 j k hjk σ hσ t ht
    have haff := (ha P).2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
      (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight hmlo hmhi
    exact (haff selected hsel h1 h2 h3 j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right (hCa' P) (Real.rpow_nonneg hU _))

end
end OAI.SevenEighths.Target830.Physical.SourceMoments

#print axioms OAI.SevenEighths.Target830.Physical.SourceMoments.weighted_source_moments_A

namespace OAI.SevenEighths.Target830.Physical.SourceMoments
noncomputable section
set_option autoImplicit false
open scoped Classical
open Filter HeckeFamily Cycle25ProbeFinalAssembly
open Cycle25ProbeDetectorPlainMarkedFineField

theorem weighted_actual_source_moments_A {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) (κplain : ℝ)
    (hk : 7/10≤κplain) (hk1 : κplain≤3/4)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1≤κplain)
    (counts : DetectorCount.CountParameters F.modulus ⊤ D.t)
    (hfine : ∀j,D.ell j≤Cycle25.sourceMesh D.t/200)
    (haffine : ∀P : Count.Plane,InitialTransport.weighted_AffineFineInputAt P F) :
    ∀η:Character,∃J:ℝ,0≤J ∧ ∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        weighted_SourceMomentBoundA F κplain counts η Z τ
          (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  exact weighted_source_moments_A F κplain hk1
    counts (Cycle25.sourceMesh D.t) (Cycle25.sourceMesh_pos D.t_pos) hfine
    (terminal_plain_input F κplain hk hk1 hbeta hκbeta)
    (terminal_zero_input F κplain hk hk1 hbeta hκbeta) haffine
end
end OAI.SevenEighths.Target830.Physical.SourceMoments
#print axioms OAI.SevenEighths.Target830.Physical.SourceMoments.weighted_actual_source_moments_A
