import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Final.Parameters
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Numerator.Source.Collect
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Transport.HighApproximation
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Numerator.Scalar.SourcePacket
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Count.Public
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle25.Assembly.Count.MaskedCount
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Assembly.Low.Normalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
noncomputable section
set_option maxHeartbeats 2200000
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Arithmetic.Bernstein Cycle63.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle25DetectorRowCount HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open HeckePrimeAmplitudeBins ProbeMellinBoundary
instance source_fixed_product_neZero (D : BaselineData) (F : BaselineSourceData D) : NeZero (∏P∈F.S,P) :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

 theorem source_prime_bins (D : BaselineData) (F : BaselineSourceData D) (P : FinalAssembly.TransportParameters D)
    (τ : ℝ) (n : ℕ) (hτ : 0 < τ) (hheight : 4*τ < (1/200:ℝ)*D.cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 →
      ∀(η : Character) (u : FreeRow),Z^(1/100:ℝ) ≤ rowNorm u →
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 → rowNorm u ≤ Z^(d-D.t) →
      ∀(a : ℝ) (i : ℕ),i ≤ n → (51/100:ℝ) ≤ a → a ≤ 1 →
      detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
        (rayCubeFamily F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ) < a+2*D.e →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ (3*i+1:ℕ)*Z^τ → ∀j : Fin D.N,
      let Q := HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.length j)) z
      let g := amplitude (Z^(D.length j)) (a-1/2) D.t Q
      0 ≤ g ∧ g ≤ a-1/2 ∧ g∈labels (a-1/2) D.t ∧
      ‖Q‖ ≤ (Z^(D.length j))^(g+D.t) ∧
      (0 < g → (Z^d)^(2*(D.length j/d)*g) ≤ ‖Q‖^2) := by
  have hp := actual_phase_bins_on_cube F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad F.maximal F.W 1 2 (by norm_num) (by norm_num)
    (WeightedQRH.Numerator.source_complex_support_open F) (F.W.smooth ⊤)
    D.t (1/200) (7/8) P.rmin τ P.phaseEpsilon D.e P.phaseKappa D.cost D.t (1/100) D.t n
    D.t_pos.le (by norm_num) (by norm_num) P.rmin_pos hτ P.phaseEpsilon_pos D.e_pos D.e_small
    P.phaseKappa_pos D.cost_pos.le D.t_pos (by norm_num) P.phase_budget (lt_of_lt_of_le P.phase_gap (mul_le_mul_of_nonneg_left P.mesh_small P.rmin_pos.le))
    D.t_pos (by linarith)
  filter_upwards [hp,HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) 2 (by norm_num),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z hp hscale hT hZ
  intro d hd hd' η u hulo hcal huhi a i hi ha ha' hbin z hz hzim j
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hdpos : 0 < d := by linarith
  have hrlo : P.rmin ≤ D.length j/d := by
    apply (le_div_iff₀ hdpos).mpr
    have hh := (P.slots_lower j)
    nlinarith only [hh,hd',P.rmin_pos]
  have hrhi : D.length j/d ≤ D.t := by
    apply (div_le_iff₀ hdpos).mpr
    have hh := (D.slots_small j)
    nlinarith only [hh,hd,D.t_pos]
  have hH : 0 ≤ ((3*i+1:ℕ):ℝ)*Z^τ := by positivity
  have hhh : ((|((0,z.im),0).1.1| ≤ (3*i+1:ℕ)*Z^τ ∧
      |((0,z.im),0).2| ≤ (3*i+1:ℕ)*Z^τ) ∧
      |((0,z.im),0).1.2| ≤ (3*i+1:ℕ)*Z^τ) := by
    simpa only [abs_zero] using And.intro (And.intro hH hH) hzim
  have hh := hp d hd hd' (hscale d hd) hT η u hulo hcal huhi a i hi ha ha' hbin
    (D.length j/d) ((0,z.im),0) hrlo hrhi hhh
  have he : (Z^d)^(D.length j/d)=Z^(D.length j) := by
    rw [←Real.rpow_mul hZpos.le,mul_div_cancel₀ _ hdpos.ne']
  have hz' : (17/50:ℂ)+z.im*Complex.I=z := by
    apply Complex.ext <;> simp [hz]
  dsimp only at hh ⊢
  rw [he,hz'] at hh
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩

theorem source_scalar_on_rows (D : BaselineData) (F : BaselineSourceData D) (eps : ℝ) (heps : 0<eps) :
    ∃Cs : ℝ,0 < Cs ∧ ∀(η : Character) (rows : Finset FreeRow) (Z τ d a : ℝ) (i : ℕ),
      0 < Z → 2 < Z^τ → (51/100:ℝ) ≤ a → a ≤ 7/8 →
      (∀u∈rows,Z^(d-2*D.t) ≤ rowNorm u) →
      (∀u∈rows,rowNorm u ≤ Z^d) →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      ∀q∈WeightedQRH.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),∀u∈rows,
        ‖frequencyWeight ((17/50:ℂ)+q.2*Complex.I) ⟨u.val,u.property.1⟩*
          WeightedQRH.Numerator.numeratorFreeRowScalar F.S F.exclusions F.maximal η u
            ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖ ≤
          Cs*(η.modulus.absNorm:ℝ)^(2*eps)*(3+((3*i+1:ℕ):ℝ)*Z^τ)^(2*eps)*
            (Z^d)^(2*eps)*(Z^d)^(-(17/50:ℝ))*Z^((17/25)*D.t) := by
  obtain ⟨Cs,hCs,hbound⟩ := WeightedQRH.Numerator.source_frequency_scalar_bound
    D.e eps D.e_pos D.e_small heps F.S F.exclusions F.maximal
  refine ⟨Cs,hCs,?_⟩
  intro η rows Z τ d a i hZ hB ha ha' hfreq hupper hnext q hq u hu
  have hH : ((3*i+1:ℕ):ℝ)*Z^τ ≤ ((3*i+2:ℕ):ℝ)*Z^τ := by
    push_cast
    have hp : 0 ≤ Z^τ := Real.rpow_nonneg hZ.le _
    nlinarith
  exact hbound η u (rayCubeFamily F.modulus ⊤ le_top u)
    (Z^τ) a (((3*i+1:ℕ):ℝ)*Z^τ) i hB ha (by linarith) hH (hnext u hu)
    ((((a+16*D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)
    (by simp) (by norm_num) (by simpa using hq.1)
    Z d D.t (Z^d) hZ rfl (hfreq u hu) (hupper u hu)

theorem source_normalizer_bound (D : BaselineData) (F : BaselineSourceData D) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      Cycle63HighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z≠0 ∧
      ‖(Cycle63HighTransport.actualNormalizer F.modulus ⊤ F.S D.length 1 2 (fun _=>F.w) F.W F.W Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact Cycle63LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.length (fun j=>(D.slots_pos j)) D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)

theorem source_pools_nonempty (D : BaselineData) (F : BaselineSourceData D) :
    ∀ᶠZ:ℝ in atTop,∀j:Fin D.N,(WeightedQRH.Numerator.sourcePrimePool F Z j).Nonempty := by
  obtain ⟨C,hC,hbound⟩ := source_normalizer_bound D F
  filter_upwards [hbound] with Z hn
  intro j
  by_contra hne
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
  have hmass : PrincipalSignalComparison.slotMass (WeightedQRH.Numerator.sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) (fun j=>Z^(D.length j))) j=0 := by
    simp only [PrincipalSignalComparison.slotMass,hempty,Finset.sum_empty]
  have hprod : (∏i:Fin D.N,PrincipalSignalComparison.slotMass (WeightedQRH.Numerator.sourcePrimePool F Z)
      (ProbePrincipalResidueActual.residueWeights (fun _=>F.w) (fun j=>Z^(D.length j))) i)=0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) hmass
  apply hn.1
  unfold Cycle63HighTransport.actualNormalizer Probe.principalScalar
  exact mul_eq_zero_of_right _ (Complex.ofReal_eq_zero.mpr (mul_eq_zero_of_right _ hprod))

theorem plainOld_p_anti {κ δ x y m : ℝ} (hk : 0 < κ) (hδ : 0 ≤ δ) (hm : m ≤ 1/2) (hxy : x ≤ y) :
    Cycle63.CountAffine.plainOld κ δ y m ≤ Cycle63.CountAffine.plainOld κ δ x m := by
  unfold Cycle63.CountAffine.plainOld
  have h1 : 0 ≤ 1-2*m := by linarith
  have hk6 : 0 < 6*κ := by linarith
  have h2 : 2*(δ*x)*(1-2*m)/(6*κ) ≤ 2*(δ*y)*(1-2*m)/(6*κ) := by
    apply div_le_div_of_nonneg_right _ hk6.le
    have := mul_le_mul_of_nonneg_left hxy hδ
    nlinarith
  linarith

/-- The combined count is nonincreasing in the prime amplitude. -/
theorem countingR_antitone {κ δ x y : ℝ} (hk : 7/10 ≤ κ) (hk1 : κ ≤ 3/4)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 3/4) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1/2) :
    countingR κ δ y ≤ countingR κ δ x := by
  have hold : countingROld κ δ y ≤ countingROld κ δ x := by
    rw [← Cycle63.Assembly.Count.rowCount_eq hk, ← Cycle63.Assembly.Count.rowCount_eq hk]
    exact rowCount_antitone hδ hδ1 hk hk1 hx hxy hy
  unfold countingR
  by_cases hrx : Cycle63.CountAffine.inRegion δ x
  · have hry := Cycle63.CountAffine.inRegion_up hrx hxy hy
    rw [ite_eq_left hrx, ite_eq_left hry]
    have hnb : Cycle63.CountAffine.newBranch κ δ y ≤ Cycle63.CountAffine.newBranch κ δ x := by
      unfold Cycle63.CountAffine.newBranch
      exact max_le_max (max_le_max (Cycle63.CountAffine.RStar_anti hrx hxy hy)
          (Cycle63.CountAffine.RStarC_anti hrx hxy hy))
        (plainOld_p_anti (by linarith) hδ (by norm_num [Cycle63.CountAffine.plainTop]) hxy)
    exact min_le_min hold hnb
  · rw [ite_eq_right hrx]
    split_ifs with hry
    · exact (min_le_left _ _).trans hold
    · exact hold

/-- A card bound in the full physical bins remains true at the diluted main-slot mean. -/
theorem masked_class_count_combined {N : ℕ} {Row : Type*}
    (rows : Finset Row) (main : Finset (Fin N)) (U δ κ mesh : ℝ) (hm : 0 < mesh)
    (width : Fin N→ℝ) (Q : Row→Fin N→ℂ)
    (bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) (δ/2) mesh)
    (hδ : 0 < δ) (hδtop : δ ≤ 3/4) (hk : 7/10≤κ) (hk1 : κ≤3/4) (hU : 1 ≤ U)
    (hw : ∀j∈(Finset.univ : Finset (Fin N)),0 ≤ width j) (hL : 0 < ∑j∈(Finset.univ : Finset (Fin N)),width j)
    (C loss : ℝ) (hC : 0 ≤ C)
    (hne : (HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ U (δ/2) mesh hm width Q bin).Nonempty)
    (hcard : ((HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ U (δ/2) mesh hm width Q bin).card:ℝ) ≤
      C*U^(countingR κ δ (HeckeDetectorAmplitudeFirst.classMean Finset.univ (δ/2) mesh width bin/δ)+loss)) :
    let g := HeckeDetectorFiberPartition.binValue Finset.univ (δ/2) mesh bin
    let q := weightedMean Finset.univ width (WeightedQRH.maskedGain main g)
    0 ≤ q ∧ q ≤ δ/2 ∧
      ((HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ U (δ/2) mesh hm width Q bin).card:ℝ) ≤
        C*U^(countingR κ δ (q/δ)+loss) := by
  dsimp only
  have hg : ∀j∈(Finset.univ : Finset (Fin N)),0 ≤ HeckeDetectorFiberPartition.binValue Finset.univ (δ/2) mesh bin j ∧
      HeckeDetectorFiberPartition.binValue Finset.univ (δ/2) mesh bin j ≤ δ/2 := by
    obtain ⟨u,hu⟩ := hne
    intro j hj
    rw [←WeightedQRH.amplitude_class_value rows Finset.univ U (δ/2) mesh hm width Q bin u hu j hj]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq0,hq,hqtop⟩ := WeightedQRH.maskedMean_bounds Finset.univ main width
    (HeckeDetectorFiberPartition.binValue Finset.univ (δ/2) mesh bin) δ hw hL hg
  refine ⟨hq0,hq.trans hqtop,?_⟩
  have hfull : HeckeDetectorAmplitudeFirst.classMean Finset.univ (δ/2) mesh width bin =
      weightedMean Finset.univ width (HeckeDetectorFiberPartition.binValue Finset.univ (δ/2) mesh bin) := rfl
  rw [hfull] at hcard
  apply hcard.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_le hU
  apply add_le_add _ le_rfl
  apply countingR_antitone hk hk1 hδ.le hδtop
  · exact div_nonneg hq0 hδ.le
  · exact div_le_div_of_nonneg_right hq hδ.le
  · apply (div_le_iff₀ hδ).mpr
    linarith

theorem source_masked_count_with_error (D : Data) (F : SourceData)
    (counts : Cycle25ProbeHighRowFamily.CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
    (hτ : 0 < τ) (hτzero : τ < (1/200:ℝ)/2)
    (hτheight : 4*τ < (1/200:ℝ)*D.cost) (hτ2 : 2*τ ≤ D.t) (herror : 159*D.ε+609*D.t≤σ) :
    ∃C : ℝ,1 ≤ C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d a C0 : ℝ,(1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 7/8 → 1 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
      ∀i : ℕ,i ≤ n →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*Z^τ) < a+2*D.e) →
      (∀u∈rows,a ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        ((3*i:ℕ)*Z^τ)) →
      ∀z : ℂ,z.re=17/50 → |z.im| ≤ Z^(2*τ) →
      SourceMomentBound D F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      let Q := canonicalFamily D F Z z
      ∀main : Finset (Fin D.N),
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
      let q := weightedMean Finset.univ (fun j=>D.length j/d) (WeightedQRH.maskedGain main (binValue Finset.univ ((2*a-1)/2) D.t bin))
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*
          (Z^d)^(Cycle63.Arithmetic.Bernstein.countingR D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨K,hK,hcount⟩ := canonical_source_count_with_error D F counts τ σ n hτ hτzero hτheight hτ2 herror
  refine ⟨K,hK,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro main bin hne
  have hdpos : 0<d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  have hcard := (hb bin hne).2.2
  exact masked_class_count_combined rows main
    (Z^d) (2*a-1) D.momentKappa D.t D.t_pos (fun j=>D.length j/d)
    (canonicalFamily D F Z z) bin (by linarith) (by linarith) D.momentKappa_lo D.momentKappa_hi
    (Real.one_le_rpow hZ.le hdpos.le) (fun j _=>(div_pos (D.slots_pos j) hdpos).le)
    (by rw [←Finset.sum_div,D.slots_sum];exact div_pos Cycle63.Assembly.Count.ell_pos hdpos)
    (K*C0) σ (by positivity) hne hcard

end Cycle63.Numerator.Source

end
end Record1252270103Bootstrap.PR67
