/- Repeated marks: fork of Collet's generic return module PhysicalDirect.PublicCount (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Original retained full-class and error-mask count transport, adapted Gao/Hailey Collet/OpenAI; Apache-2.0. -/
import Submissions.arvi_repeated_marks_20261024.ReturnD.Schedule
import Submissions.arvi_repeated_marks_20261024.ReturnD.PhysicalDirect.CanonicalCount
import Submissions.hailey_collet_1252270103.Cycle61.Assembly.Count.Errors
noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open QRH.Record1252270103Return

namespace QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
open QRH.Record1252270103Return QRH.Record1252270103Return.GenericPhysical
variable [Geometry.Parameters] [Geometry.BoundsR] [scheme : CountScheme] [GenericArithmetic.PhysicalSchedule]
open OAI OAI.SevenEighths QRH.Record12518109Count
open QRH.Record1252270103Return.GenericPhysical (SourceData)
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeHighRowFamily
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
theorem canonical_source_count_with_error (D : BaselineData) (F : SourceData) 
    (counts : CountParameters F.modulus ⊤ D.t) (τ σ : ℝ) (n : ℕ)
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
      ∀bin : BinLabel (Finset.univ : Finset (Fin D.N)) ((2*a-1)/2) D.t,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) D.t D.t_pos (fun j=>D.length j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) D.t (fun j=>D.length j/d) bin
      rows'.Nonempty → 0 ≤ q ∧ q ≤ (2*a-1)/2 ∧
        (rows'.card:ℝ) ≤ C*C0*
          (Z^d)^(QRH.Record1252270103Return.GenericCount.envelope D.momentKappa (2*a-1) (q/(2*a-1))+σ) := by
  obtain ⟨C,hC,hcount⟩ := physical_source_amplitude_count D F counts τ n hτ hτzero hτheight hτ2
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hcount η,eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only
  intro bin hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hdp : 0<d := by linarith
  have hb := hc d a C0 hd hd' ha ha' hC0 rows hrows i hi hnext hcurrent z hz hzim hmom
  dsimp only at hb
  rw [physical_eq_canonical D F Z d hZp hdp.ne'] at hb
  have hbound := hb bin hne
  refine ⟨hbound.1,hbound.2.1,?_⟩
  apply hbound.2.2.trans
  apply Cycle61DetectorCount.source_error_absorption Z d D.t D.ε _ σ (C*C0) hZ.le hd D.t_pos.le
  · exact mul_nonneg (by linarith) (by linarith)
  · exact herror

end QRH.RepeatedMarks.Return.GenericPhysical.PhysicalDirect
end

