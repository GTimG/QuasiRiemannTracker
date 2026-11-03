/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/SourceMomentsCore.lean
Original SHA-256: b40ff19b8c1978fcf324e3b39ad469c084085d65ec3dc5524f43ca89650b64aa
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.InverseFields
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.EnergyMesh
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.PlainInputExtract
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.PlainUnmarked
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorMoments

namespace LW56e2.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainUnmarkedField
local notation "O"=>HeckeFamily.O

/-- Actual raw fiber moments at fixed kappa=3/4, for every finite collection
of sufficiently fine positive distinct slots. The old geometry carried by
`F : SourceData D` is not used. All four `Moments` fields are proved from
OpenAI003 arithmetic/energy theorems under the accepted family ceiling. -/
theorem actual_source_moments_from_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (N:ℕ)(ell:Fin N→ℝ)(hell:∀j,0<ell j)(hinj:Function.Injective ell)
    (ε εm:ℝ)(hε:ε≤1/1000)(hεm:0<εm)(hεm1:εm≤1)
    (hfine:∀j,ell j≤plainMesh εm/200)
    (cB kB cH kH:ℝ)(hcB:0<cB)(hkB:0<kB)(hcH:0<cH)(hkH:0<kH)
    (hinputs:PositiveFineSourceInput F N εm (plainMesh εm) ∧
      (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
          0 1 2 (εm/4) U degree control A)):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
      1<Z ∧ ∀height:ℝ,0≤height→∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→∀d:ℝ,(1/200:ℝ)≤d→
      ∀a τ dmax slotMesh binWidth:ℝ,∀i:ℕ,∀z:ℂ,z.re=17/50→|z.im|≤height→
      SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows ell
        (fun _ y=>(F.w y:ℂ)) Z d a ε τ dmax 2 slotMesh binWidth i z 0
        (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then kB else kH)
        (C*(1+height)^J) height εm :=by

  obtain ⟨hpositive,hzero⟩:=hinputs
  have hmesh:0<plainMesh εm:=plainMesh_pos hεm
  obtain ⟨Ji,hi⟩:=source_batch_inverse_fields F.modulus ⊤ le_top F N ell hell hinj εm hεm
    cB kB cH kH hcB hkB hcH hkH
  obtain ⟨Jm,hm⟩:=source_batch_plain_marked_fine F N ell hell ε εm hε hεm hεm1 (plainMesh εm) hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=source_batch_plain_unmarked F N ell hell ε εm hε hεm hεm1 hzero
  refine ⟨Ji+Jm+Ju,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0<Z:=zero_lt_one.trans hi.1
  refine ⟨hi.1,?_⟩
  intro height hh rows hrows d hd a τ dmax slotMesh binWidth i z hz hzim
  have hbase:1≤1+height:=by linarith
  have hCi':Ci*(1+height)^Ji≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  intro q B hB hdata hreverse hslots hwidth hprofile hupper hexternal
    hslotMesh hbinWidth hfamily bin label left right hne
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im|≤height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0≤Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected (by simpa only [mul_zero,add_zero] using hcap) j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

end
end LW56e2.Transport.PhysicalHigh
