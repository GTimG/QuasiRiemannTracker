import Candidate.Uneven.EndpointProbeGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorNormalized
import Candidate.Uneven.EndpointTransportFloorExponent
import Candidate.Uneven.EndpointTransportLowNormalizer
import Candidate.Uneven.EndpointTransportCubeFloorGlobalIntegral
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorCollected
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition
import Candidate.Uneven.EndpointTransportNormalizedTransportSaving
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit

/- Original module: Candidate.Uneven.EndpointTransportCubeFloorNormalized. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.UnevenEndpointPhysicalHighRowFamily
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem normalizedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_floor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0 < dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0 < mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=UnevenEndpointPhysical.Arithmetic.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0 < nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (UnevenEndpointPhysical.Arithmetic.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (normalizedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(UnevenEndpointPhysical.Transport.floorSourceExponent v+
            UnevenEndpointPhysical.Transport.floorRealLoss N v e eps loss mesh+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤ A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨Cg,hCg,hbound⟩ := actual_global_floor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0 < ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := UnevenEndpointPhysicalLowNormalizer.actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Cg*Cn,mul_pos hCg hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (UnevenEndpointPhysical.Transport.floorSourceExponent v+
    UnevenEndpointPhysical.Transport.floorRealLoss N v e eps loss mesh) nu]
  ring

end SevenEighths.UnevenEndpointPhysicalHighRowFamily

end

end OAI
end

/- Original module: Candidate.Uneven.EndpointTransportCubeFloorSaving. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.UnevenEndpointPhysicalHighRowFamily
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem savingFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_cube_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0 < dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0 < mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=UnevenEndpointPhysical.Arithmetic.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0 < nu)
    (saving : ℝ) (_hsaving : 0 < saving)
    (htotal : 26*e+(N+8)*eps+loss+mesh*UnevenEndpointPhysical.Arithmetic.ell+nu+saving≤1/100) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v : ℝ),0≤ v → v≤ UnevenEndpointPhysical.Arithmetic.h+UnevenEndpointPhysical.Transport.rowExtension → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤ Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (UnevenEndpointPhysical.Arithmetic.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (savingFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(UnevenEndpointPhysical.Assembly.signal UnevenEndpointPhysical.Arithmetic.theta-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := actual_normalized_floor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv hvhi rows hrows hnorm i hi hbin
  dsimp only
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := UnevenEndpointPhysical.Transport.floor_source_margin hvhi
  have hl := UnevenEndpointPhysical.Transport.floor_loss_bound N (loss:=loss) (mesh:=mesh) (hvhi.trans UnevenEndpointPhysical.Transport.extended_h_lt_one.le) he.le heps.le
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
  linarith

end SevenEighths.UnevenEndpointPhysicalHighRowFamily

end

end OAI
end

/- Original module: Candidate.Uneven.EndpointTransportCubeFloorCollected. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.UnevenEndpointPhysicalHighRowFamily
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem collectedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c ≤ b) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0 ≤ W j t ∧ W j t ≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=UnevenEndpointPhysical.Arithmetic.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0 < nu)
    (saving : ℝ) (hsaving : 0 < saving)
    (htotal : 26*e+(N+8)*eps+loss+mesh*UnevenEndpointPhysical.Arithmetic.ell+nu+saving≤1/100) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin ≤ d → d ≤ dmax → ∀(v : ℝ),0 ≤ v → v ≤ UnevenEndpointPhysical.Arithmetic.h+UnevenEndpointPhysical.Transport.rowExtension → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-margin)) →
      (∀u∈rows,rowNorm u ≤ Z^v) →
      ∀idx : FreeRow→ℕ,(∀u∈rows,idx u ≤ n) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (UnevenEndpointPhysical.Arithmetic.ell)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (collectedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(UnevenEndpointPhysical.Assembly.signal UnevenEndpointPhysical.Arithmetic.theta-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := actual_floor_cube_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu saving hsaving htotal
  refine ⟨(n+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η] with Z hb
  intro d hd hd' v hv hvhi rows hrows hnorm idx hidx hbin
  dsimp only
  let Yp : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Yp j)
  let hT := collectedFloorPoolOutside M H S N c b Yp
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (UnevenEndpointPhysical.Arithmetic.ell)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
  let Ri : ℕ→Finset FreeRow := fun i=> rows.filter (fun u=> idx u=i)
  have hnormer := (hb d hd hd' v hv hvhi ∅ (by simp) (by simp) 0 (Nat.zero_le n) (by simp)).1
  refine ⟨hnormer,?_⟩
  have hpart := finiteCentralCubeRows_bin_partition S hS hmax η rows T hT WC Yp W0 W1
    (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (Z^τ) idx (fun _=>0) n 0 (fun u hu=>⟨hidx u hu,le_rfl⟩)
  have heq : finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
      (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑i∈Finset.range (n+1),finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ) := by
    simpa [cubeBinRows,Ri] using hpart
  change ‖finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
    (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤ _
  rw [heq,Finset.sum_div]
  apply (norm_sum_le _ _).trans
  have hboundi (i : ℕ) (hi : i∈Finset.range (n+1)) :
      ‖finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(UnevenEndpointPhysical.Assembly.signal UnevenEndpointPhysical.Arithmetic.theta-saving) := by
    have hsub : Ri i⊆rows := Finset.filter_subset _ _
    have hbi : ∀u∈Ri i,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e := by
      intro u hu
      have hh := hbin u (hsub hu)
      rwa [(Finset.mem_filter.mp hu).2] at hh
    exact (hb d hd hd' v hv hvhi (Ri i) (fun u hu=> hrows u (hsub hu))
      (fun u hu=> hnorm u (hsub hu)) i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hbi).2
  calc
    _ ≤ ∑i∈Finset.range (n+1),C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(UnevenEndpointPhysical.Assembly.signal UnevenEndpointPhysical.Arithmetic.theta-saving) := Finset.sum_le_sum hboundi
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];ring

end SevenEighths.UnevenEndpointPhysicalHighRowFamily

end

end OAI
end

/- Original module: Candidate.Uneven.EndpointTransportNonfloorTransport. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.UnevenEndpointPhysicalHighRowFamily
variable [config : _root_.OAI.SevenEighths.UnevenEndpoint.Configuration]
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

omit [NeZero M] in
private theorem nonfloorTransportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_nonfloor_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0 < e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/10000000000) (hτ : 0<τ)
    (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B) (hmin : 0 < ellMin) (hnu : 0 < nu)
    (hβlo : UnevenEndpointPhysical.Arithmetic.theta ≤ HeckeZeroSupremum.beta)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8:ℝ))
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin ≤ ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=UnevenEndpointPhysical.Arithmetic.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0 ≤ W j y ∧ W j y ≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0 < sigma)
    (hgeometric : sigma+8*e+nu≤1/20) (hprincipal : sigma+nu≤1/4000)
    (hwindow : sigma+e ≤ UnevenEndpointPhysical.Arithmetic.theta*ellMin) (hlarge : sigma+nu ≤ saving+UnevenEndpointPhysical.Assembly.signal UnevenEndpointPhysical.Arithmetic.theta)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0 < eps) (hR : 0 ≤ R) (hdmin : 0 < dmin) (hdmax : 0 ≤ dmax) (hdRange : dmin ≤ dmax)
    (hrmin : 0 < rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0 ≤ cost) (hmesh : 0 < mesh) (hmargin : 0 < margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε < rmin*mesh)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (hcap : UnevenEndpointPhysical.Arithmetic.h+ζ ≤ dmax-margin)
    (helllo : ∀j,dmax*rmin ≤ ell j) (hellhi : ∀j,ell j ≤ dmin*R)
    (hζcap : ζ ≤ UnevenEndpointPhysical.Transport.rowExtension)
    (hfloorbudget : 26*e+(K+8)*eps+loss+mesh*UnevenEndpointPhysical.Arithmetic.ell+nu+sigma≤1/100) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0 < n ∧ ∀η : Character,∃C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := nonfloorTransportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (UnevenEndpointPhysical.Arithmetic.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ) ≤ a ∧ a≤7/8 ∧
        a ≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) < a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ) < a+2*e ∧
        (51/100 < a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a ≤ s.re ∧ s.re < a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((UnevenEndpointPhysical.Arithmetic.h:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-(4+UnevenEndpointPhysical.Transport.b)/6) Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((UnevenEndpointPhysical.Arithmetic.h:ℝ)+ζ))) grid) T hT WC Yp
          W0 W1 (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-(4+UnevenEndpointPhysical.Transport.b)/6-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,htransport⟩ := actual_normalized_probe_transport_saving M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβlo hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    sigma hsigma hgeometric hprincipal hwindow hlarge
  obtain ⟨Cf,hCf,hfloor⟩ := actual_floor_rows_saving M H hH K n e eps a b B R dmin dmax rmin τ ε κ cost mesh
    (1/100) margin loss he he' heps ha hab hB hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    (by norm_num) hphasebudget hphasegap hmargin hheight hloss S hS hfirst hmax ell hellinj helllo hellhi
    W hsupp hW hWB hcompact hne hellsum W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    nu hnu sigma hsigma hfloorbudget
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  let C := Ct+Cf*(η.modulus.absNorm:ℝ)^(2*eps)
  have hC : 0 < C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [htransport,hfloor η,eventually_ge_atTop (1:ℝ)] with Z ht hf hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  let Yp : Fin K→ℝ := fun j=> Z^(ell j)
  let T : Fin K→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := nonfloorTransportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let rows := rowBand (Z^(1/100:ℝ)) (Z^((UnevenEndpointPhysical.Arithmetic.h:ℝ)+ζ))
  let floors := supportedFloorRows S hmax rows grid
  have hrows : ∀u∈floors,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(dmax-margin) := by
    intro u hu
    rcases (mem_supportedFloorRows S hmax rows grid u).mp hu with ⟨hur,hcal,hg⟩
    have hm := mem_rowBand.mp hur
    exact ⟨hm.1,hm.2.1,hcal,hm.2.2.le.trans (Real.rpow_le_rpow_of_exponent_le hZ hcap)⟩
  have hnorms : ∀u∈floors,rowNorm u ≤ Z^((UnevenEndpointPhysical.Arithmetic.h:ℝ)+ζ) := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedFloorRows S hmax rows grid u).mp hu).1).2.2.le
  have hfloorbin : ∀u∈floors,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e := by
    intro u hu
    have hg := ((mem_supportedFloorRows S hmax rows grid u).mp hu).2.2
    have hh := (hbins u).2.2.2.2.1
    simpa only [hg,Nat.cast_zero,mul_zero,add_zero] using hh
  have hb := (hf dmax hdRange le_rfl (UnevenEndpointPhysical.Arithmetic.h+ζ) (by linarith [UnevenEndpointPhysical.Transport.h_interval]) (by linarith) floors hrows hnorms idx
    (fun u hu=>(hlabels u).2.1) hfloorbin).2
  have hsplit := finiteCentralCubeRows_supported_split S hS hmax η rows T hT WC Yp W0 W1
    (Z^(UnevenEndpointPhysical.Arithmetic.x:ℝ)) (Z^(UnevenEndpointPhysical.Arithmetic.y:ℝ)) Z e grid (fun u=>(3*idx u+1:ℕ)*Z^τ)
  change _ ≤ Ct*Z^(HeckeZeroSupremum.beta-(4+UnevenEndpointPhysical.Transport.b)/6-sigma) at herror
  rw [hsplit] at herror
  have hh := normalized_nonfloor_error _ _ _ _ _ _ _ herror hb
  apply hh.trans
  have hβlower := hβlo
  have hp : Z^(UnevenEndpointPhysical.Assembly.signal UnevenEndpointPhysical.Arithmetic.theta-sigma) ≤ Z^(HeckeZeroSupremum.beta-(4+UnevenEndpointPhysical.Transport.b)/6-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by dsimp [UnevenEndpointPhysical.Assembly.signal]; rw [←UnevenEndpointPhysical.Transport.signalShift_eq]; linarith)
  calc
    _ ≤ Ct*Z^(HeckeZeroSupremum.beta-(4+UnevenEndpointPhysical.Transport.b)/6-sigma)+
      (Cf*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-(4+UnevenEndpointPhysical.Transport.b)/6-sigma) := by gcongr
    _ = _ := by dsimp [C];ring

end SevenEighths.UnevenEndpointPhysicalHighRowFamily

end

end OAI
end
