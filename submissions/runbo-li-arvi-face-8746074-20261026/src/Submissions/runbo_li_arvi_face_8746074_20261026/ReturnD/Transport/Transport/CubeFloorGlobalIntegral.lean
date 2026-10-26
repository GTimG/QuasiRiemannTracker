/- Repeated marks: fork of Collet's generic return module Transport.Transport.CubeFloorGlobalIntegral (Record1252270103Return,
Apache-2.0; inherited notices retained), re-elaborated in QRH.RepeatedMarks.Return against the
relaxed parameter bounds `Geometry.BoundsR`, with the physical face applied globally (Lemma D). -/
/- Ported from Cycle25 transport, weighted upstream PR6 and OpenAI/math; Apache-2.0 attribution retained. -/
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.TransportGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobalIntegral
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Transport.Transport.FloorExponent
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Transport.Transport.LowNormalizer
import Submissions.runbo_li_arvi_face_8746074_20261026.ReturnD.Transport.Transport.CubeFloorGlobal
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralExponent
namespace OAI

noncomputable section
variable [QRH.Record1252270103Return.Geometry.Parameters] [QRH.Record1252270103Return.Geometry.BoundsR]
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.RepeatedMarksReturn.TransportHighRowFamily
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem globalFloorIntegralPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_global_floor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0 < e) (he1 : e<1/1000) (heps : 0 < eps) (hc : 0 < c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0 < dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0 < rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0 < mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε < rmin*mesh) (hmargin : 0 < margin)
    (hheight : 2*τ < dmin*cost) (hloss : τ*(2+4*eps) < loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=RepeatedMarksReturn.Transport.Arithmetic.ell)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0 < C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      ‖finiteCentralCubeRows S hS hmax η rows T (globalFloorIntegralPoolOutside M H S N c b Yp) W Yp
        W0 W1 (Z^(RepeatedMarksReturn.Transport.Arithmetic.x:ℝ)) (Z^(RepeatedMarksReturn.Transport.Arithmetic.y:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(RepeatedMarksReturn.Transport.Transport.floorSourceExponent v+
            RepeatedMarksReturn.Transport.Transport.floorRealLoss N v e eps loss mesh) := by
  obtain ⟨Ca,hCa,hbound⟩ := actual_global_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cp*Ca,mul_pos hCp hCa,?_⟩
  intro η
  filter_upwards [hbound η,source_cube_height_eventually τ hτ] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  have hZp : 0 < Z := zero_lt_one.trans_le hZ.1
  let Yp : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
  have hheight : (3*i+1:ℕ)*Z^τ≤(3*i+2:ℕ)*Z^τ := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
    exact_mod_cast (show 3*i+1≤3*i+2 by omega)
  let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*RepeatedMarksReturn.Transport.Arithmetic.ell/20)+mesh*RepeatedMarksReturn.Transport.Arithmetic.ell)
  have hp := hprofile e (51/100) (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 le_rfl (by norm_num)
    hZ.2 hheight S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1) T
    (globalFloorIntegralPoolOutside M H S N c b Yp) (rayCubeFamily M H hH) hbin W Yp
    (Z^(RepeatedMarksReturn.Transport.Arithmetic.x:ℝ)) (Z^(RepeatedMarksReturn.Transport.Arithmetic.y:ℝ)) Z (by positivity) (by positivity) hZp mass (by dsimp [mass];positivity)
    (hb d hd hd' v hv rows hrows hnorm i hi hbin)
  apply hp.trans_eq
  rw [RepeatedMarksReturn.Transport.Transport.physical_scale_identity Z (51/100) e hZp]
  have hpowers : Z^(RepeatedMarksReturn.Transport.Transport.centralScale (51/100) e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*RepeatedMarksReturn.Transport.Arithmetic.ell/20)+mesh*RepeatedMarksReturn.Transport.Arithmetic.ell)=
      Z^(RepeatedMarksReturn.Transport.Transport.floorSourceExponent v+
        RepeatedMarksReturn.Transport.Transport.floorRealLoss N v e eps loss mesh) := by
    rw [←Real.rpow_add hZp]
    congr 1
    unfold RepeatedMarksReturn.Transport.Transport.floorSourceExponent RepeatedMarksReturn.Transport.Transport.floorRealLoss RepeatedMarksReturn.Transport.Transport.centralScale
    ring
  dsimp [mass]
  calc
    _ = (Cp*Ca)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^(RepeatedMarksReturn.Transport.Transport.centralScale (51/100) e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-(3*RepeatedMarksReturn.Transport.Arithmetic.ell/20)+mesh*RepeatedMarksReturn.Transport.Arithmetic.ell)) := by ring
    _ = _ := by rw [hpowers]

end SevenEighths.RepeatedMarksReturn.TransportHighRowFamily

end

end OAI
