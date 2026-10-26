import Candidate.Cycle63.Numerator.Source.Actual
import Candidate.Cycle25.Numerator.FullWBound
import Candidate.Cycle63.Numerator.Finite.Summation
import Candidate.Cycle63.Numerator.Finite.Transfer
import Candidate.Cycle63.Assembly.Final.CommonProbe
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineAssembly

/- Original module: Candidate.Cycle63.Numerator.Source.FullW. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
noncomputable section
set_option maxHeartbeats 2400000
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace Cycle63.Numerator.Source
open Cycle63.Arithmetic Cycle63.Numerator.Scalar
open Cycle25.Weighted.Numerator Cycle25.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbePhysical HeckeFamily HeckeInverseAmplification
open Cycle63DetectorCount Cycle63.FinalAssembly
theorem source_height_absorption (J t τ : ℝ) (n : ℕ)
    (hJ : 0 ≤ J) (_ht : 0 < t) (hτ : 0 < τ) (hbudget : 2*τ*(1+J) ≤ t) :
    ∀ᶠZ : ℝ in atTop,∀i : ℕ,i ≤ n →
      (3+((3*i+1:ℕ):ℝ)*Z^τ)^J ≤ Z^t := by
  filter_upwards [HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+4) τ hτ,
    eventually_ge_atTop (1:ℝ)] with Z hn hZ
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hp : 1 ≤ Z^τ := Real.one_le_rpow hZ hτ.le
  intro i hi
  have hhi : (i:ℝ) ≤ n := by exact_mod_cast hi
  have hheight : 3+((3*i+1:ℕ):ℝ)*Z^τ ≤ Z^(2*τ) := by
    calc
      _ ≤ (3*(n:ℝ)+4)*Z^τ := by push_cast;nlinarith
      _ ≤ Z^τ*Z^τ := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = _ := by rw [←Real.rpow_add hZpos];congr 1;ring
  calc
    _ ≤ (Z^(2*τ))^J := Real.rpow_le_rpow (by positivity) hheight hJ
    _ = Z^(2*τ*J) := (Real.rpow_mul hZpos.le _ _).symm
    _ ≤ Z^t := Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith only [hbudget,hτ])

/-- Absorb the single fixed height degree after every amplitude class has
already been placed below the common numerical target. -/
theorem source_absorb_height (V : ℂ) (Z C H J E t : ℝ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hheight : (3+H)^J ≤ Z^t)
    (hV : ‖V‖ ≤ C*(3+H)^J*Z^(E-t)) :
    ‖V‖ ≤ C*Z^E := by
  calc
    _ ≤ C*(3+H)^J*Z^(E-t) := hV
    _ ≤ C*Z^t*Z^(E-t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hheight hC) (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hZ];congr 2;ring

def FullWCellBound (A : ChosenData) (η : Character) (Z τ : ℝ) (n : ℕ)
    (C C0 : ℝ) : Prop :=
  ∀(rows : Finset FreeRow) (d a : ℝ) (i : ℕ),d0≤d → d≤dPlus →
  51/100<a → a≤7/8 → i≤n →
  (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
    (calibrationForSet A.F.S A.F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-A.D.t)) →
  (∀u∈rows,(Z^d)^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^d) →
  (∀u∈rows,(rowCharacter A.F.S A.F.exclusions.prime u).residue≠1) →
  (∀u∈rows,Z^(d-2*A.D.t)≤rowNorm u) →
  (∀u∈rows,detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) (3*(i+1:ℕ)*Z^τ)<a+2*A.D.e) →
  (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily A.F.S A.F.exclusions.prime η u
    (rayCubeFamily A.F.modulus ⊤ le_top u)) ((3*i:ℕ)*Z^τ)) →
  ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows A.F.S A.F.exclusions A.F.maximal η rows
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W A.F.W (Z^x) (Z^y) Z A.D.e
    (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/
      Cycle63HighTransport.actualNormalizer A.F.modulus ⊤ A.F.S A.D.length 1 2 (fun _=>A.F.w) A.F.W A.F.W Z‖≤
    C*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget+A.D.t/8)

/-- The two remaining Mellin integrals and literal source normalization cost
only the displayed normalizer reserve, after the fixed degree is absorbed. -/
theorem actual_fullW_cells (hgap : theta<HeckeZeroSupremum.beta) (A : ChosenData)
    (hAffine : ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
    ∀n : ℕ,∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
    ∀C0 : ℝ,1≤C0 →
    SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ (C0*Z^A.D.t) (Z^(2*τ)) →
    FullWCellBound A η Z τ n C C0 := by
  obtain ⟨J,hJ,hraw⟩ := actual_raw_source hgap A hAffine
  obtain ⟨Ci,hCi,hi⟩ := Cycle25.Weighted.FullWContour.finiteFullW_uniform_norm_bound A.F.W 1 2
    (by norm_num) A.F.complex_support
  obtain ⟨Cn,hCn,hn⟩ := source_normalizer_bound A.D A.F
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  obtain ⟨Cw,hCw,hw⟩ := hraw τ hheight n η
  refine ⟨Ci*Cn*Cw,by positivity,?_⟩
  filter_upwards [hw,hn,source_height_absorption J A.D.t τ n hJ A.D.t_pos hheight.1 hheight.2.2.2.2.2,
    (tendsto_rpow_atTop hheight.1).eventually (eventually_gt_atTop (2:ℝ)),eventually_gt_atTop (1:ℝ)]
    with Z hw hn hheight hT hZ
  intro C0 hC0 hmom
  have hraw := hw C0 hC0 hmom
  unfold FullWCellBound
  intro rows d a i hd hdmax ha hatop hiidx hsource hrows hrow hfreq hnext hcurrent
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  let B : ℝ := Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*Z^(sourceTarget-kernelExponent a A.D.e)
  have hB : 0≤B := by dsimp [B];positivity
  have hintegrated : ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
      ‖Cycle25.Weighted.FullWContour.integratedDyadValue A.F.S A.F.exclusions A.F.maximal η rows
        (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
        (fun _ y=>(A.F.w y:ℂ)) (fun j=>Z^(A.D.length j)) A.F.W (Z^y)
        ((((a+16*A.D.e):ℝ):ℂ)+q.1*Complex.I) ((17/50:ℂ)+q.2*Complex.I)‖≤B := by
    intro q hq
    have hh := hraw rows d a i hd hdmax ha hatop hiidx hsource hrows hrow hfreq hnext hcurrent q hq
    rw [source_real_profile_eq A.F]
    exact source_absorb_height _ Z (Cw*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps))
      (((3*i+1:ℕ):ℝ)*Z^τ) J (sourceTarget-kernelExponent a A.D.e) A.D.t hZ0
      (by positivity) (hheight i hiidx) (by simpa only [sub_sub,add_comm] using hh)
  have hh := hi A.D.e a (Z^τ) (((3*i+1:ℕ):ℝ)*Z^τ) i A.D.e_pos A.D.e_small ha.le
    (by linarith) hT (by push_cast;have hp:=Real.rpow_nonneg hZ0.le τ;nlinarith)
    A.F.S A.F.exclusions A.F.maximal A.F.first η rows (fun u hu=>(hsource u hu).1)
    (sourcePrimePool A.F Z) (fun j=>source_prime_pool_outside A.F Z j)
    (rayCubeFamily A.F.modulus ⊤ le_top) hnext (fun _ y=>(A.F.w y:ℂ))
    (fun j=>Z^(A.D.length j)) A.F.W 1 2 (by norm_num) A.F.complex_support
    (Z^x) (Z^y) Z B (by positivity) (by positivity) hZ0 hB hintegrated
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)).trans_eq
  dsimp only [B]
  rw [←Real.rpow_mul hZ0.le]
  have hp : Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
      Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)=Z^(sourceTarget+A.D.t/8) := by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    unfold kernelExponent
    ring
  calc
    _ = (Ci*Cn*Cw)*C0*(η.modulus.absNorm:ℝ)^(2*A.P.eps)*
        (Z^(x*(1/2-17/50))*Z^(a+16*A.D.e+17/50-1)*
          Z^(sourceTarget-kernelExponent a A.D.e)*Z^(A.D.t/8)) := by ring
    _ = _ := by rw [hp]
end Cycle63.Numerator.Source
end

/- Original module: Candidate.Cycle63.Numerator.Finite.SourceCells. -/
section

set_option autoImplicit false
namespace Cycle63.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle63DetectorCount FinalAssembly Cycle63HighTransport Cycle25.Numerator

/-- Source's genuine cell theorem is specialized to the actual buffered partition. -/
theorem actual_cells_of_affine (hgap : Arithmetic.theta<HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Numerator.Source.ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ActualFullWCellInput A J := by
  obtain ⟨J,hJ,hcells⟩:=Numerator.Source.actual_fullW_cells hgap A hAffine
  refine ⟨J,hJ,?_⟩
  intro τ hheight n η
  obtain ⟨C,hC,hcells⟩:=hcells τ hheight n η
  refine ⟨C,hC,?_⟩
  filter_upwards [hcells,actual_cell_geometry A η τ n] with Z hc hg
  intro C0 hC0 hmom idx grid hsel k hk i hi j hj hne
  have hf:=hg idx grid hsel k i j hne
  have hrow : ∀u∈cellRows A.D A.F Z idx grid k i j,
      (rowCharacter A.F.S A.F.exclusions.prime u).residue≠1 := by
    intro u hu
    exact calibrated_row_nonprincipal A.F.S A.F.exclusions.prime A.F.maximal A.F.exclusions.bad
      u (hf.source_rows u hu).1 (hf.source_rows u hu).2.2.1
  have hb:=hc C0 hC0 hmom (cellRows A.D A.F Z idx grid k i j)
    (sourceDyadConductor Z A.D.t k) (51/100+A.D.e*j) i hf.d_lower hf.d_upper hf.a_lower hf.a_upper
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hf.source_rows hf.moment_rows hrow
    hf.frequency_lower hf.next_maximum hf.current_maximum
  convert hb using 1 <;> rfl
end
end Cycle63.FiniteNumerator
end

/- Original module: Candidate.Cycle63.Numerator.Finite.Bridge. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                           
                                        

set_option autoImplicit false
namespace Cycle63.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Cycle63DetectorCount FinalAssembly Cycle63HighTransport

theorem target_positive (A : ChosenData) (hgap : Arithmetic.theta<HeckeZeroSupremum.beta) :
    0<HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
  have ht:=A.P.t_padding
  have hs:=A.P.sigma_small
  have ha : (1/10:ℝ)<Arithmetic.theta+Assembly.signalShift := by
    norm_num [Arithmetic.theta,Assembly.signalShift,Arithmetic.x,Arithmetic.y,Arithmetic.ell]
  linarith

/-- Actual cell bounds and actual count moments imply the literal finite cube bound. -/
theorem fixed_numerator_of_cells (hgap : Arithmetic.theta<HeckeZeroSupremum.beta)
    (A : ChosenData) (J : ℝ) (hcell : ActualFullWCellInput A J)
    (τ : ℝ) (hheight : HeightAdmissible A.D A.P J τ) (η : Character)
    (hcount : ∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) : FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  intro n _
  obtain ⟨Cc,hCc,hcount⟩:=hcount
  obtain ⟨Cs,hCs,hcell⟩:=hcell τ hheight n η
  have hCcpos : 0<Cc:=zero_lt_one.trans_le hCc
  have hηpos : (0:ℝ)<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (HeckeLogarithmicInput.modulus_norm_ge_one η)
  let C : ℝ:=Cs*Cc*(η.modulus.absNorm:ℝ)^(2*A.P.eps)
  have hC : 0<C:=by dsimp [C];positivity
  obtain ⟨Csum,hCsum,hsum⟩:=fullW_sum_bound A τ n η C hC
  obtain ⟨Ce,hCe,herror⟩:=actual_selected_error A τ hheight.1
  change ∃Ctot : ℝ,0<Ctot ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
      1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid‖ ≤
      Ctot*‖normalizer A.D A.F Z‖*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  refine ⟨Csum+1,by positivity,?_⟩
  filter_upwards [hcount,hcell,hsum,herror,eventually_ge_atTop ((Ce+1)*(η.modulus.absNorm:ℝ)^2),
    eventually_ge_atTop (1:ℝ)] with Z hc hcells hs he hlarge hZ
  intro idx grid hsel
  have hcells : FullWCellsAt A τ n η C Z:=hcells Cc hCc hc
  have hb:=hs hcells idx grid hsel
  obtain ⟨hN,herr⟩:=he n η idx grid hsel
  have hZp : 0<Z:=zero_lt_one.trans_le hZ
  have hsaving : Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ))≤1 := by
    calc
      _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
        (by nlinarith only [hlarge,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
      _ = 1 := by rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hZp.ne'
  have hone : (1:ℝ)≤Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) :=
    Real.one_le_rpow hZ (target_positive A hgap).le
  let V := finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
    1 2 rowPadding A.D.e τ (fun _=>A.F.w) A.F.W A.F.W η Z idx grid
  let W := fullW A.D A.F η Z (selectedRows A.D A.F Z grid)
    (fun u=>51/100+A.D.e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)
  let N := normalizer A.D A.F Z
  let E := Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  have hnormalized : ‖V/N‖≤(Csum+1)*E := by
    calc
      _ = ‖(V/N-W/N)+W/N‖ := by rw [sub_add_cancel]
      _ ≤ ‖V/N-W/N‖+‖W/N‖ := norm_add_le _ _
      _ ≤ 1+Csum*E := add_le_add (herr.trans hsaving) hb
      _ ≤ (Csum+1)*E := by dsimp [E];nlinarith only [hone]
  rw [norm_div] at hnormalized
  have hraw:=(div_le_iff₀ (norm_pos_iff.mpr hN)).mp hnormalized
  simpa only [V,N,E,mul_assoc,mul_comm,mul_left_comm] using hraw

/-- The only remaining analytic input is the initial affine moment at this fixed data. -/
theorem fixed_numerator_of_affine (hgap : Arithmetic.theta<HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Numerator.Source.ActualAffineInput A) :
    ∃J : ℝ,0≤J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
      ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
          (C*Z^A.D.t) (Z^(2*τ))) → FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  obtain ⟨J,hJ,hcells⟩:=actual_cells_of_affine hgap A hAffine
  exact ⟨J,hJ,fun τ hheight η hcount=>fixed_numerator_of_cells hgap A J hcells τ hheight η hcount⟩
end
end Cycle63.FiniteNumerator
end

/- Original module: Candidate.Cycle63.Assembly.MeshChoice. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                         

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI.SevenEighths HeckeFamily Cycle63DetectorCount

/-- Choose the slot data after a positive analytic mesh cap has been fixed.
The cap precedes the slot count, source profiles, exclusions and ray modulus. -/
theorem exists_chosen_data_with_mesh
    (hβ : Arithmetic.theta<HeckeZeroSupremum.beta)
    {meshCap : ℝ} (hmesh : 0 < meshCap) :
    ∃ A : ChosenData, A.P.mesh ≤ meshCap := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  have hbudget : 0 < min ((HeckeZeroSupremum.beta-Arithmetic.theta)/10000) meshCap :=
    lt_min (by positivity) hmesh
  obtain ⟨D,hκ,hbound,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1 hbudget
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hdet : ∀j,D.length j≤DetectorAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (div_le_div_of_nonneg_right commonMesh_le_detector (by norm_num))
  have hcount := hbound.trans (min_le_left _ _)
  have ht : D.t ≤ meshCap := by
    have hsmall := hbound.trans (min_le_right _ _)
    have he := D.epsilon_pos
    have ht := D.t_pos
    linarith
  exact ⟨⟨D,hκ,hcount,hfine,hdet,P,F,counts⟩,P.mesh_small.trans ht⟩

/-- The actual numerator is needed for one suitably chosen set of data.
This avoids requiring a moment theorem for every otherwise admissible mesh. -/
def ChosenFiniteNumeratorInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
  ∃ A : ChosenData, ∃ J : ℝ, 0≤J ∧
    ∀ τ : ℝ, HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_chosen_finite_numerator
    (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenFiniteNumeratorInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,J,hJ,hfinite⟩ := hinput hβ
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hβhi : HeckeZeroSupremum.beta≤7/8 := by linarith [(moment_parameter_gates hβ).2.1]
  have hkβ : 2*HeckeZeroSupremum.beta-1≤A.D.momentKappa := A.kappa_exact.ge
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine
    hdet hβhi A.detector_fine J hJ

  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hgap : loss<HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss (fun η=>by
      obtain ⟨τ,hheight,hcount⟩ := hjoint η
      exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
        (hfinite τ hheight η hcount))⟩
end
end Cycle63.FinalAssembly

#print axioms Cycle63.FinalAssembly.exists_chosen_data_with_mesh
#print axioms Cycle63.FinalAssembly.common_probe_of_chosen_finite_numerator
end

/- Original module: Candidate.Cycle63.Assembly.ChosenAffine. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                  
                                      

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open OAI.SevenEighths

/-- The genuine initial affine theorem is needed for one fixed choice of data. -/
def ChosenAffineInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
    ∃A : ChosenData,Numerator.Source.ActualAffineInput A

/-- An analytic mesh cap is chosen before constructing slots and source data. -/
def MeshAffineInput : Prop :=
  Arithmetic.theta<HeckeZeroSupremum.beta →
    ∃meshCap : ℝ,0 < meshCap ∧ ∀A : ChosenData,A.P.mesh ≤ meshCap →
      Numerator.Source.ActualAffineInput A

theorem chosen_affine_of_mesh (hinput : MeshAffineInput) : ChosenAffineInput := by
  intro hβ
  obtain ⟨meshCap,hmesh,haffine⟩:=hinput hβ
  obtain ⟨A,hA⟩:=exists_chosen_data_with_mesh hβ hmesh
  exact ⟨A,haffine A hA⟩

theorem chosen_finite_numerator_of_affine (hinput : ChosenAffineInput) :
    ChosenFiniteNumeratorInput := by
  intro hβ
  obtain ⟨A,hAffine⟩:=hinput hβ
  obtain ⟨J,hJ,hfinite⟩:=FiniteNumerator.fixed_numerator_of_affine hβ A hAffine
  exact ⟨A,J,hJ,hfinite⟩

theorem common_probe_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_finite_numerator hdet (chosen_finite_numerator_of_affine hinput)

theorem common_probe_of_mesh_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : MeshAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_affine hdet (chosen_affine_of_mesh hinput)

theorem beta_le_theta_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤Arithmetic.theta :=
  Cycle25.beta_le_of_common_probe Assembly.theta_gt_half.le Assembly.theta_lt_seven_eighths.le
    (common_probe_of_chosen_affine hdet hinput)

theorem beta_le_rational_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤(Cycle63.Arithmetic.theta:ℝ) :=
  beta_le_theta_of_chosen_affine hdet hinput

theorem hecke_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (χ : HeckeFamily.Character) (s : ℂ) (hs : Arithmetic.theta<s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : HeckeFamily.LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_theta_of_chosen_affine hdet hinput).trans_lt hs) hpole

theorem dirichlet_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : Arithmetic.theta<s.re) (hexc : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  Cycle25.dirichlet_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) χ s hs hexc

/-- Mathlib's total zeta convention includes its nonzero value at 1. -/
theorem riemannZeta_nonzero_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) : riemannZeta s≠0 :=
  Cycle25.zeta_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) s hs

/-- The classical zeta region explicitly excludes the pole. -/
theorem zeta_nonzero_off_pole_of_chosen_affine (hdet : Cycle25ProbeFinalAssemblyCertifiedBands.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta<s.re) (_hpole : s≠1) : riemannZeta s≠0 :=
  riemannZeta_nonzero_of_chosen_affine hdet hinput s hs
end
end Cycle63.FinalAssembly

#print axioms Cycle63.FinalAssembly.chosen_affine_of_mesh
#print axioms Cycle63.FinalAssembly.chosen_finite_numerator_of_affine
#print axioms Cycle63.FinalAssembly.common_probe_of_chosen_affine
#print axioms Cycle63.FinalAssembly.common_probe_of_mesh_affine
#print axioms Cycle63.FinalAssembly.beta_le_theta_of_chosen_affine
#print axioms Cycle63.FinalAssembly.beta_le_rational_of_chosen_affine
#print axioms Cycle63.FinalAssembly.hecke_nonzero_of_chosen_affine
#print axioms Cycle63.FinalAssembly.dirichlet_nonzero_of_chosen_affine
#print axioms Cycle63.FinalAssembly.riemannZeta_nonzero_of_chosen_affine
#print axioms Cycle63.FinalAssembly.zeta_nonzero_off_pole_of_chosen_affine
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryChosenAffine. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace Cycle63.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass
open scoped SchwartzMap

/-- The chosen-source interface is exactly the literal geometry budget
followed by the proved physical-mass and affine assembly. The budget remains
an explicit analytic obligation; this adapter does not assert it. -/
theorem actual_affine_input_of_geometry (A : ChosenData) (bΦ δ τ ξ : ℝ)
    (hbΦ : 0<bΦ) (hδ : 0<δ) (hτ : 0<τ) (hξ : 0<ξ)
    (hδgap : δ≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000)
    (hsΦ : Function.support
      (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (hmesh : A.P.mesh≤Cycle63FirstActual.comparisonMesh 1 1 (δ/2))
    (hbudget : SourceLiteralAffineGeometryBudget A.F bΦ A.P.mesh (δ/4) τ ξ) :
    Numerator.Source.ActualAffineInput A := by
  have hgap : Arithmetic.theta<HeckeZeroSupremum.beta := by linarith
  have hβ:=moment_parameter_gates hgap
  obtain ⟨degree,S,C,hC,hbound⟩:=weighted_source_affine_from_geometry A.F
    bΦ A.P.mesh δ τ ξ hbΦ A.P.mesh_pos hδ hτ hξ hmesh hβ.2.2 hβ.2.1 hbudget
  exact ⟨bΦ,δ,hδ,hδgap,hsΦ,degree,S,C,hC,hbound⟩

end
end Cycle63.FinalAssembly
#print axioms Cycle63.FinalAssembly.actual_affine_input_of_geometry
end
