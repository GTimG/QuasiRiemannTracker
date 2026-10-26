import Candidate.Target836.Target836FinalCommonProbe
import Candidate.Target836.Num836.Finite.Summation
import Candidate.Target836.Num836.Source.FullW
import Candidate.Target836.Num836.Finite.Transfer
import Candidate.Target836.Target836SourceLiteral
import Candidate.Cycle63.Physical.InitialMass.MarkedParameters
import Candidate.Cycle63.Physical.InitialMass.GeometryMeshChoice

/- Original module: Candidate.Target836.Target836MeshChoice. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                         

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open scoped Classical
open Filter OAI.SevenEighths HeckeFamily Target836DetectorCount

/-- Choose the slot data after a positive analytic mesh cap has been fixed.
The cap precedes the slot count, source profiles, exclusions and ray modulus. -/
theorem exists_chosen_data_with_mesh
    (hβ : Arithmetic.theta< HeckeZeroSupremum.beta)
    {meshCap : ℝ} (hmesh : 0< meshCap) :
    ∃ A : ChosenData, A.P.mesh≤ meshCap := by
  obtain ⟨hk,hk1,hbeta⟩ := moment_parameter_gates hβ
  have hbudget : 0< min ((HeckeZeroSupremum.beta-Arithmetic.theta)/10000) meshCap :=
    lt_min (by positivity) hmesh
  obtain ⟨D,hκ,hbound,hfine,hcommon,⟨P⟩⟩ := exists_compatible_data hk hk1 hbudget
  obtain ⟨F⟩ := exists_baseline_source D
  obtain ⟨counts⟩ := fresh_count_parameters D.toData (baselineSource D F)
  have hdet : ∀j,D.length j≤ DetectorAffine.detectorMesh D.t/200 := fun j=>
    (hcommon j).trans (div_le_div_of_nonneg_right commonMesh_le_detector (by norm_num))
  have hcount := hbound.trans (min_le_left _ _)
  have ht : D.t≤ meshCap := by
    have hsmall := hbound.trans (min_le_right _ _)
    have he := D.epsilon_pos
    have ht := D.t_pos
    linarith
  exact ⟨⟨D,hκ,hcount,hfine,hdet,P,F,counts⟩,P.mesh_small.trans ht⟩

/-- The actual numerator is needed for one suitably chosen set of data.
This avoids requiring a moment theorem for every otherwise admissible mesh. -/
def ChosenFiniteNumeratorInput : Prop :=
  Arithmetic.theta< HeckeZeroSupremum.beta →
  ∃ A : ChosenData, ∃ J : ℝ, 0≤ J ∧
    ∀ τ : ℝ, HeightAdmissible A.D A.P J τ →
    ∀η : Character,(∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) →
    FixedFiniteNumeratorInputAt A.D A.F A.P τ η

theorem common_probe_of_chosen_finite_numerator
    (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenFiniteNumeratorInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift := by
  intro hβ
  obtain ⟨A,J,hJ,hfinite⟩ := hinput hβ
  have hβ51 := (moment_parameter_gates hβ).2.2
  have hβhi : HeckeZeroSupremum.beta≤7/8 := by linarith [(moment_parameter_gates hβ).2.1]
  have hkβ : 2*HeckeZeroSupremum.beta-1≤ A.D.momentKappa := A.kappa_exact.ge
  have hjoint := actual_joint_height A.D A.F A.P A.counts hβ51 hkβ A.fine
    hdet hβhi A.detector_fine J hJ

  let loss := (HeckeZeroSupremum.beta-Arithmetic.theta)/2
  have hloss : 0< loss := by dsimp [loss];linarith
  have hgap : loss< HeckeZeroSupremum.beta-Arithmetic.theta := by dsimp [loss];linarith
  exact ⟨loss,A.P.sigma,hloss,hgap,A.P.sigma_pos,
    fixed_source_contract A.D A.F loss A.P.sigma hloss (fun η=> by
      obtain ⟨τ,hheight,hcount⟩ := hjoint η
      exact sourceProbe_high_of_finite_numerator_at A.D A.F A.P J τ hheight hβ.le η
        (hfinite τ hheight η hcount))⟩
end
end Target836.FinalAssembly

#print axioms Target836.FinalAssembly.exists_chosen_data_with_mesh
#print axioms Target836.FinalAssembly.common_probe_of_chosen_finite_numerator
end

/- Original module: Candidate.Target836.Num836.Finite.SourceCells. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/

set_option autoImplicit false
namespace Target836.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Target836DetectorCount FinalAssembly Target836HighTransport Cycle25.Numerator

/-- Source's genuine cell theorem is specialized to the actual buffered partition. -/
theorem actual_cells_of_affine (hgap : Arithmetic.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Numerator.Source.ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ActualFullWCellInput A J := by
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
end Target836.FiniteNumerator

#print axioms Target836.FiniteNumerator.actual_cells_of_affine
end

/- Original module: Candidate.Target836.Num836.Finite.Bridge. -/
section
/- Private .874836 actual numerator specialization; predecessor attribution retained. Apache-2.0. -/
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                           
                                        

set_option autoImplicit false
namespace Target836.FiniteNumerator
noncomputable section
open scoped Classical BigOperators
open Filter OAI.SevenEighths ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical
open Target836DetectorCount FinalAssembly Target836HighTransport

theorem target_positive (A : ChosenData) (hgap : Arithmetic.theta< HeckeZeroSupremum.beta) :
    0< HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma := by
  have ht:=A.P.t_padding
  have hs:=A.P.sigma_small
  have ha : (1/10:ℝ)< Arithmetic.theta+Assembly.signalShift := by
    norm_num [Arithmetic.theta,Assembly.signalShift,Arithmetic.x,Arithmetic.y,Arithmetic.ell]
  linarith

/-- Actual cell bounds and actual count moments imply the literal finite cube bound. -/
theorem fixed_numerator_of_cells (hgap : Arithmetic.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (J : ℝ) (hcell : ActualFullWCellInput A J)
    (τ : ℝ) (hheight : HeightAdmissible A.D A.P J τ) (η : Character)
    (hcount : ∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
        (C*Z^A.D.t) (Z^(2*τ))) : FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  intro n _
  obtain ⟨Cc,hCc,hcount⟩:=hcount
  obtain ⟨Cs,hCs,hcell⟩:=hcell τ hheight n η
  have hCcpos : 0< Cc:=zero_lt_one.trans_le hCc
  have hηpos : (0:ℝ)<(η.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (HeckeLogarithmicInput.modulus_norm_ge_one η)
  let C : ℝ:=Cs*Cc*(η.modulus.absNorm:ℝ)^(2*A.P.eps)
  have hC : 0< C:=by dsimp [C];positivity
  obtain ⟨Csum,hCsum,hsum⟩:=fullW_sum_bound A τ n η C hC
  obtain ⟨Ce,hCe,herror⟩:=actual_selected_error A τ hheight.1
  change ∃Ctot : ℝ,0< Ctot ∧ ∀ᶠZ : ℝ in atTop,∀idx grid : FreeRow→ℕ,
    ActualBufferedSelection A.F.modulus ⊤ le_top A.F.S A.F.exclusions A.F.maximal
      η rowPadding A.D.e τ n Z idx grid →
    ‖finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
      1 2 rowPadding A.D.e τ (fun _=> A.F.w) A.F.W A.F.W η Z idx grid‖ ≤
      Ctot*‖normalizer A.D A.F Z‖*Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma)
  refine ⟨Csum+1,by positivity,?_⟩
  filter_upwards [hcount,hcell,hsum,herror,eventually_ge_atTop ((Ce+1)*(η.modulus.absNorm:ℝ)^2),
    eventually_ge_atTop (1:ℝ)] with Z hc hcells hs he hlarge hZ
  intro idx grid hsel
  have hcells : FullWCellsAt A τ n η C Z:=hcells Cc hCc hc
  have hb:=hs hcells idx grid hsel
  obtain ⟨hN,herr⟩:=he n η idx grid hsel
  have hZp : 0< Z:=zero_lt_one.trans_le hZ
  have hsaving : Ce*(η.modulus.absNorm:ℝ)^2*Z^(-(1:ℝ))≤1 := by
    calc
      _ ≤ Z*Z^(-(1:ℝ)) := mul_le_mul_of_nonneg_right
        (by nlinarith only [hlarge,sq_nonneg (η.modulus.absNorm:ℝ)]) (by positivity)
      _ = 1 := by rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hZp.ne'
  have hone : (1:ℝ)≤ Z^(HeckeZeroSupremum.beta+Assembly.signalShift-A.P.sigma) :=
    Real.one_le_rpow hZ (target_positive A hgap).le
  let V := finiteNonfloorNumerator A.F.modulus ⊤ A.F.S A.F.exclusions A.F.maximal A.D.length
    1 2 rowPadding A.D.e τ (fun _=> A.F.w) A.F.W A.F.W η Z idx grid
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
theorem fixed_numerator_of_affine (hgap : Arithmetic.theta< HeckeZeroSupremum.beta)
    (A : ChosenData) (hAffine : Numerator.Source.ActualAffineInput A) :
    ∃J : ℝ,0≤ J ∧ ∀τ : ℝ,HeightAdmissible A.D A.P J τ →
      ∀η : Character,(∃C : ℝ,1≤ C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound A.D.toData (baselineSource A.D A.F) A.counts η Z τ
          (C*Z^A.D.t) (Z^(2*τ))) → FixedFiniteNumeratorInputAt A.D A.F A.P τ η := by
  obtain ⟨J,hJ,hcells⟩:=actual_cells_of_affine hgap A hAffine
  exact ⟨J,hJ,fun τ hheight η hcount=> fixed_numerator_of_cells hgap A J hcells τ hheight η hcount⟩
end
end Target836.FiniteNumerator


#print axioms Target836.FiniteNumerator.target_positive
#print axioms Target836.FiniteNumerator.fixed_numerator_of_cells
#print axioms Target836.FiniteNumerator.fixed_numerator_of_affine
end

/- Original module: Candidate.Target836.Target836ChosenAffine. -/
section
/- Source integration: PR50 8cb265dc base; PR56 67edfb7a detector affine interfaces.
   Original Hailey Collet, OpenAI and predecessor notices are retained.
   Detector affine contribution: DaysSky, with Claude assistance; Apache-2.0. -/

                                  
                                      

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open OAI.SevenEighths

/-- The genuine initial affine theorem is needed for one fixed choice of data. -/
def ChosenAffineInput : Prop :=
  Arithmetic.theta< HeckeZeroSupremum.beta →
    ∃A : ChosenData,Numerator.Source.ActualAffineInput A

/-- An analytic mesh cap is chosen before constructing slots and source data. -/
def MeshAffineInput : Prop :=
  Arithmetic.theta< HeckeZeroSupremum.beta →
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

theorem common_probe_of_chosen_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_finite_numerator hdet (chosen_finite_numerator_of_affine hinput)

theorem common_probe_of_mesh_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : MeshAffineInput) :
    Cycle25.UniformCommonProbe Arithmetic.theta Assembly.signalShift :=
  common_probe_of_chosen_affine hdet (chosen_affine_of_mesh hinput)

theorem beta_le_theta_of_chosen_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤ Arithmetic.theta :=
  Cycle25.beta_le_of_common_probe Assembly.theta_gt_half.le Assembly.theta_lt_seven_eighths.le
    (common_probe_of_chosen_affine hdet hinput)

theorem beta_le_rational_of_chosen_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenAffineInput) :
    HeckeZeroSupremum.beta≤(Target836.Arithmetic.theta:ℝ) :=
  beta_le_theta_of_chosen_affine hdet hinput

theorem hecke_nonzero_of_chosen_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (χ : HeckeFamily.Character) (s : ℂ) (hs : Arithmetic.theta< s.re)
    (hpole : s≠1 ∨ χ.residue≠1) : HeckeFamily.LFunction χ s≠0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
    ((beta_le_theta_of_chosen_affine hdet hinput).trans_lt hs) hpole

theorem dirichlet_nonzero_of_chosen_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : Arithmetic.theta< s.re) (hexc : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
  Cycle25.dirichlet_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) χ s hs hexc

/-- Mathlib's total zeta convention includes its nonzero value at 1. -/
theorem riemannZeta_nonzero_of_chosen_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta< s.re) : riemannZeta s≠0 :=
  Cycle25.zeta_of_hecke (by norm_num [Arithmetic.theta])
    (hecke_nonzero_of_chosen_affine hdet hinput) s hs

/-- The classical zeta region explicitly excludes the pole. -/
theorem zeta_nonzero_off_pole_of_chosen_affine (hdet : Target836InitialTransport.DetectorAffineInput)
    (hinput : ChosenAffineInput)
    (s : ℂ) (hs : Arithmetic.theta< s.re) (_hpole : s≠1) : riemannZeta s≠0 :=
  riemannZeta_nonzero_of_chosen_affine hdet hinput s hs
end
end Target836.FinalAssembly

#print axioms Target836.FinalAssembly.chosen_affine_of_mesh
#print axioms Target836.FinalAssembly.chosen_finite_numerator_of_affine
#print axioms Target836.FinalAssembly.common_probe_of_chosen_affine
#print axioms Target836.FinalAssembly.common_probe_of_mesh_affine
#print axioms Target836.FinalAssembly.beta_le_theta_of_chosen_affine
#print axioms Target836.FinalAssembly.beta_le_rational_of_chosen_affine
#print axioms Target836.FinalAssembly.hecke_nonzero_of_chosen_affine
#print axioms Target836.FinalAssembly.dirichlet_nonzero_of_chosen_affine
#print axioms Target836.FinalAssembly.riemannZeta_nonzero_of_chosen_affine
#print axioms Target836.FinalAssembly.zeta_nonzero_off_pole_of_chosen_affine
end

/- Original module: Candidate.Target836.Target836ChosenGeometry. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
namespace Target836.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass Target836SourceAssembly
open scoped SchwartzMap

/-- The chosen-source interface is exactly the literal geometry budget
followed by the proved physical-mass and affine assembly. The budget remains
an explicit analytic obligation; this adapter does not assert it. -/
theorem actual_affine_input_of_geometry (A : ChosenData) (bΦ δ τ ξ : ℝ)
    (hbΦ : 0< bΦ) (hδ : 0< δ) (hτ : 0< τ) (hξ : 0< ξ)
    (hδgap : δ≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000)
    (hsΦ : Function.support
      (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ)
    (hmesh : A.P.mesh≤ Cycle63FirstActual.comparisonMesh 1 1 (δ/2))
    (hbudget : Target836SourceAssembly.SourceLiteralAffineGeometryBudget A.F bΦ A.P.mesh (δ/4) τ ξ) :
    Numerator.Source.ActualAffineInput A := by
  have hgap : Arithmetic.theta< HeckeZeroSupremum.beta := by linarith
  have hβ:=moment_parameter_gates hgap
  obtain ⟨degree,S,C,hC,hbound⟩:=Target836SourceAssembly.weighted_source_affine_from_geometry A.F
    bΦ A.P.mesh δ τ ξ hbΦ A.P.mesh_pos hδ hτ hξ hmesh hβ.2.2 hβ.2.1 hbudget
  exact ⟨bΦ,δ,hδ,hδgap,hsΦ,degree,S,C,hC,hbound⟩

end
end Target836.FinalAssembly
#print axioms Target836.FinalAssembly.actual_affine_input_of_geometry
end

/- Original module: Candidate.Target836.Target836ChosenSetup. -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace Target836.FinalAssembly
noncomputable section
open OAI.SevenEighths Cycle63InitialMass Target836SourceAssembly Cycle63MarkedPlain

/-- This cap depends only on the outer error, before any dictionary is chosen. -/
def geometryChosenMesh (ε : ℝ) : ℝ :=
  markedGeometryMesh (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
    (Cycle63FirstActual.comparisonMesh 1 1 (ε/2)))

theorem geometry_chosen_mesh_admission (ε : ℝ) (hε : 0< ε) :
    let μ:=geometryLossUnit 1 (ε/4)
    0< geometryChosenMesh ε ∧
    geometryChosenMesh ε≤ Cycle63FirstActual.comparisonMesh 1 1 (ε/2) ∧
    geometryChosenMesh ε≤ Cycle25.Energy.commonMesh 2 28 1 (μ/8) ∧
    geometryChosenMesh ε≤ μ/8 ∧
    geometryChosenMesh ε<(902420521/120632400000:ℝ)/2 := by
  intro μ
  have ha:=geometry_analytic_mesh_admission 1 1 (ε/4) 2 28 1
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by norm_num)
  have hc:=Cycle63FirstActual.comparisonMesh_pos 1 1 (ε/2)
    (by norm_num) (by norm_num) (by positivity)
  have hle : geometryChosenMesh ε≤ geometryAnalyticMesh 1 1 (ε/4) 2 28 1 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hnew := marked_geometry_mesh_gates
    (min (geometryAnalyticMesh 1 1 (ε/4) 2 28 1)
      (Cycle63FirstActual.comparisonMesh 1 1 (ε/2))) (lt_min ha.1 hc)
  refine ⟨hnew.1,hnew.2.1.trans (min_le_right _ _),hle.trans ha.2.2.1,
    hle.trans ha.2.2.2.1,?_⟩
  simpa only [one_mul] using hle.trans_lt ha.2.2.2.2


/-- The marked cap is fixed before the chosen dictionary. -/
theorem geometry_chosen_marked_mesh (ε : ℝ) :
    geometryChosenMesh ε≤ markedRawMesh*markedCoreMin := by
  have hc : geometryChosenMesh ε≤ markedRawMesh*markedCoreMin/64 := min_le_right _ _
  have hp : 0≤ markedRawMesh*markedCoreMin := mul_nonneg marked_raw_mesh_gates.1.le
    (by norm_num [markedCoreMin])
  nlinarith

/-- Fix the loss and mesh before the chosen dictionary; enlarge only the
radial support bound to meet the high-family admission gate. No analytic
moment estimate is assumed or asserted here. -/
theorem exists_chosen_geometry_setup
    (hgap : Arithmetic.theta< HeckeZeroSupremum.beta) :
    ∃ ε : ℝ,0< ε ∧ ε≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 ∧
    ∃ A : ChosenData,A.P.mesh≤ geometryChosenMesh ε ∧
    ∃ bΦ : ℝ,2≤ bΦ ∧ Function.support
      (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ := by
  let ε:=(HeckeZeroSupremum.beta-Arithmetic.theta)/20000
  have hε : 0< ε := by dsimp [ε];positivity
  have hεgap : ε≤(HeckeZeroSupremum.beta-Arithmetic.theta)/10000 := by
    dsimp [ε];linarith
  obtain ⟨A,hA⟩:=exists_chosen_data_with_mesh hgap
    (geometry_chosen_mesh_admission ε hε).1
  obtain ⟨b,hb,hs⟩:=CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  refine ⟨ε,hε,hεgap,A,hA,max 2 b,le_max_left _ _,?_⟩
  intro x hx
  exact (show x≤ b from hs hx).trans (le_max_right _ _)

/-- A uniform source geometry estimate supplies the genuine chosen affine
input, with the mesh fixed before the dictionary and the support bound fixed
before its analytic height. The source estimate remains explicit here. -/
theorem chosen_affine_of_source_geometry
    (hsource : ∀{D : Cycle25.Weighted.MomentData}
      (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
      (εaffine mesh bΦ : ℝ),0< εaffine →
      mesh < (902420521/120632400000:ℝ)/2 → 0 ≤ mesh →
      mesh ≤ geometryLossUnit 1 εaffine/8 →
      mesh ≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8) →
      mesh≤ markedRawMesh*markedCoreMin →
      2≤ bΦ → 51/100≤ HeckeZeroSupremum.beta → HeckeZeroSupremum.beta≤7/8 →
      ∃τ : ℝ,0< τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
        Target836SourceAssembly.SourceLiteralAffineGeometryBudget F bΦ mesh εaffine τ
          (geometryLossUnit 1 εaffine/64)) : ChosenAffineInput := by
  intro hgap
  obtain ⟨ε,hε,hεgap,A,hA,bΦ,hbΦ,hsΦ⟩:=exists_chosen_geometry_setup hgap
  have hm:=geometry_chosen_mesh_admission ε hε
  obtain ⟨τ,hτ,_hτcap,hbudget⟩:=hsource A.F (ε/4) A.P.mesh bΦ (by positivity)
    (hA.trans_lt hm.2.2.2.2) A.P.mesh_pos.le
    (hA.trans hm.2.2.2.1) (hA.trans hm.2.2.1) (hA.trans (geometry_chosen_marked_mesh ε)) hbΦ
    (moment_parameter_gates hgap).2.2 baseline_beta
  refine ⟨A,actual_affine_input_of_geometry A bΦ ε τ (geometryLossUnit 1 (ε/4)/64)
    (by linarith) hε hτ ?_ hεgap hsΦ (hA.trans hm.2.1) hbudget⟩
  exact div_pos (geometry_loss_unit_pos 1 (ε/4) (by norm_num) (by positivity))
    (by norm_num)

end
end Target836.FinalAssembly
#print axioms Target836.FinalAssembly.geometry_chosen_mesh_admission
#print axioms Target836.FinalAssembly.exists_chosen_geometry_setup
#print axioms Target836.FinalAssembly.chosen_affine_of_source_geometry
end
