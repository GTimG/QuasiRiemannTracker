/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B004
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B009
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B016
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B025
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B026
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B034
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B035
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B036
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B037
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B041
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B043
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B044
import Submissions.gao_asymmetric_reserves_20261013.Bundles.B045
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalChildPaid
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual

/- BEGIN ORIGINAL MODULE Global.Weighted.SourceFinish ; sha256 b9f4da04d4cd83fa90faa7b8e358a4c9c160750a8231859430b2f33560a55e3f -/
section





/-! The final physical source specialization, conditional only on a literal
integrated numerator bound. This file does not assert that remaining bound. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set Complex
namespace Submission20261012.Global.ProbeAssembly
open OAI OAI.SevenEighths
open Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical ProbeRaySlots
open HeckeInverseAmplification PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

/-- The two remaining Mellin scale factors after integrating w. -/
def weightedSourceSZExponent (a e : ℝ) : ℝ :=
  Submission20261012.Global.lx*(1/2-17/50)+a+16*e+17/50-1

def weightedSourceNormalizer {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z : ℝ) : ℂ :=
  sourceResidueConstant F.W F.W F.modulus*
    (Probe.principalScalar Finset.univ Z Submission20261012.Global.ell
      (slotMass (Cycle25.Numerator.sourcePrimePool F Z)
        (residueWeights (fun _=> F.w) (fun j=> Z^(D.ell j)))) : ℂ)

theorem weighted_source_normalizer_bound {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      weightedSourceNormalizer D F Z≠0 ∧
      ‖(weightedSourceNormalizer D F Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact LowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.ell (fun j=>(D.slots_bounds j).1) D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _ y=>(F.bounded y).1) (fun _=> F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by have := D.t_pos;positivity)

/-- A fixed height degree is chosen before tau; the threshold may depend on n. -/
theorem weighted_source_height_absorption (J t τ : ℝ) (n : ℕ)
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
theorem weighted_source_absorb_height (V : ℂ) (Z C H J E t : ℝ)
    (hZ : 0 < Z) (hC : 0 ≤ C) (hheight : (3+H)^J ≤ Z^t)
    (hV : ‖V‖ ≤ C*(3+H)^J*Z^(E-t)) :
    ‖V‖ ≤ C*Z^E := by
  calc
    _ ≤ C*(3+H)^J*Z^(E-t) := hV
    _ ≤ C*Z^t*Z^(E-t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hheight hC) (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [mul_assoc,←Real.rpow_add hZ];congr 2;ring

/-- Literal integrated full-w bounds imply normalized full-w cells. This theorem
only performs the remaining Mellin integration and actual source normalization. -/
theorem weighted_source_normalized_fullW_of_integrated {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,∀(η : Character) (rows : Finset FreeRow)
      (a B H C0 Cw : ℝ) (i : ℕ),
      (∀u∈rows,u.val≠1) → (51/100:ℝ) ≤ a → a ≤ 1 → 2 < B → H ≤ (3*i+2:ℕ)*B →
      0 ≤ C0 → 0 ≤ Cw →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*B) < a+2*D.e) →
      let Yp : Fin D.N→ℝ := fun j=> Z^(D.ell j)
      let T := Cycle25.Numerator.sourcePrimePool F Z
      let hT := nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
      (∀q∈Cycle25.Weighted.FullWContour.szRectangle H,
        ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows T hT
          (fun _ y=>(F.w y:ℂ)) Yp F.W (Z^Submission20261012.Global.ly)
          (((a+16*D.e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)‖ ≤
          Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
            Z^(Submission20261012.Global.weightedTarget-weightedSourceSZExponent a D.e)) →
      ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η rows T hT
        (fun _ y=>(F.w y:ℂ)) Yp F.W F.W (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z D.e
        (fun _=> a) (fun _=> H)/weightedSourceNormalizer D F Z‖ ≤
        C*Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          Z^(Submission20261012.Global.weightedTarget+D.t/8) := by
  obtain ⟨Ci,hCi,hi⟩ := Cycle25.Weighted.FullWContour.finiteFullW_uniform_norm_bound F.W 1 2
    (by norm_num) F.complex_support
  obtain ⟨Cn,hCn,hn⟩ := weighted_source_normalizer_bound D F
  refine ⟨Ci*Cn,mul_pos hCi hCn,?_⟩
  filter_upwards [hn,eventually_ge_atTop (1:ℝ)] with Z hn hZ
  intro η rows a B H C0 Cw i hrow ha ha' hB hH hC0 hCw hbin
  dsimp only
  intro hg
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  let A := Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
    Z^(Submission20261012.Global.weightedTarget-weightedSourceSZExponent a D.e)
  have hA : 0 ≤ A := by dsimp[A];positivity
  have hb := hi D.e a B H i D.e_pos D.e_small ha ha' hB hH
    F.S F.exclusions F.maximal F.first η rows hrow
    (Cycle25.Numerator.sourcePrimePool F Z)
    (nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 (fun j=> Z^(D.ell j)))
    (rayCubeFamily F.modulus ⊤ le_top) hbin (fun _ y=>(F.w y:ℂ)) (fun j=> Z^(D.ell j))
    F.W 1 2 (by norm_num) F.complex_support
    (Z^Submission20261012.Global.lx) (Z^Submission20261012.Global.ly) Z A (by positivity) (by positivity) hZpos hA hg
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hb hn.2 (norm_nonneg _) (by positivity)).trans_eq
  dsimp [A]
  rw [←Real.rpow_mul hZpos.le]
  calc
    _ = (Ci*Cn)*Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
        (Z^(Submission20261012.Global.lx*(1/2-17/50))*Z^(a+16*D.e+17/50-1)*
        Z^(Submission20261012.Global.weightedTarget-weightedSourceSZExponent a D.e)*Z^(D.t/8)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
      congr 2
      unfold weightedSourceSZExponent
      ring


/-- The remaining numerical target on literal reconstructed row integrals.
Unlike FullWCellsAt this has not yet integrated the two external variables. -/
def IntegratedWeightedCellsAt {Δ : ℝ} (D : Submission20261012.Global.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character)
    (Z τ : ℝ) (n : ℕ) (Cw C0 : ℝ) : Prop :=
  ∀idx grid : FreeRow→ℕ,
    let rows := supportedNonfloorRows F.S F.maximal
      (rowBand (Z^(1/100:ℝ)) (Z^(Submission20261012.Global.h+D.t))) grid
    (∀u∈rows,idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/D.e⌋₊ ∧
      (51/100:ℝ)+D.e*grid u ≤ 7/8) →
    (∀u∈rows,detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(idx u+1:ℕ)*Z^τ) < 51/100+D.e*grid u+2*D.e) →
    (∀u∈rows,(51/100:ℝ)+D.e*grid u ≤ detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*idx u:ℕ)*Z^τ)) →
    ∀k∈smallDyadicIndices (Z^(Submission20261012.Global.h+D.t)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
      let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
      let Yp : Fin D.N→ℝ := fun j=> Z^(D.ell j)
      let T := Cycle25.Numerator.sourcePrimePool F Z
      let hT := nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
      rows'.Nonempty → (1/2:ℝ) < sourceDyadConductor Z D.t k →
      (1/3:ℝ) < 2*(51/100+D.e*j)-1 →
      sourceDyadConductor Z D.t k ≤ Submission20261012.Global.h+3*D.t →
      ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
        ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows' T hT
          (fun _ y=>(F.w y:ℂ)) Yp F.W (Z^Submission20261012.Global.ly)
          ((((51/100+D.e*j)+16*D.e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)‖ ≤
          Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
            Z^(Submission20261012.Global.weightedTarget-
              weightedSourceSZExponent (51/100+D.e*j) D.e)

/-- The literal integrated estimate closes the exact FullWCellsAt interface.
The constant is independent of the moment constant C0 and is linear in Cw. -/
theorem fullWCellsAt_of_integrated {Δ : ℝ}
    (D : Submission20261012.Global.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∃C : ℝ,0 < C ∧ ∀τ : ℝ,0 < τ → ∀n : ℕ,∀ᶠZ : ℝ in atTop,
      ∀η : Character,∀Cw C0 : ℝ,0 ≤ Cw → 0 ≤ C0 →
      IntegratedWeightedCellsAt D F η Z τ n Cw C0 →
      FullWCellsAt D F η Z τ n (C*Cw) C0 := by
  obtain ⟨C,hC,hfinish⟩ := weighted_source_normalized_fullW_of_integrated D F
  refine ⟨C,hC,?_⟩
  intro τ hτ n
  filter_upwards [hfinish,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))]
    with Z hfinish hB
  intro η Cw C0 hCw hC0 hint
  unfold FullWCellsAt
  intro idx grid
  dsimp only
  intro hlabels hnext hcurrent k hk i hi j hj
  intro hne hd hdelta htop
  let rows := supportedNonfloorRows F.S F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^(Submission20261012.Global.h+D.t))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows := (Finset.filter_subset _ _).trans Finset.inter_subset_left
  have ha : (51/100:ℝ) ≤ 51/100+D.e*j := by
    have hh : 0 ≤ D.e*(j:ℝ) := mul_nonneg D.e_pos.le (Nat.cast_nonneg j)
    linarith
  have ha' : (51/100:ℝ)+D.e*j ≤ 1 := by
    obtain ⟨u,hu⟩ := hne
    have huj := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
    have hh := (hlabels u (hsub hu)).2.2
    rw [huj] at hh
    linarith
  have hrow : ∀u∈rows',u.val≠1 := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsub hu)).1).1
  have hb : ∀u∈rows',detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(i+1:ℕ)*Z^τ) < 51/100+D.e*j+2*D.e := by
    intro u hu
    obtain ⟨_,hui,huj⟩ := (mem_cubeBinRows _ idx grid i j u).mp hu
    simpa only [hui,huj] using hnext u (hsub hu)
  have hH : (3*i+1:ℕ)*Z^τ ≤ (3*i+2:ℕ)*Z^τ := by
    have hzp : 0 ≤ Z^τ := le_trans (by norm_num : (0:ℝ) ≤ 2) hB.le
    gcongr
    omega
  have hh := hfinish η rows' (51/100+D.e*j) (Z^τ) ((3*i+1:ℕ)*Z^τ) C0 Cw i
    hrow ha ha' hB hH hC0 hCw hb
    (hint idx grid hlabels hnext hcurrent k hk i hi j hj hne hd hdelta htop)
  exact hh

end Submission20261012.Global.ProbeAssembly
end

#print axioms Submission20261012.Global.ProbeAssembly.weighted_source_normalized_fullW_of_integrated

#print axioms Submission20261012.Global.ProbeAssembly.fullWCellsAt_of_integrated
end
/- END ORIGINAL MODULE Global.Weighted.SourceFinish -/

/- BEGIN ORIGINAL MODULE Analytic.BufferedProduct ; sha256 2dbf2b099419076401f270293b5008c982cec51448965391b1a0d921e5f94db3 -/
section




set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredExceptionalProfile CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot ConcretePrimeRowBridge LocalMoment
local notation "O" => HeckeFamily.O

/-- A plain profile with exactly the source Mellin seminorm gates. -/
structure BufferedPlainProfile (n : ℕ) (profileBound : ℕ → ℝ) (a e : ℝ) where
  W : ℝ → ℂ
  A : ℝ
  B : ℝ
  σ : ℝ
  freq : ℝ
  lower_pos : 0 < A
  support : Function.support W ⊆ Icc A B
  smooth : ContDiff ℝ ∞ W
  mellin_two : ∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
    (1+|t|)^2*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound 2
  mellin_tail : ∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
    (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*Complex.I)‖ ≤ profileBound (n+2)

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def bufferedProductFamily {Slot : Type*} (η₀ : Slot → Character)
    (χ : Character) : Option (Slot × RayQuotient.Characters M H) → Character
  | none => χ
  | some (j, θ) => twistedFamily M H hH (χ.product (η₀ j).inverse) θ

lemma bufferedProductFamily_nonprincipal {Slot : Type*} (η₀ : Slot → Character)
    (η : Character) (z : O) (N : NaturalRow η z) (Q R : Ideal O)
    (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus) (hR : R ≠ 0) (hz : z ≠ 0)
    (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z) :
    ∀ label, (bufferedProductFamily M H hH η₀ (excluded N.character R) label).residue ≠ 1 := by
  intro label
  rcases label with _ | ⟨j, θ⟩
  · exact excluded_nonprincipal _ _ (N.nonprincipal hz Q R hR hex)
  · exact coefficient_equality_nonprincipal _ _
      (averaged_sector_coefficient M H hH N.character (η₀ j) R hR θ)
      (excluded_nonprincipal _ _ (sector_nonprincipal M H hH N (η₀ j) θ Q R
        hQM (hQη₀ j) hR hz hex))

lemma zeroMaximum_pullback_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : κ → Character) (hχ : ∀ j, (χ j).residue ≠ 1) (f : ι → κ) (T : ℝ) :
    zeroMaximum (fun i => χ (f i)) (fun i => hχ (f i)) T ≤ zeroMaximum χ hχ T := by
  apply zeroMaximum_le_of_zero_inclusion
  intro i
  exact ⟨f i, fun _ _ hz => hz⟩

lemma squared_product_bound {Slot : Type*} [Fintype Slot]
    (U δ ε C : ℝ) (Cp : Slot → ℝ) (r₁ r₂ : ℝ) (r : Slot → ℝ)
    (p₁ p₂ : ℂ) (v : Slot → ℂ) (hU : 0 < U) (hC : 0 ≤ C) (hCp : ∀ j, 0 ≤ Cp j)
    (hp₁ : ‖p₁‖^2 ≤ C*U^(δ*r₁+ε)) (hp₂ : ‖p₂‖^2 ≤ C*U^(δ*r₂+ε))
    (hv : ∀ j, ‖v j‖^2 ≤ (Cp j)^2*U^(δ*r j+2*ε)) :
    ‖p₁*p₂*∏ j, v j‖^2 ≤
      (C^2*∏ j, (Cp j)^2)*U^(δ*(r₁+r₂+∑ j, r j)+(2+2*(Fintype.card Slot : ℝ))*ε) := by
  have hp : ∏ j, ‖v j‖^2 ≤ ∏ j, (Cp j)^2*U^(δ*r j+2*ε) :=
    Finset.prod_le_prod₀ (fun j _ => sq_nonneg _) (fun j _ => hv j)
  have hrpow : (∏ j, U^(δ*r j+2*ε)) = U^(∑ j, (δ*r j+2*ε)) := by
    exact (Real.rpow_sum_of_pos hU _ Finset.univ).symm
  calc
    ‖p₁*p₂*∏ j, v j‖^2 = (‖p₁‖^2*‖p₂‖^2)*(∏ j, ‖v j‖^2) := by
      rw [norm_mul, norm_mul, norm_prod, mul_pow, mul_pow, Finset.prod_pow]
    _ ≤ ((C*U^(δ*r₁+ε))*(C*U^(δ*r₂+ε)))*(∏ j, (Cp j)^2*U^(δ*r j+2*ε)) := by
      exact mul_le_mul (mul_le_mul hp₁ hp₂ (sq_nonneg _) (by positivity)) hp (by positivity) (by positivity)
    _ = _ := by
      rw [Finset.prod_mul_distrib, hrpow]
      have hexp : δ*(r₁+r₂+∑ j, r j)+(2+2*(Fintype.card Slot : ℝ))*ε =
          (δ*r₁+ε)+(δ*r₂+ε)+(∑ j, (δ*r j+2*ε)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring
      rw [hexp]
      simp only [Real.rpow_add hU]
      ring

/-- Actual pointwise payment for two independent plain profiles and the
canonical relative prime pools. All constants precede the live row, scales,
heights and profiles. A single complete buffered maximum controls every factor. -/
theorem natural_buffered_product_bound {Slot : Type*} [Fintype Slot]
    (η₀ : Slot → Character) (Q : Ideal O) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
    (V : Slot → ℝ → ℂ) (A B : Slot → ℝ) (hA : ∀ j, 0 < A j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (A j) (B j)) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (Rwidth dmax τ ε e κ ηaux σmin σmax loss : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hloss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ loss)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ →
      ∀ (η : Character) (z : O) (N : NaturalRow η z) (R : Ideal O)
        (hR : R ≠ 0) (hz : z ≠ 0)
        (hex : ¬FixedInducingRow η Q (fixedBadMask*idealGenerator R) 1 z),
      let χ := bufferedProductFamily M H hH η₀ (excluded N.character R)
      let hχ := bufferedProductFamily_nonprincipal M H hH η₀ η z N Q R hQM hQη₀ hR hz hex
      ∀ (a : ℝ) (i : ℕ), 51/100 ≤ a → a ≤ 1 →
      zeroMaximum χ hχ (3*(i+1 : ℕ)*Z^τ) < a+2*e →
      ∀ (P₁ P₂ : BufferedPlainProfile n profileBound a e) (r₁ r₂ : ℝ)
        (r σ v : Slot → ℝ) (t : ℝ),
      0 ≤ r₁ → r₁ ≤ Rwidth → 0 ≤ r₂ → r₂ ≤ Rwidth →
      (∀ j, 0 ≤ r j ∧ r j ≤ Rwidth ∧ σmin ≤ σ j ∧ σ j ≤ σmax) →
      (∀ label, (χ label).modulus.absNorm ≤ Z^d) →
      |P₁.freq|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      |P₂.freq|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ →
      (∀ j, |t+v j|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) →
      (3+(3*i+2 : ℕ)*Z^τ)^4 ≤ (Z^d)^ηaux →
      (3+(3*i+2 : ℕ)*Z^τ)^2 ≤ (Z^d)^ηaux →
      (∀ j, 2*(|Real.log (A j)|+|Real.log (B j)|)+1 ≤ Real.log ((Z^d)^(r j))) →
      ‖((Real.sqrt ((Z^d)^r₁) : ℂ)⁻¹ * rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z
          (twistProfile P₁.W P₁.σ P₁.freq) 0 ((Z^d)^r₁)) *
        ((Real.sqrt ((Z^d)^r₂) : ℂ)⁻¹ * rowTwistedSum η (fixedBadMask*idealGenerator R) 1 z
          (twistProfile P₂.W P₂.σ P₂.freq) 0 ((Z^d)^r₂)) *
        ∏ j, normalizedSlot η (fixedBadMask*idealGenerator R) 1 z
          (primePool M H (B j) ((Z^d)^(r j)))
          (fun I => idealCoeff (η₀ j).inverse I * annularWeight (V j) ((Z^d)^(r j)) (σ j) (v j) I)
          t ((Z^d)^(r j))‖^2 ≤ C*(Z^d)^((2*a-1)*(r₁+r₂+∑ j, r j)+loss) := by
  obtain ⟨n, Cp, hCp, hplain⟩ := natural_plain_buffered_bound Rwidth dmax τ ε e κ ηaux
    hRw hdmax hτ hε he he' hκ hκone hη hbudget profileBound hprofile
  choose Cs hCs hslot using fun j => natural_relative_slot_buffered_bound M H hH
    (V j) (A j) (B j) (hA j) (hVs j) (hV j) Rwidth dmax τ ε e κ ηaux σmin σmax
    hRw hdmax hτ hε he he' hκ hη hprimebudget
  refine ⟨n, Cp^2*∏ j, (Cs j)^2,
    mul_pos (sq_pos_of_pos hCp) (Finset.prod_pos (fun j _ => sq_pos_of_pos (hCs j))), ?_⟩
  intro Z d hZ hd hd' hbase hT η z N R hR hz hex χ hχ a i ha ha' hmax P₁ P₂ r₁ r₂
    r σ v t hr₁ hr₁' hr₂ hr₂' hr hmod hfreq₁ hfreq₂ hfreq hheight₄ hheight₂ hlarge
  have hplainmax : zeroMaximum (fun _ : Unit => excluded N.character R)
      (fun _ => excluded_nonprincipal _ _ (N.nonprincipal hz Q R hR hex))
      (3*(i+1 : ℕ)*Z^τ) < a+2*e :=
    (zeroMaximum_pullback_le χ hχ (fun _ : Unit => none) _).trans_lt hmax
  have plainbound (P : BufferedPlainProfile n profileBound a e) (r₀ : ℝ)
      (hr₀ : 0 ≤ r₀) (hr₀' : r₀ ≤ Rwidth)
      (hf : |P.freq|+Z^τ/2 ≤ (3*i+2 : ℕ)*Z^τ) :=
    (hplain Z d hZ hd hd' hT (fun _ : Unit => η) (fun _ : Unit => z) (fun _ => N)
      Q (fun _ => R) (fun _ => hz) (fun _ => hR) (fun _ => hex) a i ha ha' hplainmax
      () P.W P.A P.B P.lower_pos P.support P.smooth r₀ P.σ P.freq (hmod none)
      hr₀ hr₀' hf hheight₄ P.mellin_two P.mellin_tail).1
  have slotbound (j : Slot) := hslot j Z d hZ hd hd' hbase hT η z N (η₀ j) R hR
    (fun θ => hχ (some (j, θ))) a i ha ha'
    ((zeroMaximum_pullback_le χ hχ (fun θ => some (j, θ)) _).trans_lt hmax)
    (r j) (σ j) t (v j) (hr j).1 (hr j).2.1 (hr j).2.2.1 (hr j).2.2.2 (hlarge j)
    (fun θ => hmod (some (j, θ))) (hfreq j) hheight₂
  have hb := squared_product_bound (Z^d) (2*a-1) ε Cp Cs r₁ r₂ r _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) d) hCp.le (fun j => (hCs j).le)
    (plainbound P₁ r₁ hr₁ hr₁' hfreq₁) (plainbound P₂ r₂ hr₂ hr₂' hfreq₂) slotbound
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)) (by positivity)

#print axioms natural_buffered_product_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.BufferedProduct -/

/- BEGIN ORIGINAL MODULE Analytic.JointActualMainRadius ; sha256 656aa06ec68d6ad5a612e3e4c20cbadb0005212b12a5a3095250564adaf41428 -/
section




/-! The coherent amplifier radius and the numerical second-ball radius
refer to the same literal first common ideals and puncture. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentFirstScale CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentFirstPhysicalSource
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
open ActualEisensteinCubic
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

namespace FirstJointLabel

theorem self_common_parts (q : FirstJointLabel ι) :
    commonPart q.C q.D = q.C ∧ commonPart q.D q.C = q.D := by
  have hcd : IdealMobiusDivisorSum.primeSupport q.C = IdealMobiusDivisorSum.primeSupport q.D := q.hCD
  have hc := reconstruct q.C q.D q.hC.1
  have hd := reconstruct q.D q.C q.hD.1
  have hrc : residualPart q.C q.D = 1 := by simp [residualPart,hcd]
  have hrd : residualPart q.D q.C = 1 := by simp [residualPart,hcd]
  simpa only [hrc,hrd,mul_one] using And.intro hc.symm hd.symm

theorem nominal_scale_power (q : FirstJointLabel ι) (Z A M : ℝ) (hZ : 1 < Z) :
    firstNominalScale q.C q.D (Ideal.span {q.puncture}) (Z^M) (Z^A) =
      Z^(2*A-q.leftWidth Z-q.rightWidth Z+q.activeWidth Z+q.punctureWidth Z-M) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hnc := norm_pos q.C q.hC.1
  have hnd := norm_pos q.D q.hD.1
  have hnr := active_norm_pos q.C q.D
  have hne : 0 < ((Ideal.span {q.puncture}).absNorm : ℝ) := by
    apply norm_pos
    exact Ideal.span_singleton_eq_bot.not.mpr
      (primeSubsetGenerator_ne_zero _ _)
  have hc : (q.C.absNorm : ℝ) = Z^(q.leftWidth Z) := (Real.rpow_logb hz hZ.ne' hnc).symm
  have hd : (q.D.absNorm : ℝ) = Z^(q.rightWidth Z) := (Real.rpow_logb hz hZ.ne' hnd).symm
  have hr : ((Ideal.span {activeConductor q.C q.D}).absNorm : ℝ) = Z^(q.activeWidth Z) :=
    (Real.rpow_logb hz hZ.ne' hnr).symm
  have he : ((Ideal.span {q.puncture}).absNorm : ℝ) = Z^(q.punctureWidth Z) := by
    rw [punctureWidth,eisEmbedding_norm_sq_eq_absNorm_span]
    exact (Real.rpow_logb hz hZ.ne' hne).symm
  rw [firstNominalScale,q.self_common_parts.1,q.self_common_parts.2,hc,hd,hr,he]
  rw [show (2:ℝ)*A = A+A by ring]
  simp only [Real.rpow_add hz,Real.rpow_sub hz]
  ring

theorem nominal_log_power (q : FirstJointLabel ι) (Z A M : ℝ) (hZ : 1 < Z) :
    nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) (Z^A) Z =
      2*A-q.leftWidth Z-q.rightWidth Z+q.activeWidth Z+q.punctureWidth Z-M := by
  rw [nominalLog,q.nominal_scale_power Z A M hZ,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem main_radius_exact (q : FirstJointLabel ι) (Z A M δ reserve : ℝ) (hZ : 1 < Z) :
    mainCommonRadius Z (q.rightWidth Z)
      (nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) (Z^A) Z)
      (q.leftWidth Z) (9/500) δ reserve =
    jointSecondBall Z A (q.leftWidth Z) (q.rightWidth Z) (q.activeWidth Z)
      (q.punctureWidth Z) M (3/500) (δ+reserve) := by
  rw [q.nominal_log_power Z A M hZ]
  unfold mainCommonRadius jointSecondBall
  congr 1
  ring

theorem nominal_scale_mono_source (q : FirstJointLabel ι) (K X Y : ℝ)
    (hK : 0 < K) (hX : 0 ≤ X) (hXY : X ≤ Y) :
    firstNominalScale q.C q.D (Ideal.span {q.puncture}) K X ≤
      firstNominalScale q.C q.D (Ideal.span {q.puncture}) K Y := by
  unfold firstNominalScale
  gcongr

theorem eventually_main_radius_enlarged (margin : ℝ) (hmargin : 0 < margin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (q : FirstJointLabel ι) (A M X sourceLoss δ reserve omega : ℝ),
      0 < X → X ≤ Z^(A+sourceLoss) → δ+reserve+2*sourceLoss+margin ≤ omega →
      2*mainCommonRadius Z (q.rightWidth Z)
        (nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) X Z)
        (q.leftWidth Z) (9/500) δ reserve ≤
      jointSecondBall Z A (q.leftWidth Z) (q.rightWidth Z) (q.activeWidth Z)
        (q.punctureWidth Z) M (3/500) omega := by
  filter_upwards [(tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z h2 hZ
  refine ⟨hZ,?_⟩
  intro q A M X sourceLoss δ reserve omega hX hcap hbudget
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hE : Ideal.span {q.puncture} ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeSubsetGenerator_ne_zero _ _)
  have hs := q.nominal_scale_mono_source (Z^M) X (Z^(A+sourceLoss)) (by positivity) hX.le hcap
  have hl := Real.logb_le_logb_of_le hZ
    (firstNominalScale_pos q.C q.D _ hE _ _ (by positivity) hX) hs
  change nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) X Z ≤
    nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) (Z^(A+sourceLoss)) Z at hl
  rw [q.nominal_log_power Z (A+sourceLoss) M hZ] at hl
  unfold mainCommonRadius jointSecondBall
  calc
    _ ≤ Z^margin*Z^(nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) X Z+
      max (q.rightWidth Z-q.leftWidth Z) 0+2*(9/500)+δ+reserve) := by gcongr
    _ = Z^(margin+(nominalLog q.C q.D (Ideal.span {q.puncture}) (Z^M) X Z+
      max (q.rightWidth Z-q.leftWidth Z) 0+2*(9/500)+δ+reserve)) := (Real.rpow_add hz _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)

theorem commonEnergy_radius_le (q : FirstJointLabel ι) (η : Character) (t : ℝ) (L : Ideal O)
    (Y V : ℝ) (hY : 0 < Y) (hV : 0 < V) (hscale : 2*Y ≤ V) :
    (commonEnergy q.data q.C q.hC η t L ballProfile Y).re ≤
      (commonEnergy q.data q.C q.hC η t L ballProfile V).re :=
  sourceGaussEnergy_radius_le (commonSecondColumns q.data q.C q.hC)
    (commonSecondBeta q.data q.C L) (CenteredMomentHeckeColumnWindow.heightCoeff η t)
    Y V hY hV hscale

#print axioms eventually_main_radius_enlarged
#print axioms commonEnergy_radius_le

end FirstJointLabel
#print axioms FirstJointLabel.main_radius_exact
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointActualMainRadius -/

/- BEGIN ORIGINAL MODULE Analytic.JointExceptionalLedger ; sha256 a3fae8f16bc5c9fede7870460c2924fadbd87df4cee3f8ee53c28018a7582ebb -/
section





/-! The exceptional savings evaluated on the literal common ideals and
the enlarged-ball gain. Both F₁ and F₂ are the source expressions; their
lower bounds are derived from actual common-support and correlation lemmas. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.Local44.Analytic
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentRankinRadical
open CenteredMomentFirstExceptionalPrefactor CenteredMomentFirstExtractedLedger
open CenteredMomentFirstScale CenteredMomentDescentLedger CenteredMomentSectorLocalization
open CenteredMomentSecondCanonical CenteredMomentSecondLedger
open CenteredMomentSupportedCorrelation CenteredMomentSupport
local notation "O" => HeckeFamily.O

def enlargedFirstSaving (C D E : Ideal O) (Z q D₀ a omega : ℝ) : ℝ :=
  let c := Real.logb Z (C.absNorm : ℝ)
  let d := Real.logb Z (D.absNorm : ℝ)
  let p := Real.logb Z ((commonRadical C D).absNorm : ℝ)
  let R := Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)
  firstSaving c D₀ 0 (q+R+Real.logb Z (E.absNorm : ℝ)) 0 (c+d-2*p-R)
    (D₀-d+max (d-c) 0+6*a+omega) a

theorem actual_enlarged_first_saving (C D E : Ideal O)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D) (hE : E ≠ 0)
    (Z q D₀ a omega : ℝ) (hZ : 1 < Z) (hq : 0 ≤ q) :
    2*Real.logb Z (C.absNorm : ℝ)/3-4*a-5*omega/6 ≤
      enlargedFirstSaving C D E Z q D₀ a omega := by
  have hRa : (1 : ℝ) ≤ (Ideal.span {activeConductor C D}).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (finitePrimeModulus_ne_zero _)))
  have hEa : (1 : ℝ) ≤ E.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE)
  have hR := Real.logb_nonneg hZ hRa
  have he := Real.logb_nonneg hZ hEa
  have hb := actual_extracted_first_saving C D hC hD Z hZ
  dsimp only at hb
  rw [commonPart_of_equal_support C D hC.1 hCD,
    commonPart_of_equal_support D C hD.1 hCD.symm] at hb
  specialize hb (Real.logb Z (D.absNorm : ℝ)) 0
    (q+Real.logb Z ((Ideal.span {activeConductor C D}).absNorm : ℝ)+Real.logb Z (E.absNorm : ℝ))
    0 (max (Real.logb Z (D.absNorm : ℝ)-Real.logb Z (C.absNorm : ℝ)) 0) 0 0 0
    le_rfl (by linarith) le_rfl le_rfl le_rfl (by linarith) (by linarith)
    (by simp) le_rfl (by norm_num)
  dsimp only [enlargedFirstSaving, firstSaving] at hb ⊢
  linarith

/-- The main exceptional reserve, with F₂ obtained from the actual
nonzero ideal correlation and F₁ from the source common-support allowance. -/
theorem actual_local_exceptional_stage (C₁ D₁ E₁ C₂ D₂ : Ideal O)
    (hC₁ : Supported C₁) (hD₁ : Supported D₁)
    (hCD₁ : CompletedGauss.primeSupport C₁ = CompletedGauss.primeSupport D₁) (hE₁ : E₁ ≠ 0)
    (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (hCD₂ : CompletedGauss.primeSupport C₂ = CompletedGauss.primeSupport D₂)
    (u : O) (hne : idealCorrelation C₂ D₂ hC₂ hD₂ (commonFrequencyGenerator C₂ D₂*u) ≠ 0)
    (Z A q D₀ omega : ℝ) (hZ : 1 < Z) (hA : A ≤ 883/1000) (hq : 0 ≤ q) :
    A-5/6-enlargedFirstSaving C₁ D₁ E₁ Z q D₀ (3/500) omega-
      secondSaving (commonPrime C₂ D₂) (leftExponent C₂ D₂) (rightExponent C₂ D₂) u Z-
      max (1/4-(Real.logb Z (C₁.absNorm : ℝ)+
        min (Real.logb Z (C₂.absNorm : ℝ)) (Real.logb Z (D₂.absNorm : ℝ)))) 0 ≤
      -93/1000+5*omega/6 := by
  have hfirst := actual_enlarged_first_saving C₁ D₁ E₁ hC₁ hD₁ hCD₁ hE₁
    Z q D₀ (3/500) omega hZ hq
  have hsecond := actual_ideal_secondSaving_lower C₂ D₂ hC₂ hD₂ hCD₂ u Z hZ hne
  have hm₁ := min_le_left (Real.logb Z (C₂.absNorm : ℝ)) (Real.logb Z (D₂.absNorm : ℝ))
  have hm₂ := min_le_right (Real.logb Z (C₂.absNorm : ℝ)) (Real.logb Z (D₂.absNorm : ℝ))
  have hc : 2*(Real.logb Z (C₁.absNorm : ℝ)+
      min (Real.logb Z (C₂.absNorm : ℝ)) (Real.logb Z (D₂.absNorm : ℝ)))/3+
      max (1/4-(Real.logb Z (C₁.absNorm : ℝ)+
        min (Real.logb Z (C₂.absNorm : ℝ)) (Real.logb Z (D₂.absNorm : ℝ)))) 0 ≥ 1/6 := by
    have hleft := le_max_left (1/4-(Real.logb Z (C₁.absNorm : ℝ)+
      min (Real.logb Z (C₂.absNorm : ℝ)) (Real.logb Z (D₂.absNorm : ℝ)))) (0 : ℝ)
    have hright := le_max_right (1/4-(Real.logb Z (C₁.absNorm : ℝ)+
      min (Real.logb Z (C₂.absNorm : ℝ)) (Real.logb Z (D₂.absNorm : ℝ)))) (0 : ℝ)
    linarith
  linarith

open CenteredMomentFirstExceptionalChildPaid CenteredMomentFirstExceptionalPaidScales
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonAllocationSum

/-- The error-child reserve retains the actual twice-extracted source
and its true surviving plain scales. -/
theorem actual_local_exceptional_error_child {ι : Type*} [Fintype ι]
    (Z A : ℝ) (hZ : 1 < Z) (hA : A ≤ 883/1000) (branch : Branch Z)
    (hσ : branch.σ ≤ 9/500) (s : Input ι) (R : Ideal O)
    (B : actualAllocations s.pools (commonPart branch.I branch.J)) (τ : Character) (t : ℝ)
    (Q : Ideal O) (hQ : Q ≠ 0) (k : ℕ)
    (Bp : actualAllocations (child s (commonPart branch.I branch.J) R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) (hw : branch.w = (k : ℝ)*Real.logb Z (Q.absNorm : ℝ))
    (hX₁ : Z^(1/4 : ℝ) ≤ s.X₁) (hX₂ : Z^(1/4 : ℝ) ≤ s.X₂)
    (hY₁ : Z^(1/4 : ℝ) ≤ s.Y₁) (hY₂ : Z^(1/4 : ℝ) ≤ s.Y₂) :
    A-5/6-saving branch-2*max (inputCap Z
      (twiceChild s (commonPart branch.I branch.J) R B τ t Q k Bp υ v)) 0/3 ≤
      -63/1000+5*frequencyLoss Z branch.Csec branch.ξ/6 := by
  have hb := error_child_stage Z A 1 hZ branch s R B τ t Q hQ k Bp υ v hw hX₁ hX₂ hY₁ hY₂
  dsimp only [loss] at hb
  linarith

#print axioms actual_enlarged_first_saving
#print axioms actual_local_exceptional_stage
#print axioms actual_local_exceptional_error_child
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointExceptionalLedger -/

/- BEGIN ORIGINAL MODULE Analytic.JointHighPopulation ; sha256 b81088fc92b27dc1bfe7483328e022b4daaaf2fb4937ec7bace3bab04b3537f5 -/
section



/-! The actual joint arithmetic population composed with the established raw
moment-dictionary density, with no density or fiber estimate as a premise. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeInverseAmplification CanonicalQuadraticSieve
open IdealMobiusDivisorSum LocalMoment ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem joint_polynomial_loss_bound (Z B P W ρ loss : ℝ)
    (hZ : 1 ≤ Z) (hB : 0 ≤ B) (hP : P ≤ B) (hW : W ≤ B) (hloss : 0 < loss) :
    let t := loss / (16*(B+1))
    Z^P * (Z^B)^t * (Z^B)^t * (Z^B)^t * (Z^B)^t *
      (Z^P*Z^W)^(5*t) * (Z^W)^(ρ+t) ≤ Z^(ρ*W+P+loss) := by
  dsimp only
  let t := loss / (16*(B+1))
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have ht : 0 < t := by dsimp [t]; positivity
  have htbudget : t*(16*(B+1)) = loss := by
    dsimp [t]
    exact div_mul_cancel₀ loss (by positivity)
  have htP := mul_le_mul_of_nonneg_left hP ht.le
  have htW := mul_le_mul_of_nonneg_left hW ht.le
  have hbudget : t*(4*B+5*P+6*W) ≤ loss := by nlinarith
  change Z^P * (Z^B)^t * (Z^B)^t * (Z^B)^t * (Z^B)^t *
    (Z^P*Z^W)^(5*t) * (Z^W)^(ρ+t) ≤ _
  calc
    _ = Z^(ρ*W+P+t*(4*B+5*P+6*W)) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hZpos.le _) (Real.rpow_nonneg hZpos.le _)]
      simp only [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

section FixedDensityData
variable {Label : Type*} [Fintype Label]
variable (η : Label → Character) (Q : Ideal O) [NeZero Q]
  (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
  (hQη : ∀ label, Q ≤ (η label).modulus)
  (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
  (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
  (hH : RayOrthogonality.globalUnits M ≤ H) (S₀ : Finset (Ideal O))
  (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
  (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
  (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
  (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
  (hβupper : HeckeZeroSupremum.beta ≤ 7/8)
include hQtop hQ72 hQη hβ hH S₀ hφ hφc hφp hφ0 hφne ha₀ hab₀ hB₀ hφs hφB hβupper

/-- Uniform all-radius joint high-bin population. The sole zero-bin premise
is on the actual reconstructed row. The first labels and first projector are
inside this count; the second projector does not occur. -/
theorem actual_joint_population_density (a ε loss : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hloss : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧
      ∀ (p : DensityWindow) (u : Oˣ) (S : Finset JointReconstructionLabel),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, ∃ hw : v.row u ≠ 0, rawZeroBin (fun j => momentData (η j))
        p.lower p.upper p.height ⟨v.row u, hw⟩) →
      ∀ X₁ Y₁ X₂ Y₂ Yw Yr : ℝ,
      0 < X₁ → 0 < Y₁ → 0 < X₂ → 0 < Y₂ → 0 < Yw → 0 ≤ Yr →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ X₁ ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Y₁ ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ X₂ ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Y₂) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {v.row u}) : ℝ) ≤ Yw) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (v.row u)) : ℝ) ≤ Yr) →
      (S.card : ℝ) ≤ K * (1+|p.height|)^A * Yr * X₁^a * Y₁^a * X₂^a * Y₂^a *
        (Yr*Yw)^(5*ε) * Yw^(unmarkedDensity (2*p.lower-1)+loss) := by
  obtain ⟨A, C, hC, _, hraw⟩ := actual_momentData_density η Q hQtop hQ72 hQη hβ
    M H hH S₀ φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
    hβupper loss hloss
  obtain ⟨K, hK, hpop⟩ := joint_population_count a ε ha hε
  refine ⟨A, K*C, mul_pos hK hC, ?_⟩
  intro p u S hsup heq hproj hbin X₁ Y₁ X₂ Y₂ Yw Yr hX₁ hY₁ hX₂ hY₂ hYw hYr hnorm hNw hNr
  let W : Finset ProbePhysical.NonzeroFrequency := S.attach.image
    (fun v => ⟨v.val.row u, (hbin v.val v.property).choose⟩)
  have hWd : (W.card : ℝ) ≤ C*(1+|p.height|)^A*Yw^(unmarkedDensity (2*p.lower-1)+loss) := by
    apply hraw p Yw hYw W
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨hNw v.val v.property, (hbin v.val v.property).choose_spec⟩
  have hW0 : ∀ w ∈ W.image Subtype.val, w ≠ 0 := by
    intro w hw
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    exact w'.property
  have hWS : ∀ v ∈ S, v.row u ∈ W.image Subtype.val := by
    intro v hv
    apply Finset.mem_image.mpr
    refine ⟨⟨v.row u, (hbin v hv).choose⟩, ?_, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_attach _ _, rfl⟩
  have hWN : ∀ w ∈ W.image Subtype.val, (Ideal.absNorm (Ideal.span {w}) : ℝ) ≤ Yw := by
    intro w hw
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw'
    exact hNw v.val v.property
  have hp := hpop u (W.image Subtype.val) S hW0 hsup heq hproj hWS
    X₁ Y₁ X₂ Y₂ Yw Yr hX₁ hY₁ hX₂ hY₂ hYw.le hYr hnorm hWN hNr
  rw [Finset.card_image_of_injective W Subtype.val_injective] at hp
  calc
    (S.card : ℝ) ≤ K * W.card * Yr * X₁^a * Y₁^a * X₂^a * Y₂^a * (Yr*Yw)^(5*ε) := hp
    _ ≤ K * (C*(1+|p.height|)^A*Yw^(unmarkedDensity (2*p.lower-1)+loss)) *
        Yr * X₁^a * Y₁^a * X₂^a * Y₂^a * (Yr*Yw)^(5*ε) := by gcongr
    _ = _ := by ring

/-- Polynomial-scale form of the actual joint high-bin population. The common
range bound B is fixed before all live exponents. Nonnegative P,W retain
literal caps at least one, including the bounded endpoint Z=1. -/
theorem actual_joint_population_polynomial (B loss : ℝ) (hB : 0 ≤ B) (hloss : 0 < loss) :
    ∃ (A : ℕ) (K : ℝ), 0 < K ∧
      ∀ (Z P W : ℝ), 1 ≤ Z → 0 ≤ P → P ≤ B → 0 ≤ W → W ≤ B →
      ∀ (p : DensityWindow) (u : Oˣ) (S : Finset JointReconstructionLabel),
      (∀ v ∈ S, Supported v.C₁ ∧ Supported v.D₁ ∧ Supported v.C₂ ∧ Supported v.D₂) →
      (∀ v ∈ S, primeSupport v.C₁ = primeSupport v.D₁ ∧
        primeSupport v.C₂ = primeSupport v.D₂) →
      (∀ v ∈ S, Squarefree v.L ∧ v.L ∣ v.C₂ ∧ v.L ∣ v.D₂) →
      (∀ v ∈ S, ∃ hw : v.row u ≠ 0, rawZeroBin (fun j => momentData (η j))
        p.lower p.upper p.height ⟨v.row u, hw⟩) →
      (∀ v ∈ S, (Ideal.absNorm v.C₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.D₁ : ℝ) ≤ Z^B ∧
        (Ideal.absNorm v.C₂ : ℝ) ≤ Z^B ∧ (Ideal.absNorm v.D₂ : ℝ) ≤ Z^B) →
      (∀ v ∈ S, (Ideal.absNorm (Ideal.span {v.row u}) : ℝ) ≤ Z^W) →
      (∀ v ∈ S, (Ideal.absNorm (jointMissingRadical v.C₁ (v.row u)) : ℝ) ≤ Z^P) →
      (S.card : ℝ) ≤ K * (1+|p.height|)^A * Z^(unmarkedDensity (2*p.lower-1)*W+P+loss) := by
  let t := loss / (16*(B+1))
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨A, K, hK, hcount⟩ := actual_joint_population_density η Q hQtop hQ72 hQη hβ
    M H hH S₀ φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB hβupper
    t t t ht ht ht
  refine ⟨A, K, hK, ?_⟩
  intro Z P W hZ _hP0 hP _hW0 hW p u S hsup heq hproj hbin hnorm hNw hNr
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hcap : 0 < Z^B := Real.rpow_pos_of_pos hZpos _
  have hh := hcount p u S hsup heq hproj hbin (Z^B) (Z^B) (Z^B) (Z^B) (Z^W) (Z^P)
    hcap hcap hcap hcap (Real.rpow_pos_of_pos hZpos _) (Real.rpow_nonneg hZpos.le _)
    hnorm hNw hNr
  have hl := joint_polynomial_loss_bound Z B P W (unmarkedDensity (2*p.lower-1))
    loss hZ hB hP hW hloss
  calc
    (S.card : ℝ) ≤ K * (1+|p.height|)^A * Z^P * (Z^B)^t * (Z^B)^t * (Z^B)^t *
        (Z^B)^t * (Z^P*Z^W)^(5*t) * (Z^W)^(unmarkedDensity (2*p.lower-1)+t) := hh
    _ = (K * (1+|p.height|)^A) *
        (Z^P * (Z^B)^t * (Z^B)^t * (Z^B)^t * (Z^B)^t *
          (Z^P*Z^W)^(5*t) * (Z^W)^(unmarkedDensity (2*p.lower-1)+t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)

end FixedDensityData

#print axioms actual_joint_population_density
#print axioms actual_joint_population_polynomial
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointHighPopulation -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighAssembly ; sha256 2321abd6d4648d04174be57458528e49676fae718770b8bda7219dcad8ace02b -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighAssembly.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighAssembly
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyPositiveHighSource Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

omit [Fintype α] [DecidableEq α] in
lemma low_restrict (W:ℝ→ℂ)(bslot a b bΦ Bmask L L' Lslot lo hi Mcap d d' κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hZ:1≤ Z)(hL:L'≤ L)(hd:d≤ d')(hC:0≤ C)
    (h:PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
      Mcap d κ Z η₀ Q degree S C):
    PositiveLowAt (α:=α) M H hH W bslot a b bΦ Bmask L' Lslot lo hi
      Mcap d' κ Z η₀ Q degree S C:=by
  intro T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcap hlow
  have hscale:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    s hQ hs p X₁ X₂ hX₁ hX₂ (hc₁.trans hscale) (hc₂.trans hscale) hcap hlow
  apply hh.trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (by have hh:=diagonalControl_nonneg s.radial.profile;positivity)

theorem actual_high_source_split
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃d L:ℝ,0< d ∧ 0≤ L ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0< Cdiag ∧0< Ctail ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃Ju Jr:ℕ,∃Uu Ur:Finset (ℕ×ℕ),∃Cu Cr:ℝ,0< Cu ∧ 0< Cr ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap d κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 7/10≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cu*(K+1)*diagonalControl s.radial.profile*(sourceControl Uu (p.profile 0)*sourceControl Uu (p.profile 1))^2*
          (1+|t|+height)^Ju*Z^(s.width+ε) ∨
      (Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) ∧
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      2*diagonalControl s.radial.profile*(
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp+
        Cdiag*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^εdiag+
        Ctail*(plainControl inp (p.profile 0) (p.profile 1))^2*
          Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*s.radial.scale*Z^(-saving))+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(sourceControl Ur (p.profile 0)*sourceControl Ur (p.profile 1))^2*
        (1+|t|+height)^Jr*Z^(s.width+ε) :=by
  obtain ⟨du,xiu,Lu,hdu,hxiu,hxiuR,hLu,hustage⟩:=original_unbalanced_from_low (α:=α)
    M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ rho ε Mcap Bmask ha hlo hhi hbΦ hrho hε hM hBmask
  obtain ⟨dr,xir,Lr,hdr,hxir,hxirR,hLr,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hrstage⟩:=
    actual_positive_source_entry (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨min du dr,max Lu Lr,lt_min hdu hdr,?_,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  · exact (show 0≤ Lu by linarith).trans (le_max_left _ _)
  intro degree S
  obtain ⟨Ju,Uu,Cu,hCu,hu⟩:=hustage degree S
  obtain ⟨Jr,Ur,Cr,hCr,hr⟩:=hrstage degree S
  refine ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,?_⟩
  filter_upwards [hu,hr] with Z hzu hzr
  refine ⟨hzu.1,?_⟩
  intro Lslot κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hlu:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lu
    Lslot lo hi Mcap (min du dr) du κ Z η₀ Q degree S K hzu.1.le (le_max_left _ _) (min_le_left _ _) hK hlow
  have hlr:=low_restrict (α:=α) M H hH Wslot bslot a b bΦ Bmask (max Lu Lr) Lr
    Lslot lo hi Mcap (min du dr) dr κ Z η₀ Q degree S K hzu.1.le (le_max_right _ _) (min_le_right _ _) hK hlow
  by_cases hshort:min (length Z X₁) (length Z X₂)≤ s.width/4
  · left
    exact hzu.2 Lslot κ η₀ Q K hK hlu θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs (p.profile 0) (p.profile 1) (p.support 0) (p.support 1)
      X₁ X₂ hX₁ hX₂ hshort hlarge hcap
  · have hfour:=balanced_four_scale_gates Z s.width X₁ X₂ hzu.1 (hrho.trans_le hslo)
      hX₁ hX₂ (le_of_lt (lt_of_not_ge hshort))
    rcases hzr.2 Lslot κ η₀ Q K hK hlr θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
      s hQ hslo hs p X₁ X₂ hX₁ hX₂ hlarge hcap with hzero|hsource
    · left
      rw [hzero]
      have hd:=diagonalControl_nonneg s.radial.profile
      have hz:=zero_lt_one.trans hzu.1
      positivity
    · exact Or.inr ⟨⟨hfour.1,hfour.2.1,hfour.2.2.1,hfour.2.2.2.1⟩,hsource⟩
end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighAssembly

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighAssembly -/
