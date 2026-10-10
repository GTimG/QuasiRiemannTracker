import Cycle25.Assembly.Weighted.FullWCellInput
import Cycle25.Assembly.Low.Normalizer
import Cycle25.Numerator.PhysicalFront
import Cycle25.Numerator.FullWBound

/-! The final physical source specialization, conditional only on a literal
integrated numerator bound. This file does not assert that remaining bound. -/
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set Complex
namespace OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
open Cycle25ProbeFinalAssembly ProbeHighRowFamily HeckeFamily ProbePhysical ProbeRaySlots
open HeckeInverseAmplification PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

/-- The two remaining Mellin scale factors after integrating w. -/
def weightedSourceSZExponent (a e : ℝ) : ℝ :=
  Cycle25.lx*(1/2-17/50)+a+16*e+17/50-1

def weightedSourceNormalizer {Δ : ℝ} (D : Cycle25.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (Z : ℝ) : ℂ :=
  sourceResidueConstant F.W F.W F.modulus*
    (Probe.principalScalar Finset.univ Z Cycle25.ell
      (slotMass (Cycle25.Numerator.sourcePrimePool F Z)
        (residueWeights (fun _=>F.w) (fun j=>Z^(D.ell j)))) : ℂ)

theorem weighted_source_normalizer_bound {Δ : ℝ}
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,
      weightedSourceNormalizer D F Z≠0 ∧
      ‖(weightedSourceNormalizer D F Z)⁻¹‖ ≤ C*Z^(D.t/8) := by
  exact Cycle25WeightedLowNormalizer.actual_ray_normalizer_inverse F.modulus ⊤ le_top F.S F.exclusions
    1 2 (by norm_num) (by norm_num) D.ell (fun j=>(D.slots_bounds j).1) D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _ y=>(F.bounded y).1) (fun _=>F.nonzero)
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
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
    ∃C : ℝ,0 < C ∧ ∀ᶠZ : ℝ in atTop,∀(η : Character) (rows : Finset FreeRow)
      (a B H C0 Cw : ℝ) (i : ℕ),
      (∀u∈rows,u.val≠1) → (51/100:ℝ) ≤ a → a ≤ 1 → 2 < B → H ≤ (3*i+2:ℕ)*B →
      0 ≤ C0 → 0 ≤ Cw →
      (∀u∈rows,detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
        (3*(i+1:ℕ)*B) < a+2*D.e) →
      let Yp : Fin D.N→ℝ := fun j=>Z^(D.ell j)
      let T := Cycle25.Numerator.sourcePrimePool F Z
      let hT := nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
      (∀q∈Cycle25.Weighted.FullWContour.szRectangle H,
        ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows T hT
          (fun _ y=>(F.w y:ℂ)) Yp F.W (Z^Cycle25.ly)
          (((a+16*D.e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)‖ ≤
          Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
            Z^(Cycle25.weightedTarget-weightedSourceSZExponent a D.e)) →
      ‖Cycle25.Weighted.FullWContour.finiteCentralFullWRows F.S F.exclusions F.maximal η rows T hT
        (fun _ y=>(F.w y:ℂ)) Yp F.W F.W (Z^Cycle25.lx) (Z^Cycle25.ly) Z D.e
        (fun _=>a) (fun _=>H)/weightedSourceNormalizer D F Z‖ ≤
        C*Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
          Z^(Cycle25.weightedTarget+D.t/8) := by
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
    Z^(Cycle25.weightedTarget-weightedSourceSZExponent a D.e)
  have hA : 0 ≤ A := by dsimp[A];positivity
  have hb := hi D.e a B H i D.e_pos D.e_small ha ha' hB hH
    F.S F.exclusions F.maximal F.first η rows hrow
    (Cycle25.Numerator.sourcePrimePool F Z)
    (nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 (fun j=>Z^(D.ell j)))
    (rayCubeFamily F.modulus ⊤ le_top) hbin (fun _ y=>(F.w y:ℂ)) (fun j=>Z^(D.ell j))
    F.W 1 2 (by norm_num) F.complex_support
    (Z^Cycle25.lx) (Z^Cycle25.ly) Z A (by positivity) (by positivity) hZpos hA hg
  rw [div_eq_mul_inv,norm_mul]
  apply (mul_le_mul hb hn.2 (norm_nonneg _) (by positivity)).trans_eq
  dsimp [A]
  rw [←Real.rpow_mul hZpos.le]
  calc
    _ = (Ci*Cn)*Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
        (Z^(Cycle25.lx*(1/2-17/50))*Z^(a+16*D.e+17/50-1)*
        Z^(Cycle25.weightedTarget-weightedSourceSZExponent a D.e)*Z^(D.t/8)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
      congr 2
      unfold weightedSourceSZExponent
      ring


/-- The remaining numerical target on literal reconstructed row integrals.
Unlike FullWCellsAt this has not yet integrated the two external variables. -/
def IntegratedWeightedCellsAt {Δ : ℝ} (D : Cycle25.HighParameters.HighData Δ)
    (F : WeightedSourceData D.toMomentData) (η : Character)
    (Z τ : ℝ) (n : ℕ) (Cw C0 : ℝ) : Prop :=
  ∀idx grid : FreeRow→ℕ,
    let rows := supportedNonfloorRows F.S F.maximal
      (rowBand (Z^(1/100:ℝ)) (Z^(Cycle25.h+D.t))) grid
    (∀u∈rows,idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/D.e⌋₊ ∧
      (51/100:ℝ)+D.e*grid u ≤ 7/8) →
    (∀u∈rows,detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      (3*(idx u+1:ℕ)*Z^τ) < 51/100+D.e*grid u+2*D.e) →
    (∀u∈rows,(51/100:ℝ)+D.e*grid u ≤ detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*idx u:ℕ)*Z^τ)) →
    ∀k∈smallDyadicIndices (Z^(Cycle25.h+D.t)),
    ∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/D.e⌋₊+1),
      let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
      let Yp : Fin D.N→ℝ := fun j=>Z^(D.ell j)
      let T := Cycle25.Numerator.sourcePrimePool F Z
      let hT := nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Yp
      rows'.Nonempty → (1/2:ℝ) < sourceDyadConductor Z D.t k →
      (1/3:ℝ) < 2*(51/100+D.e*j)-1 →
      sourceDyadConductor Z D.t k ≤ Cycle25.h+3*D.t →
      ∀q∈Cycle25.Weighted.FullWContour.szRectangle ((3*i+1:ℕ)*Z^τ),
        ‖Cycle25.Weighted.FullWContour.integratedDyadValue F.S F.exclusions F.maximal η rows' T hT
          (fun _ y=>(F.w y:ℂ)) Yp F.W (Z^Cycle25.ly)
          ((((51/100+D.e*j)+16*D.e:ℝ):ℂ)+q.1*I) ((17/50:ℂ)+q.2*I)‖ ≤
          Cw*C0*(η.modulus.absNorm:ℝ)^(2*D.eps)*
            Z^(Cycle25.weightedTarget-
              weightedSourceSZExponent (51/100+D.e*j) D.e)

/-- The literal integrated estimate closes the exact FullWCellsAt interface.
The constant is independent of the moment constant C0 and is linear in Cw. -/
theorem fullWCellsAt_of_integrated {Δ : ℝ}
    (D : Cycle25.HighParameters.HighData Δ) (F : WeightedSourceData D.toMomentData) :
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
    (rowBand (Z^(1/100:ℝ)) (Z^(Cycle25.h+D.t))) grid
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

end OAI.SevenEighths.Cycle25WeightedHighFinalAssembly
end
