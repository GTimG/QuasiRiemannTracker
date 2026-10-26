/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainPayment

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentAllocatedRayDictionary
local instance affineParentBranchesSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost

variable {α : Type} [Fintype α] [DecidableEq α]

variable [Cycle63.AffineLedger] in
/-- Raising the degrees of the two inner Mellin heights preserves the branch bounds. -/
theorem affine_main_selected_branches_degree_mono
    (ε ξ Z amp reserve baseHeight CL CH : ℝ)(dl dh dl' dh' : ℕ)(hZ : 1<Z)
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hCL : 0≤CL)(hCH : 0≤CH)(hdl : dl≤dl')(hdh : dh≤dh')
    (hbranches : GeometryAffineMainSelectedBranches ε ξ Z amp reserve baseHeight CL CH dl dh hZ
      reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂) :
    GeometryAffineMainSelectedBranches ε ξ Z amp reserve baseHeight CL CH dl' dh' hZ
      reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂ := by
  intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex selected datum coefficient
  obtain ⟨e,select,hlow,hhigh⟩:=hbranches second t₀ u column hinj alloc hf
  have ht : 1≤1+‖t₀‖ := by linarith [norm_nonneg t₀]
  have hu : 1≤1+‖u‖ := by linarith [norm_nonneg u]
  refine ⟨e,select,hlow.trans ?_,hhigh.trans ?_⟩
  · gcongr
  · gcongr

section Parent
variable (M : Ideal O) [NeZero M]
local instance affineParentBranchesFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

variable [Cycle63.AffineLedger] in
/-- At a parent `s` with puncture `R`, seed one and radial scale `Z^Mrow`, the selected low frequency columns of the
second transform paid by the row 5 of the old region, without presentation of the children, and the HIGH part of the
second transform bounded by `CH` on the canonical selector are the two branches of the parent payment, with the
common union `S` of profile controls, the common height degree `D`, the Mellin degrees `dl` and `dh'`, and the common
constant `KL` of the LOW part. -/
theorem actual_affine_parent_selected_branches
    (W : ℝ→ℂ) (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (Cs : ℝ) (Sp : Finset (ℕ×ℕ)) (degreeAll : ℕ) (Kall : ℝ) (hKall : 0≤Kall)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ)
    (hlow : GeometryAffineLowSelectedSpec (α:=α) M H hH W hβlo g 2
      (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
      (fun _ _ _ _ _=>True) Sp degreeAll Kall η₀ Q hQM hQ72 Z)
    (hZ : 1<Z) (hT : 2<Z^g.τ) (s : Input α) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs Z)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ) (hm : Matches M H hH s η₀ θ w σ freq W 2 Z)
    (R : Ideal O) (Rc Mrow : ℝ) (hR : R≠0) (hRc : Rc≤20) (hRcap : (R.absNorm:ℝ)≤Z^Rc)
    (hMrow : 0≤Mrow) (hMrow1 : Mrow≤1)
    (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+g.μ/16)
    (height mesh : ℝ) (hw : ∀j,0≤w j) (hwL : ∀j,w j≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hmesh : 0≤ mesh) (hwm : ∀j,w j≤ mesh) (hσ : ∀j,σ j∈Set.Icc (33/50:ℝ) (33/50))
    (hheight : 0≤height) (hfreq : ∀j,|freq j|≤height)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
      (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop)
    (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
      Cycle63.AffineLedger.B)
    (hω : 0≤frequencyLoss Z 32 (g.μ/64)+g.μ/8 ∧ frequencyLoss Z 32 (g.μ/64)+g.μ/8≤33*g.μ/128)
    (beta : ℝ) (hbeta : beta=Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))))
    (reflected : Bool) (baseHeight : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ)) (χ₀ : RayCharacter)
    (CH : ℝ) (hCH : 0≤CH) (dh : ℕ)
    (hhigh : GeometryAffineMainCanonicalHighBound M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4)
      reflected s R 1 Mrow (Cycle63.AffineLedger.amp beta) baseHeight key Ψ χ₀ caps.zero₁ caps.zero₂ CH dh)
    (KL : ℝ) (S : Finset (ℕ×ℕ)) (D dl dh' : ℕ)
    (hKL : Kall≤KL) (hSp : Sp⊆S) (hdD : degreeAll≤D) (hdl : degreeAll≤dl) (hdh : dh≤dh') :
    let amp:=Cycle63.AffineLedger.amp beta
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    let low:=geometryAffineLowTarget g (Fintype.card α) amp omega mesh+(1-Mrow)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*(1+|baseHeight|+height)^D
    GeometryAffineMainSelectedBranches g.δ (g.μ/64) Z amp (g.μ/8) baseHeight
      ((KL*control)*Z^low) CH dl dh' hZ reflected s R 1 Mrow key Ψ χ₀ (internalQ Q η₀) fixedBadMask
      caps.zero₁ caps.zero₂ := by
  intro amp omega low control
  have hcell:=Cycle63.AffineLedger.originalCell_mem hzslot
  have hb : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop := by
    rw [hbeta]
    exact Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp := (Cycle63.AffineLedger.amp_pos hb).le
  have homega : |omega|≤4 := by
    rw [abs_of_nonneg hω.1]
    exact hω.2.trans (by linarith [g.μ_cap])
  have htarget:=affine_main_low_target_lower g (Fintype.card α) amp omega mesh hamp0 hω.1 hmesh
  have hampeq : (1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))=amp := by
    simp only [div_one,one_mul,hbeta,amp]
  have hw1 (j : α) : w j≤1 := by
    have hlogs (i : α) : Real.logb Z (s.P i)=w i := by
      rw [hm.scale i]
      exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
    have hsum : (∑i,Real.logb Z (s.P i))=∑i,w i := Finset.sum_congr rfl (fun i _=>hlogs i)
    have hj:=Finset.single_le_sum (fun i _=>hw i) (Finset.mem_univ j)
    have h2:=hzslot.2
    rw [hsum] at h2
    linarith [Cycle63.AffineLedger.slotTop_le_one]
  have hwr (j : α) : w j/31≤1 := by linarith [hw1 j]
  have hnorm1 : Real.logb Z (normValue (1:O))≤g.δ := by
    have h1 : normValue (1:O)=1 := by simp [normValue]
    rw [h1,Real.logb_one]
    exact g.δ_pos.le
  have hside : 0≤geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key :=
    (geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)).le
  have hgen : ∀a : ℝ,a=(1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))→
      GeometryAffineMainCanonicalHighBound M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT (1/4) (9/4)
        reflected s R 1 Mrow a baseHeight key Ψ χ₀ caps.zero₁ caps.zero₂ CH dh→
      GeometryAffineMainSelectedBranches g.δ (g.μ/64) Z a (g.μ/8) baseHeight
        (Kall*(p.control Sp)^2*geometryHighFactor reflected
          (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
          Z^(geometryAffineLowTarget g (Fintype.card α) a omega mesh+(1-Mrow))*
          (1+|baseHeight|+height)^degreeAll) CH degreeAll dh hZ reflected s R 1 Mrow key Ψ χ₀
        (internalQ Q η₀) fixedBadMask caps.zero₁ caps.zero₂ := by
    intro a ha hhigh'
    subst ha
    intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex selected datum coefficient
    have hl:=hlow
    unfold GeometryAffineLowSelectedSpec at hl
    have hb':=hl (Label:=Label) hZ s p caps θ w σ freq hm R 1 Rc Mrow hR squarefree_one hRc hRcap hMrow hMrow1
      hfit trivial height mesh hw hwL hwr hmesh hwm hσ hheight hfreq hT hβhi hzslot haff
      reflected second key baseHeight firstIndex
      (by rw [hampeq]; exact hamp0)
      (by rw [hampeq,abs_of_nonneg hamp0]; linarith [(Cycle63.AffineLedger.amp_bounds hb).2,
        Cycle63.AffineLedger.amplifierCap_le_one])
      homega (by rw [hampeq]; exact htarget) hf hinj (fun _=>one_dvd _) (fun _=>χ₀) fixedBadMask
      fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u
    obtain ⟨hP,hPN,hPNc,hcost⟩:=hb'
    have hh:=hhigh' second t₀ u column hinj alloc hf hP hPN
    refine ⟨g.e,_,?_,hh⟩
    have hc:=hcost (!reflected) 1 (fun _=>1) 0 rfl one_ne_zero ⟨fun _=>isUnit_one,hnorm1⟩
      (fun _ _ _ _=>trivial)
    simpa only [Real.norm_eq_abs,datum,coefficient,firstIndex,mass,geometryMainOrdinaryDatum,
      mainLowSelectedDatum] using hc
  have hbase:=hgen amp hampeq.symm hhigh
  have hx : 1≤1+|baseHeight|+height := by linarith [abs_nonneg baseHeight]
  have hz:=Real.rpow_nonneg (zero_lt_one.trans hZ).le low
  have hrest : 0≤(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*Z^low*
      (1+|baseHeight|+height)^D :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hside) hz) (pow_nonneg (by linarith) _)
  have hlarge : Kall*(p.control Sp)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*Z^low*
        (1+|baseHeight|+height)^degreeAll≤(KL*control)*Z^low := by
    have hmono:=affine_main_branch_control_mono p Sp S Kall
      (geometryHighFactor reflected (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key)
      (1+|baseHeight|+height) Z low degreeAll D hSp hKall hside hx hZ hdD
    refine hmono.trans ?_
    have hKLmul:=mul_le_mul_of_nonneg_right hKL hrest
    calc
      _ = Kall*((p.control S)^2*geometryHighFactor reflected
          (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*Z^low*
          (1+|baseHeight|+height)^D) := by ring
      _ ≤ KL*((p.control S)^2*geometryHighFactor reflected
          (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*Z^low*
          (1+|baseHeight|+height)^D) := hKLmul
      _ = (KL*control)*Z^low := by
        simp only [control]
        ring
  have hCL : 0≤(KL*control)*Z^low := by
    have hKL0 : 0≤KL := hKall.trans hKL
    have hc : 0≤control :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hside) (pow_nonneg (by linarith) _)
    exact mul_nonneg (mul_nonneg hKL0 hc) hz
  exact affine_main_selected_branches_degree_mono g.δ (g.μ/64) Z amp (g.μ/8) baseHeight _ CH degreeAll dh dl dh'
    hZ reflected s R 1 Mrow key Ψ χ₀ (internalQ Q η₀) fixedBadMask caps.zero₁ caps.zero₂ hCL hCH hdl hdh
    (affine_main_selected_branches_mono g.δ (g.μ/64) Z amp (g.μ/8) baseHeight _ CH _ CH degreeAll dh hZ
      reflected s R 1 Mrow key Ψ χ₀ (internalQ Q η₀) fixedBadMask caps.zero₁ caps.zero₂ hlarge le_rfl hbase)

end Parent

end
end OAI.SevenEighths.Cycle63InitialMass
