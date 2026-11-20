/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.FixedCubeGaussProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FixedCubeGauss
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve FourierBridge
open CenteredMomentLattice CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSecondSectorColumns
open CenteredMomentSecondActivePhysicalDictionary CenteredMomentActiveSource
open QRH.Cycle092.SignedCenter
open QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedHeightEnergy MixedCommonHeights MixedCommonRestriction
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def sourceProfile₁ (r : Source ι a b) (ha : 0<a) : ℝ→ℂ :=
  normPowerProfile r.W₁ a b ha r.hs₁ (r.W₁.smooth ⊤) r.t₁

def sourceProfile₂ (r : Source ι a b) (ha : 0<a) : ℝ→ℂ :=
  normPowerProfile r.W₂ a b ha r.hs₂ (r.W₂.smooth ⊤) r.t₂

def shiftedSlotCoefficient (r : Source ι a b) (v : ℝ) : ι→Id→ℂ :=
  fun i=>CenteredMomentCommonMaskEnergy.heightCoefficient (r.ν i) v

def shiftedProfile₁ (r : Source ι a b) (ha : 0<a) (v : ℝ) :=
  ReferencePrimeEnclosure.phaseProfile (sourceProfile₁ r ha) (v/(2*Real.pi))

def shiftedProfile₂ (r : Source ι a b) (ha : 0<a) (v : ℝ) :=
  ReferencePrimeEnclosure.phaseProfile (sourceProfile₂ r ha) (v/(2*Real.pi))

lemma logPhase_zero_height (x : ℝ) : logPhase 0 x=1 := by simp [FourierBridge.logPhase]

lemma phaseProfile_zero (W : ℝ→ℂ) : ReferencePrimeEnclosure.phaseProfile W 0=W := by
  funext x
  simp only [ReferencePrimeEnclosure.phaseProfile,logPhase_zero_height,mul_one]

lemma idealHeight_normPower (v : ℝ) (I : Id) (hI : I≠0) :
    idealHeight v I=(Ideal.absNorm I:ℂ)^(Complex.I*v) := by
  have hn : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh := phase_profile_shift (fun _:ℝ=>(1:ℂ)) 0 v (Ideal.absNorm I:ℝ) hn
  simp only [ReferencePrimeEnclosure.phaseProfile,zero_add,one_mul,logPhase_zero_height] at hh
  change heightPhase (Ideal.absNorm I:ℝ) v=_
  exact hh.symm.trans (logPhase_eq_normPower v _ hn)

lemma fixedRow_unsupported_zero (D : FixedCubeDatum) (I : Id) (hI : ¬Supported I) :
    idealCoeff D.row.χ I=0 := by
  rw [D.row_spec.2.2.2]
  have hh := rowWeight_zero_of_not_supported D.η D.m D.A D.z 0 D.hml D.hm2 I hI
  change (idealCoeff D.η I*CanonicalRowCompletion.idealRowHom (D.m^6*(D.A*D.z)) I)=0
  change (idealCoeff D.η I*CanonicalRowCompletion.idealRowHom (D.m^6*(D.A*D.z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*(0:ℝ))=0 at hh
  simpa only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hh

/-- The actual original column picks up precisely the native common phase
under a common height shift. Its two independent initial profiles are kept. -/
theorem sourceCoefficient_height_shift (r : Source ι a b) (ha : 0<a)
    (G I : Id) (hG : G≠0) (hI : I≠0) (v : ℝ) :
    sourceCoefficient r ha 1 (G*I)*(Ideal.absNorm I:ℂ)^(Complex.I*v)=
      residualPhase (r.X₁*r.X₂) r.d G v*
        projectedColumn r (shiftedSlotCoefficient r v) (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) (G*I) := by
  have hdec : (MixedCommonHeights.instDecidableEqSumFinOfNatNat_submissions : DecidableEq (ι⊕Fin 2))=
      (inferInstance : DecidableEq (ι⊕Fin 2)) := Subsingleton.elim _ _
  have hdecW : (MixedHeightEnergy.instDecidableEqSumFinOfNatNat_submissions : DecidableEq (ι⊕Fin 2))=
      (inferInstance : DecidableEq (ι⊕Fin 2)) := Subsingleton.elim _ _
  have hQ : ∀u∈Fintype.piFinset (sourcePools r),∀j,u j≠0 := by
    intro u hu j
    exact MixedLiteralAllocation.source_pools_nonzero r.pool r.hp r.d r.hd b r.X₁ r.X₂ r.Y₁ r.Y₂
      j _ (Fintype.mem_piFinset.mp hu j)
  have hh := residual_column_height (Fintype.piFinset (sourcePools r)) hQ
    (MixedCommonCoefficient.tupleWeight (punctureProduct r.S r.H)) r.R 1 G hG
    r.ν r.Wslot r.P (sourceProfile₁ r ha) (sourceProfile₂ r ha) 0 0 v
    r.X₁ r.X₂ r.Y₁ r.Y₂ (r.hL.trans_le r.hX₁) (r.hL.trans_le r.hX₂)
    (r.hL.trans_le r.hY₁) (r.hL.trans_le r.hY₂) (r.hpX.trans r.hpY.symm) r.d r.hd I
  rw [phaseProfile_zero,phaseProfile_zero,idealHeight_normPower v I hI] at hh
  unfold sourceCoefficient originalColumn
  rw [hdecW]
  dsimp only [projectedColumn,shiftedSlotCoefficient,shiftedProfile₁,shiftedProfile₂,
    sourceProfile₁,sourceProfile₂,sourcePools,MixedPrincipalAllocations.tuplePools]
  simp only [sourceProfile₁,sourceProfile₂,sourcePools,MixedPrincipalAllocations.tuplePools,zero_add] at hh
  convert hh using 1
  rfl

/-- Exact Fourier-height source projection with the actual original sector.
All allocation bounds can now consume the right-hand native commonMaskedRow. -/
theorem sectorFixedHeight_eq_shifted_common (r : Source ι a b) (ha : 0<a)
    (D : FixedCubeDatum) (G : Id) (hG : Supported G) (L : Id) (v : ℝ) :
    MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P*sectorFixedHeight r ha D G hG L v=
      residualPhase (r.X₁*r.X₂) r.d G v*
        MixedCommonSource.commonMaskedRow D.row.χ r.S r.H r.pool r.d r.hd G r.R L
          (shiftedSlotCoefficient r v) r.Wslot r.P (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v)
          b r.X₁ r.X₂ r.Y₁ r.Y₂ := by
  have hext : sectorFixedHeight r ha D G hG L v=
      ∑I : sectorPool G hG.1 (sourceColumns r),
        (if L∣(I:Id) then sourceCoefficient r ha 1 (G*I) else 0)*heightCoeff D.row.χ v I := by
    unfold sectorFixedHeight
    rw [Finset.sum_coe_sort (sectorPool G hG.1 (Second.Concrete.S0 r ha))
      (fun I:Id=>(if L∣I then sourceCoefficient r ha 1 (G*I) else 0)*heightCoeff D.row.χ v I),
      Finset.sum_coe_sort (sectorPool G hG.1 (sourceColumns r))
      (fun I:Id=>(if L∣I then sourceCoefficient r ha 1 (G*I) else 0)*heightCoeff D.row.χ v I)]
    apply sector_sum_active G hG.1 (sourceColumns r) (sourceCoefficient r ha 1)
    intro I hzero
    rw [hzero]
    simp only [ite_self,zero_mul]
  rw [hext]
  have he (I : sectorPool G hG.1 (sourceColumns r)) :
      (if L∣(I:Id) then sourceCoefficient r ha 1 (G*I) else 0)*heightCoeff D.row.χ v I=
      residualPhase (r.X₁*r.X₂) r.d G v*
        ((if L∣(I:Id) then projectedColumn r (shiftedSlotCoefficient r v)
          (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v) (G*I) else 0)*idealCoeff D.row.χ I) := by
    by_cases hL : L∣(I:Id)
    · simp only [hL,ite_true,heightCoeff]
      have hh := congrArg (fun z:ℂ=>z*idealCoeff D.row.χ I)
        (sourceCoefficient_height_shift r ha G I hG.1 (sectorPool_supported G hG.1 _ I).1 v)
      convert hh using 1 <;> ring
    · simp only [hL,ite_false,zero_mul,mul_zero]
  simp_rw [he]
  rw [←Finset.mul_sum]
  rw [mul_left_comm]
  congr 1
  exact sector_projectedColumn_eq_commonMaskedRow r D.row.χ (fixedRow_unsupported_zero D)
    G hG L (shiftedSlotCoefficient r v) (shiftedProfile₁ r ha v) (shiftedProfile₂ r ha v)

#print axioms sourceCoefficient_height_shift
#print axioms sectorFixedHeight_eq_shifted_common
end
end QRH.Cycle092.FixedCubeGauss
