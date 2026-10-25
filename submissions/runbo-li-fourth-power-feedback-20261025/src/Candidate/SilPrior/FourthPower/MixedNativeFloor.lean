/- Copyright (c) 2026 Sil. Apache-2.0.
The actual non-fixed-inducing physical source at the total-width floor.
This uses the checked native punctured chain, not the strict mixed gate.
The source record, complete common/divisor masks and original volume
normalization are identified before applying that chain.

-/
import Candidate.SilPrior.FourthPower.MixedCanonicalEnvelope
import Candidate.SilPrior.FourthPower.MixedFirstActualNonexceptional
import Candidate.SilPrior.FourthPower.MixedFirstProfileEnvelope
import Candidate.SilPrior.FourthPower.IncumbentInput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedNativeFloor
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CompletedGauss RayFourExpansion ConcretePrimeRowBridge CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open ReferencePrimeEnclosure MixedCompletedRows MixedCanonicalSource MixedHeightEnergy
open MixedHeightEnvelope MixedRawEnvelope MixedCanonicalEnvelope MixedSourceAssembly
open MixedLiveNormalization MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedPrincipalHeights MixedInnerExceptionalBlock MixedFirstProfileEnvelope
open MixedFirstActualNonexceptional
open CenteredMomentEnergyState CenteredMomentEnergyChildState
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentFirstSectors CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSourceRow
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentCanonicalFirst
open CenteredMomentLattice HeckeDyadic
open CenteredMomentRowNorm CenteredMomentExceptionalWholeWindow
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open NativeInjectiveEnergy MixedLiteralAllocation
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The consumer's normalized sector row is exactly the restricted
residual-column energy divided by the ORIGINAL source volume. No seed
divisibility or principal/nonprincipal assumption is used in this identity. -/
theorem height_energy_exact (s : Source ι a b) (ha : 0<a) (τ : Character)
    (G : Id) (hG : Supported G) (seed D : Id) (v : ℝ) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    radialEnergy (heightRow s ha τ G hG seed D v) keep Φ K=
      sourceRestrictedEnergy keep (residualPool G hG.1 (sourceColumns s))
        (fun I=>if IsCoprime G I ∧ D∣I then sourceCoefficient s ha seed (G*I) else 0)
        (heightCoeff τ v) Φ K/sourceVolume s := by
  have hrow (z : O) :
      heightRow s ha τ G hG seed D v z=normalization (s.X₁*s.X₂) s.P*
        rowPolynomial Finset.univ (sourceGenerator (residualPool G hG.1 (sourceColumns s)))
          (fun I : supportedColumns (residualPool G hG.1 (sourceColumns s))=>
            (if IsCoprime G (I:Id) ∧ D∣(I:Id) then sourceCoefficient s ha seed (G*I) else 0)*
              heightCoeff τ v I) z := by
    unfold heightRow sectorCoefficient
    simp only [mul_assoc,rowPolynomial_factor]
    rw [sector_rowPolynomial (sourceColumns s)
      (fun I=>(if D∣I then sourceCoefficient s ha seed (G*I) else 0)*heightCoeff τ v I) G hG z]
    congr 2
    funext I
    by_cases hc : IsCoprime G (I:Id) <;> by_cases hd : D∣(I:Id) <;> simp [hc,hd]
  rw [funext hrow]
  rw [radial_normalization (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂))
    s.P (fun i=>zero_lt_one.trans_le (s.hP i))]
  rfl

/-- Exact source-profile frequency conversion. All canonical data
precede the source and both ordinary profiles remain unchanged. -/
theorem source_height_units (t V t₁ t₂ : ℝ) :
    sourceHeight t V (t₁/(2*Real.pi)) (t₂/(2*Real.pi))=height t V t₁ t₂ := by
  have hc (x : ℝ) : 2*Real.pi*(x/(2*Real.pi))=x := by field_simp [Real.pi_ne_zero]
  simp only [sourceHeight,height,hc,Real.norm_eq_abs]

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

/-- Actual total-width-floor nonexceptional row. Both conductor and
row-scale caps are numerical facts of the actual canonical physical
child. They produce its NaturalState admissibility internally. Full
R,G,D norms produce the puncture cap, and the native exponent is the
unconditional 3/4 supplied by the original OpenAI theorem.

This theorem pays the non-fixed-inducing side only. Its fixed-inducing,
zero and tail companions are the separate d=0 outer ledger; none is
silently included in this conclusion. -/
theorem uniform_small_width_native
    (Holes : ℕ) (Wslot : ℝ→ℂ)
    (a b L Lslot Lcap Cap BR BH Bnorm Brow Bchar rho ε lo hi : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hCap : 2≤Cap)
    (hCapb : b≤Cap) (hLordinary : L≤Lcap)
    (hBR : 0≤BR) (hBH : 0≤BH) (hBnorm : 0≤Bnorm)
    (hBrow : 0≤Brow) (hBchar : 0≤Bchar) (hε : 0<ε)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)(t₀ V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→(∑i,w i)≤rho→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s→
      (s.R.absNorm:ℝ)≤Z^BR→s.H⊆enclosure (Cap*Z^Lcap)→
      ((∏I∈holes s.H,I).absNorm:ℝ)≤Z^BH→(∀i,∀P∈s.H,P.val∈R₀ i)→
      s.X₁≤Z^L→s.X₂≤Z^L→s.Y₁≤Z^L→s.Y₂≤Z^L→
    ∀(τ : Character)(n : Fin 4→ℤ),1≤dyadicScale (n 1)→
      dyadicScale (n 1)≤Z^Brow→(τ.modulus.absNorm:ℝ)≤Z^Bchar→
    ∀(G : Id)(hG : Supported G)(seed D : Id),seed∣G→Squarefree D→
      (G.absNorm:ℝ)≤Z^Bnorm→(D.absNorm:ℝ)≤Z^Bnorm→∀v : ℝ,
    radialEnergy (heightRow s ha τ G hG seed D v)
      (canonicalRadial τ Q n).keep ballProfile (dyadicScale (n 1))≤
      (C*diagonalControl ballProfile*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
        (height t₀ V s.t₁ s.t₂)^degree*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1)*
          Z^((3/4:ℝ)*rho+ε)/(G.absNorm:ℝ)/pairNorm s.d/(D.absNorm:ℝ))*
        (1+‖v‖)^(2*degree) := by
  obtain ⟨degree,control,hsource⟩ := uniform_canonical_source_envelope (α:=ι) M Hray hHray
    Holes Wslot a b (Brow+Bchar+1) L Lslot Lcap Cap ((BR+Bnorm)+Bnorm+BH) Bnorm ε lo hi (3/4)
    hWs hW ha haUpper hb (by linarith) hLslot hLcap hCap (by positivity) hBnorm
    hCapb hLordinary hε hβ IncumbentInput.native_kappa_bound Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hsource⟩ := hsource η₀ hη₀
  refine ⟨C,hC,hsource.mono ?_⟩
  intro Z hZ
  refine ⟨hZ.1,?_⟩
  intro θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hR₀ hsmall s hcanonical
    hR hH hholes hHR hX₁ hX₂ hY₁ hY₂ τ n hn hncap hτcap G hG seed D hseed hD hNG hND v
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hτ : 0<(τ.modulus.absNorm:ℝ) :=
    zero_lt_one.trans_le (ideal_norm_one_le τ.modulus_ne_bot)
  have hnlog := Real.logb_le_logb_of_le hZ.1 (dyadicScale_pos (n 1)) hncap
  have hτlog := Real.logb_le_logb_of_le hZ.1 hτ hτcap
  rw [Real.logb_rpow hz hZ.1.ne'] at hnlog hτlog
  have hwidth : Real.logb Z (dyadicScale (n 1))+
      Real.logb Z (τ.modulus.absNorm:ℝ)≤Brow+Bchar+1 := by linarith
  have hRG : ((s.R*G).absNorm:ℝ)≤Z^(BR+Bnorm) := by
    rw [map_mul,Nat.cast_mul,Real.rpow_add hz]
    exact mul_le_mul hR hNG (Nat.cast_nonneg _) (Real.rpow_nonneg hz.le _)
  have hmask := radical_union_cap (s.R*G) D (mul_ne_zero s.hR hG.1) hD.ne_zero
    s.H Z (BR+Bnorm) Bnorm BH hz hRG hND hholes
  have hcoeff : originalColumn (enclosure (Cap*Z^Lcap)) s.H
      (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) s.d s.hd s.R seed
      (slotCoefficient (fun i=>relativeCharacter M Hray hHray η₀ (θ i)) R₀ t₀)
      (fun i=>slotProfile Wslot (σ i) (freq i)) (fun i=>Z^(w i))
      (phaseProfile s.W₁ (s.t₁/(2*Real.pi))) (phaseProfile s.W₂ (s.t₂/(2*Real.pi)))
      b s.X₁ s.X₂ s.Y₁ s.Y₂=sourceCoefficient s ha seed := by
    symm
    unfold sourceCoefficient
    rw [norm_power_profile_phase,norm_power_profile_phase]
    rcases hcanonical with ⟨hS,hpool,hν,hWslot,hP⟩
    simp only [hS,hpool,hν,hWslot,hP]
  have hcolumns : finiteColumns (Fintype.piFinset
      (sourcePools (fun i=>supportedPool (primePool M Hray 2 (Z^(w i)))) s.d s.hd b
        s.X₁ s.X₂ s.Y₁ s.Y₂))=sourceColumns s := by
    simp only [sourceColumns,tuplePools,hcanonical.2.1]
  have hvolume : s.X₁*s.X₂*(∏i,Z^(w i))=sourceVolume s := by
    simp only [sourceVolume,hcanonical.2.2.2.2]
  have he:=hZ.2 θ w σ freq t₀ V R₀ hw hwL hσ hσhi hV hfreq hR₀
    BR τ n hn hwidth s.R G seed D s.hR hR hG.1 hseed hD hNG hND s.H hH hmask hHR
    s.W₁ s.W₂ s.hs₁ s.hs₂ (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))
    s.X₁ s.X₂ s.Y₁ s.Y₂ (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) hX₁ hX₂ hY₁ hY₂
    (s.hpX.trans s.hpY.symm) s.d s.hd v
  rw [hcoeff,hcolumns,hvolume,source_height_units] at he
  rw [height_energy_exact s ha τ G hG seed D v]
  have hnorm := div_le_div_of_nonneg_right he (sourceVolume_pos s).le
  let A:=C*diagonalControl ballProfile*(sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^degree*(τ.modulus.absNorm:ℝ)*dyadicScale (n 1)
  have hA : 0≤A := by
    have hd := diagonalControl_nonneg ballProfile
    have hh : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    dsimp only [A]
    positivity
  calc
    _≤(A*Z^((3/4:ℝ)*(∑i,w i)+ε)/(G.absNorm:ℝ)/pairNorm s.d/(D.absNorm:ℝ))*
        (1+‖v‖)^(2*degree) := hnorm.trans_eq (by
      dsimp only [rawBudget,A]
      field_simp [(sourceVolume_pos s).ne',(pairNorm_pos s.hd.1 s.hd.2).ne',
        (zero_lt_one.trans_le (ideal_norm_one_le hG.1)).ne',
        (zero_lt_one.trans_le (ideal_norm_one_le hD.ne_zero)).ne']
      <;> ring)
    _≤_ := by
      have hp := Real.rpow_le_rpow_of_exponent_le hZ.1.le
        (show (3/4:ℝ)*(∑i,w i)+ε≤(3/4:ℝ)*rho+ε by linarith)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) _)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply div_le_div_of_nonneg_right _ (pairNorm_pos s.hd.1 s.hd.2).le
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left hp hA

end
end Candidate.SilPrior.FourthPower.MixedNativeFloor
