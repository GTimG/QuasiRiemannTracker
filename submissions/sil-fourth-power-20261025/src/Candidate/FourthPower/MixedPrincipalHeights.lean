/- Copyright (c) 2026 Sil. Apache-2.0.
Exact profile conversion and independent-height control for the actual
principal source records. The frozen coefficients shift together with
their live slots; all constants and seminorms refer to the original W.
-/
import Candidate.FourthPower.MixedPrincipalPair
import Candidate.FourthPower.MixedHeightEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalHeights
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentLattice CenteredMomentCommonMaskEnergy CenteredMomentAllocatedNaturalRadial
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstSectors
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open MixedPrincipalPair MixedCommonHeights MixedHeightEnergy MixedOriginalSource
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedDivisorMask
open MixedLiveNormalization ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Equality of the actual functions, including outside their support. -/
theorem norm_power_profile_phase (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (frequency : ℝ) :
    (normPowerProfile W a b ha hs hW frequency : ℝ→ℂ)=phaseProfile W (frequency/(2*Real.pi)) := by
  funext x
  rw [normPowerProfile_apply]
  by_cases hx : W x=0
  · simp only [hx,mul_zero,phaseProfile,zero_mul]
  · rw [phaseProfile,logPhase_eq_normPower frequency x (ha.trans_le (hs hx).1)]
    ring

theorem phase_profile_norm_power (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    phaseProfile W t=(normPowerProfile W a b ha hs hW (2*Real.pi*t) : ℝ→ℂ) := by
  rw [norm_power_profile_phase]
  congr 1
  field_simp [Real.pi_ne_zero]

/-- The uniform coefficient bound also holds at the zero ideal.
Only the equality of norms needs a nonzero ideal. -/
theorem height_coefficient_norm_le (ν : Id→ℂ) (v : ℝ) (I : Id) :
    ‖heightCoefficient ν v I‖≤‖ν I‖ := by
  by_cases hI : I=0
  · subst I
    have hzero : (0:Id).absNorm=0 := Ideal.absNorm_eq_zero_iff.mpr rfl
    rw [heightCoefficient,hzero,Nat.cast_zero]
    by_cases hv : Complex.I*(v:ℂ)=0
    · simp only [hv,Complex.cpow_zero,mul_one,le_refl]
    · rw [Complex.zero_cpow hv,mul_zero,norm_zero]
      exact norm_nonneg _
  · exact (heightCoefficient_norm ν v I hI).le

variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- This shifts the frozen coefficients AND the live coefficients.
The ordinary fields t1,t2 are norm-power frequencies, so they gain v. -/
def shiftSource (s : Source ι a b) (v : ℝ) : Source ι a b :=
  {s with
    ν := fun i=>heightCoefficient (s.ν i) v
    t₁ := s.t₁+v
    t₂ := s.t₂+v
    hν := fun i I=>(height_coefficient_norm_le (s.ν i) v I).trans (s.hν i I)}

theorem shift_admissible (s : Source ι a b) (v : ℝ) (N : ℕ) (Bcap Z : ℝ) :
    (shiftSource s v).Admissible N Bcap Z↔s.Admissible N Bcap Z := Iff.rfl

theorem shift_saving (s : Source ι a b) (v α : ℝ) :
    (shiftSource s v).saving α=s.saving α := rfl

theorem shifted_row (s : Source ι a b) (ha : 0<a) (χ : Character) (D : Id) (v : ℝ) :
    (shiftSource s v).row ha χ D=
      frozenWeight (punctureProduct s.S s.H) s.B*
        (normalization (s.X₁*s.X₂) s.P*
          (frozenCoefficient s.B s.G s.R (fun i=>heightCoefficient (s.ν i) v) s.Wslot s.P*
            maskedLiveSum χ s.S s.H s.pool s.d s.hd s.B s.hB s.G s.R D
              (fun i=>heightCoefficient (s.ν i) v) s.Wslot s.P
              (phaseProfile s.W₁ (s.t₁/(2*Real.pi)+v/(2*Real.pi)))
              (phaseProfile s.W₂ (s.t₂/(2*Real.pi)+v/(2*Real.pi)))
              b s.X₁ s.X₂ s.Y₁ s.Y₂)) := by
  simp only [Source.row,shiftSource,norm_power_profile_phase,add_div]

/-- Exact original-column height identity in the frequency convention
of Source. It retains the original seed and residual phase, before the
genuine common allocation identity removes the seed from live profiles. -/
theorem original_height_row (s : Source ι a b) (ha : 0<a) (χ : Character)
    (seed D : Id) (v : ℝ) :
    normalization (s.X₁*s.X₂) s.P*
      (∑I∈residualPool s.G s.common_nonzero
        (finiteColumns (Fintype.piFinset (sourcePools s.pool s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂))),
        (if IsCoprime s.G I ∧ D∣I then
          originalColumn s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P
            (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
            (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
            b s.X₁ s.X₂ s.Y₁ s.Y₂ (s.G*I) else 0)*idealCoeff χ I*
              (I.absNorm:ℂ)^(Complex.I*v))=
      residualPhase (s.X₁*s.X₂) s.d s.G v*
        originalMaskedRow χ s.S s.H s.pool s.d s.hd s.G s.R seed D s.common_nonzero
          (shiftSource s v).ν s.Wslot s.P
          (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) (shiftSource s v).t₁)
          (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) (shiftSource s v).t₂)
          b s.X₁ s.X₂ s.Y₁ s.Y₂ := by
  have he := original_masked_height_row χ v s.S s.H s.pool s.hp s.d s.hd s.G s.R seed D
    s.common_nonzero s.ν s.Wslot s.P s.W₁ s.W₂ (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))
    b s.X₁ s.X₂ s.Y₁ s.Y₂ (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) (s.hpX.trans s.hpY.symm)
  simpa only [shiftSource,norm_power_profile_phase,add_div] using he

theorem shifted_height_size (frequency₁ frequency₂ v : ℝ) :
    1+‖frequency₁+v‖+‖frequency₂+v‖≤2*(1+‖frequency₁‖+‖frequency₂‖)*(1+‖v‖) := by
  have h₁ := norm_add_le frequency₁ v
  have h₂ := norm_add_le frequency₂ v
  have hfrequency₁ := norm_nonneg frequency₁
  have hfrequency₂ := norm_nonneg frequency₂
  have hv := norm_nonneg v
  nlinarith [mul_nonneg (add_nonneg hfrequency₁ hfrequency₂) hv]

/-- The two original profile seminorms remain identical. No profile
dependent constant is selected after choosing either shifted height. -/
theorem shifted_budget (s : Source ι a b) (v : ℝ) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Z ε : ℝ) (hZ : 0≤Z) :
    (shiftSource s v).budget J control Z ε≤
      (2:ℝ)^J*s.budget J control Z ε*(1+‖v‖)^J := by
  let A := (sourceControl control s.W₁*sourceControl control s.W₂)*Z^ε*
    s.markedCost*Real.sqrt (s.T*∏i,s.P i)/pairNorm s.d/(s.G.absNorm:ℝ)
  have hA : 0≤A := by
    have := sourceControl_nonneg control s.W₁
    have := sourceControl_nonneg control s.W₂
    have h₀ : ∀i,0≤s.M i := fun i=>zero_le_one.trans (s.hM i)
    have h₁ : 0≤∏i : liveIndices s.B,256*s.M i.val :=
      Finset.prod_nonneg (fun (i : liveIndices s.B) _=>mul_nonneg (by norm_num) (h₀ i.val))
    have h₂ : 0≤∏i : liveIndices s.B,s.M i.val :=
      Finset.prod_nonneg (fun (i : liveIndices s.B) _=>h₀ i.val)
    have h₃ : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>h₀ i)
    have hM : 0≤s.markedCost := by unfold Source.markedCost;positivity
    have := pairNorm_pos s.hd.1 s.hd.2
    dsimp only [A]
    positivity
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (shifted_height_size s.t₁ s.t₂ v) J) hA
  calc
    _ = A*(1+‖s.t₁+v‖+‖s.t₂+v‖)^J := by
      dsimp only [Source.budget,shiftSource,Source.markedCost,A]
      ring
    _ ≤ A*(2*(1+‖s.t₁‖+‖s.t₂‖)*(1+‖v‖))^J := hp
    _ = _ := by
      simp only [mul_pow]
      dsimp only [Source.budget,A]
      ring

/-- Actual independent-height pair, with constants selected before the
source profiles, genuine allocations and BOTH height variables. The
numerical conductor and support gates are unchanged by shifting height. -/
theorem uniform_shifted_pair_rows (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧
      ∀(ι₁ ι₂ : Type u) [Fintype ι₁] [Fintype ι₂],
      ∀(s₁ : Source ι₁ a b)(s₂ : Source ι₂ a b),
      ∀Z : ℝ,1≤Z→s₁.Admissible N Bcap Z→s₂.Admissible N Bcap Z→
      ∀(v₁ v₂ : ℝ)(η₁ η₂ : Character)(rows : Finset O)(Ds : Finset Id)(μ : Id→ℂ),
      (∀z∈rows,z≠0)→(∀D∈Ds,Squarefree D)→(∀D∈Ds,‖μ D‖≤1)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound η₁
        (fixedBadMask*idealGenerator ((s₁.R*s₁.G)*D)) 1 z:ℝ)≤Z^Bcap)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound η₂
        (fixedBadMask*idealGenerator ((s₂.R*s₂.G)*D)) 1 (-z):ℝ)≤Z^Bcap)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow η₁ Q fixedBadMask 1 z)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow η₂ Q fixedBadMask 1 (-z))→
      (∑D∈Ds,‖μ D‖*∑z∈rows,
        ‖(shiftSource s₁ v₁).row ha (naturalCharacter η₁ z) D‖*
        ‖(shiftSource s₂ v₂).row ha (naturalCharacter η₂ (-z)) D‖)≤
      (rows.card:ℝ)*(C*(s₁.budget J control Z ε*s₂.budget J control Z ε)*
        min (s₁.saving α) (s₂.saving α))*(1+‖v₁‖)^J*(1+‖v₂‖)^J := by
  obtain ⟨J,control,h00,hpair⟩ := uniform_frozen_masked_pair_rows N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ hgap
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hpair⟩ := hpair Q hQ
  refine ⟨C*((2:ℝ)^J)^2,by positivity,?_⟩
  intro ι₁ ι₂ inst₁ inst₂ s₁ s₂ Z hZ hs₁ hs₂ v₁ v₂ η₁ η₂ rows Ds μ
    hrows hDs hμ hc₁ hc₂ he₁ he₂
  have hp := hpair ι₁ ι₂ (shiftSource s₁ v₁) (shiftSource s₂ v₂) Z hZ hs₁ hs₂
    η₁ η₂ rows Ds μ hrows hDs hμ hc₁ hc₂ he₁ he₂
  rw [shift_saving,shift_saving] at hp
  have hZ0 : 0≤Z := zero_le_one.trans hZ
  have hB₁ := s₁.budget_nonneg J control Z ε hZ0
  have hB₂ := s₂.budget_nonneg J control Z ε hZ0
  have hmin : 0≤min (s₁.saving α) (s₂.saving α) :=
    le_min (s₁.saving_nonneg α) (s₂.saving_nonneg α)
  have hb : (shiftSource s₁ v₁).budget J control Z ε*(shiftSource s₂ v₂).budget J control Z ε≤
      (((2:ℝ)^J)^2*(s₁.budget J control Z ε*s₂.budget J control Z ε))*
        (1+‖v₁‖)^J*(1+‖v₂‖)^J := by
    apply (mul_le_mul (shifted_budget s₁ v₁ J control Z ε hZ0)
      (shifted_budget s₂ v₂ J control Z ε hZ0)
      ((shiftSource s₂ v₂).budget_nonneg J control Z ε hZ0) (by positivity)).trans_eq
    ring
  apply hp.trans
  calc
    _ ≤ (rows.card:ℝ)*(C*((((2:ℝ)^J)^2*
        (s₁.budget J control Z ε*s₂.budget J control Z ε))*(1+‖v₁‖)^J*(1+‖v₂‖)^J)*
        min (s₁.saving α) (s₂.saving α)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hC.le) hmin)
        (Nat.cast_nonneg _)
    _ = _ := by ring

end
end Candidate.FourthPower.MixedPrincipalHeights

