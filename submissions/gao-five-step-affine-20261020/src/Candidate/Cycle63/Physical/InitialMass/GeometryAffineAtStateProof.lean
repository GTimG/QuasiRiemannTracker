/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersFixedSource
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineParentBudget
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineStateComparison
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainUniform
import Candidate.Cycle63.Physical.InitialMass.GeometrySourceNaturalRow

set_option autoImplicit false
set_option maxHeartbeats 800000
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
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentAllocatedRayDictionary CenteredMomentSourceMass CenteredMomentFirstSourceReduction
open CenteredMomentSecondHeightFamily ProbePhysical

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance affineAtStateProofFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The moment at a natural state of width at most one, in the unit of the ledger, for plain profiles with the support
`[1/4, 9/4]`: the generic step at the schedule `g`. For every ledger that deletes its LOW children into the old region, the
state energy is at most the old moment plus a term linear in the given HIGH part of the second transform. -/
theorem actual_geometry_affine_at_state
    (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule) (εaffine bΦ Bmask mesh ε : ℝ) :
    GeometryAffineAtStateStatement (α:=α) M H hH W hW hWs hβlo hβhi g εaffine (1/4) (9/4) bΦ Bmask mesh ε := by
  intro hεaffine hμ hδ hap hap4 hbp hbΦ hBmask hBmask20 hmesh0 hε
  have hμ0 : 0<g.μ := by
    rw [hμ]; exact geometry_loss_unit_pos 1 εaffine one_pos hεaffine
  have hμ1 : g.μ≤1/128 := by
    rw [hμ]; unfold geometryLossUnit
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hξ : 0<geometryLossUnit 1 εaffine/64 := by
    have := geometry_loss_unit_pos 1 εaffine (by norm_num) hεaffine
    positivity
  obtain ⟨Ψ,hΨ,hΨpos,Dred,hDred,hred⟩:=uniform_original_reduction (α:=α) bΦ 2 (1/4) (9/4) 2 (ε/2)
    (geometryLossUnit 1 εaffine/64) 1 hbΦ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by positivity) hξ
  refine ⟨Ψ,hΨ,hΨpos,?_⟩
  intro Led Del hmesh hres hmeshW hmeshY η₀ Q hQM hQ0 hQt hQ72 SH dh
  have hμL : g.μ=geometryLossUnit 1 (128*g.μ) := by
    unfold geometryLossUnit
    rw [show 128*g.μ/128=g.μ by ring]
    refine (min_eq_left (le_min ?_ (le_min ?_ ?_))).symm <;> linarith
  obtain ⟨Cs,hCs,hsources⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW.continuous hWs
  have hcolEv:=eventual_affine_polynomial_caps (α:=α) M H hH W hW.continuous 1 2 (33/50) (33/50) (1/4) (9/4)
    (by norm_num) hWs (by norm_num) (by norm_num) (by norm_num)
  have hrow5 : LowSelectedPaidAt M H hH g 2 (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) (fun _ _ _=>True) lowGeometryExponent
      (fun _ _ _ _ _ _=>True) :=
    lowSelectedPaidAt_of_columns M H hH actual_selected_low_paid_columns_closed g 2 _ (by norm_num) le_rfl le_rfl
  have hgate : LowBinGate lowGeometryExponent 6 := actual_geometry_low_bin_gate.mono (by norm_num)
  have hrow : ∀T : Finset α,∃(Sp : Finset (ℕ×ℕ))(degreeAll : ℕ)(Kall : ℝ),0≤Kall ∧
      ∀ᶠZ : ℝ in atTop,GeometryAffineLowSelectedSpec (α:=T) M H hH W hβlo g 2 (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
        (fun _ _ _ _ _=>True) Sp degreeAll Kall η₀ Q hQM hQ72 Z := by
    intro T
    let k:=actual_affine_low_selected_payment (α:=T) M H hH hgate W hWs hW hβlo g 2 _ (by norm_num) le_rfl hrow5
      Cs hCs (fixedSourcePrincipal fixedBadPrimes Parameters.fixed_bad_primes_prime) 1
      (fixedSourceNaturalRow fixedBadPrimes Parameters.fixed_bad_primes_prime (Finset.Subset.refl _)) 1 one_ne_zero
      η₀ Q hQM hQ0 hQt hQ72
    exact ⟨k.2.1,k.1,k.2.2.2.1,k.2.2.2.2.down.1.le,k.2.2.2.2.down.2.mono (fun _ h=>h.2)⟩
  choose Sp degreeAll Kall hKall hlow using hrow
  choose S D Cm Ch hSH hdh hCm hCh hmass using fun T : Finset α=>actual_affine_parent_mass (α:=α) M H hH T
    fixedBadPrimes (Finset.Subset.refl _) W hW hWs hβlo hβhi g (128*g.μ) mesh Bmask (by positivity) hmesh hmesh0 hμL hδ
    hBmask hBmask20 hmeshW Ψ η₀ Q hQM hQ0 hQt hQ72 Cs hCs (Sp T) (degreeAll T) (Kall T) (hKall T) (hlow T)
    SH dh (ε/2) (by positivity)
  obtain ⟨Cy,Jy,Uy,hCy,hyEv⟩:=affine_state_comparison_energy (α:=α) M H hH W hW hWs hβlo bΦ Bmask ε mesh hbΦ
    hBmask hε hmeshY η₀ Q hQM hQ0 hQt hQ72
  classical
  obtain ⟨Sall,hSall_def⟩ : ∃ X : Finset (ℕ×ℕ),X=(Finset.univ.biUnion S) ∪ Uy ∪ {(0,0)} := ⟨_,rfl⟩
  obtain ⟨Dall,hDall_def⟩ : ∃ d : ℕ,d=max (Finset.univ.sup D) Jy := ⟨_,rfl⟩
  obtain ⟨CM,hCM_def⟩ : ∃ c : ℝ,c=∑ T,Cm T := ⟨_,rfl⟩
  obtain ⟨CH,hCH_def⟩ : ∃ c : ℝ,c=∑ T,Ch T := ⟨_,rfl⟩
  obtain ⟨C0,hC0_def⟩ : ∃ c : ℝ,c=2*CM+4*Dred*Cs^(2*Fintype.card α)+2*Cy+1 := ⟨_,rfl⟩
  have hCM : 0≤CM := by rw [hCM_def]; exact Finset.sum_nonneg (fun T _ => hCm T)
  have hCH : 0≤CH := by rw [hCH_def]; exact Finset.sum_nonneg (fun T _ => hCh T)
  have hCs0 : 0≤Cs := by linarith
  have hC0 : 0<C0 := by rw [hC0_def]; positivity
  have hSall (T : Finset α) : S T⊆Sall := fun x hx => by
    rw [hSall_def]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩))
  have hUy : Uy⊆Sall := fun x hx => by rw [hSall_def]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have h00 : (0,0)∈Sall := by rw [hSall_def]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hDall (T : Finset α) : D T≤Dall := by
    rw [hDall_def]; exact (Finset.le_sup (Finset.mem_univ T)).trans (le_max_left _ _)
  have hJyD : Jy≤Dall := by rw [hDall_def]; exact le_max_right _ _
  refine ⟨Dall,Sall,(hSH ∅).trans (hSall ∅),(hdh ∅).trans (hDall ∅),C0,2*CH/C0,hC0,by positivity,?_⟩
  filter_upwards [hred,Filter.eventually_all.2 hmass,hyEv,hsources,hcolEv] with Z hr hm hy hsrc hcol
  intro hZ hT T θ w σ freq hσ t height hw hwm hheight hfreq state hmod hwidth p X₁ X₂ hX₁ hX₂ hwin hover EH hEH
    s amp hgiven
  obtain ⟨hmatch,hfitw,hslot,hplane,hcell⟩ := affine_state_bundle_data (κ:=T) M H hH W hW.continuous hWs η₀ θ w σ
    freq hσ state p hap t X₁ X₂ hX₁ hX₂ hZ hwin
  have hgatesE := hsrc.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  obtain ⟨caps,-⟩ := actual_affine_low_source_gates (α:=T) M H hH η₀ θ W hW.continuous hWs w σ freq hσ state p t X₁ X₂
    hX₁ hX₂ Cs hZ hw hwin { hgatesE with card := le_rfl }
  have hcols := hcol.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hrow1 : state.rowWidth≤1 := by
    have := state.character_nonneg
    unfold NaturalState.width at hwidth
    linarith
  have hscale : state.radial.scale⁻¹≤Z^(2:ℝ) := by
    rw [state.scale_eq]
    exact (inv_le_one_of_one_le₀ (Real.one_le_rpow hZ.le state.row_nonneg)).trans
      (Real.one_le_rpow hZ.le (by norm_num))
  have hvol : volume s≤Z^(2:ℝ) := by simpa only [show (1:ℝ)+1=2 by norm_num] using hcols.2.2.1
  have hrd := hr.2 T s p caps.profile₁ caps.profile₂ (fun i => by rw [caps.hi]) state.puncture state.radial
    state.radial_support hvol hscale
  rw [← hμ] at hrd
  have hmT := (hm T).2 hZ hT s p caps θ w σ freq hmatch
    (by simpa only [show (2:ℝ)*1+1=3 by norm_num] using hcols.2.2.2.2) state.puncture state.rowWidth
    state.puncture_ne_zero state.puncture_bound state.row_nonneg hrow1
    (by rw [← hμL]; linarith [hμ0.le]) height hw hwm hσ hheight hfreq hslot hplane _ hcell EH hEH hgiven
  rw [← hμL] at hmT
  have hyc := hy.2 T θ w σ freq hσ t height hw hwm hheight hfreq state hmod hwidth p X₁ X₂ hX₁ hX₂ hwin hover
  have hsc : state.radial.scale=Z^state.rowWidth := state.scale_eq
  rw [hsc] at hrd
  have hdg := diagonalControl_nonneg state.radial.profile
  have hh1 : 1≤1+|t|+height := by linarith [abs_nonneg t]
  have hcT : p.control (S T)≤p.control Sall := Cycle63Physical.profile_control_mono p (hSall T)
  have hcU : p.control Uy≤p.control Sall := Cycle63Physical.profile_control_mono p hUy
  have hc0 := p.control_nonneg Sall
  have hcT0 := p.control_nonneg (S T)
  have hcU0 := p.control_nonneg Uy
  have hpowT : (1+|t|+height)^(D T)≤(1+|t|+height)^Dall := pow_le_pow_right₀ hh1 (hDall T)
  have hpowY : (1+|t|+height)^Jy≤(1+|t|+height)^Dall := pow_le_pow_right₀ hh1 hJyD
  have hpow0 : 1≤(1+|t|+height)^Dall := one_le_pow₀ hh1
  have hCmT : Cm T≤CM := by rw [hCM_def]; exact Finset.single_le_sum (fun T _ => hCm T) (Finset.mem_univ T)
  have hChT : Ch T≤CH := by rw [hCH_def]; exact Finset.single_le_sum (fun T _ => hCh T) (Finset.mem_univ T)
  have hXe : Z^(1+ε/2)≤Z^(1+ε) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hYe : Z^(state.rowWidth+3*g.δ-amp+ε/2)≤Z^(state.rowWidth+3*g.δ-amp+ε) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hX0 : 0≤Z^(1+ε) := Real.rpow_nonneg hZ0.le _
  have hY0 : 0≤Z^(state.rowWidth+3*g.δ-amp+ε)*EH := mul_nonneg (Real.rpow_nonneg hZ0.le _) hEH
  -- the plain control of the input
  have hprod : (∏ i, s.M i)≤Cs^(Fintype.card α) := by
    calc (∏ i, s.M i) ≤ ∏ _i : T, Cs :=
          Finset.prod_le_prod₀ (fun i _ => (zero_le_one.trans (s.M_ge_one i))) (fun i _ => caps.controls i)
      _ = Cs^(Fintype.card T) := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ Cs^(Fintype.card α) := pow_le_pow_right₀ (by linarith)
          (Fintype.card_le_of_injective (fun i : T => i.val) Subtype.val_injective)
  have hsn (k : Fin 2) : SchwartzMap.seminorm ℝ 0 0 (p.profile k)≤
      CenteredMomentFiniteProfileExceptional.sourceControl Sall (p.profile k) :=
    Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ ℝ ℂ) (x := p.profile k) h00
  have hpc : CenteredMomentSourceInputTailUniform.plainControl s (p.profile 0) (p.profile 1)≤
      Cs^(Fintype.card α)*p.control Sall := by
    unfold CenteredMomentSourceInputTailUniform.plainControl Profiles.control
    have h0 := hsn 0
    have h1 := hsn 1
    have hn0 := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (p.profile 0)
    have hn1 := apply_nonneg (SchwartzMap.seminorm ℝ 0 0) (p.profile 1)
    have hp0 : 0≤∏ i, s.M i := Finset.prod_nonneg (fun i _ => zero_le_one.trans (s.M_ge_one i))
    have hq0 := CenteredMomentFiniteProfileExceptional.sourceControl_nonneg Sall (p.profile 0)
    have hq1 := CenteredMomentFiniteProfileExceptional.sourceControl_nonneg Sall (p.profile 1)
    have hCsN : 0≤Cs^(Fintype.card α) := by positivity
    calc (∏ i, s.M i)*SchwartzMap.seminorm ℝ 0 0 (p.profile 0)*SchwartzMap.seminorm ℝ 0 0 (p.profile 1)
        ≤ Cs^(Fintype.card α)*CenteredMomentFiniteProfileExceptional.sourceControl Sall (p.profile 0)*
            CenteredMomentFiniteProfileExceptional.sourceControl Sall (p.profile 1) := by gcongr
      _ = _ := by ring
  have hpc0 := CenteredMomentSourceInputTailUniform.plainControl_nonneg s (p.profile 0) (p.profile 1)
  have hpc2 : CenteredMomentSourceInputTailUniform.plainControl s (p.profile 0) (p.profile 1)^2≤
      Cs^(2*Fintype.card α)*p.control Sall^2 := by
    calc _ ≤ (Cs^(Fintype.card α)*p.control Sall)^2 := pow_le_pow_left₀ hpc0 hpc 2
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm (Fintype.card α) 2]
  have hrw : Z^state.rowWidth≤Z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hZ.le hrow1
  have hinv : Z^(-1:ℝ)≤Z^(ε/2) := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hplain : Dred*CenteredMomentSourceInputTailUniform.plainControl s (p.profile 0) (p.profile 1)^2*
        Z^state.rowWidth*(Z^(ε/2)+Z^(-1:ℝ))≤
      2*Dred*Cs^(2*Fintype.card α)*p.control Sall^2*(1+|t|+height)^Dall*Z^(1+ε) := by
    have hz2 : Z^(1:ℝ)*Z^(ε/2)=Z^(1+ε/2) := by rw [← Real.rpow_add hZ0]
    have hb : 0≤2*Dred*Cs^(2*Fintype.card α)*p.control Sall^2 := by positivity
    have hzε : 0≤Z^(ε/2) := Real.rpow_nonneg hZ0.le _
    have hzr : 0≤Z^state.rowWidth := Real.rpow_nonneg hZ0.le _
    have h1 : Dred*CenteredMomentSourceInputTailUniform.plainControl s (p.profile 0) (p.profile 1)^2*
          Z^state.rowWidth*(Z^(ε/2)+Z^(-1:ℝ))≤
        Dred*(Cs^(2*Fintype.card α)*p.control Sall^2)*Z^(1:ℝ)*(Z^(ε/2)+Z^(ε/2)) := by gcongr
    have h2 : Dred*(Cs^(2*Fintype.card α)*p.control Sall^2)*Z^(1:ℝ)*(Z^(ε/2)+Z^(ε/2))=
        2*Dred*Cs^(2*Fintype.card α)*p.control Sall^2*Z^(1+ε/2) := by rw [← hz2]; ring
    have h3 : 2*Dred*Cs^(2*Fintype.card α)*p.control Sall^2*Z^(1+ε/2)≤
        2*Dred*Cs^(2*Fintype.card α)*p.control Sall^2*Z^(1+ε) := mul_le_mul_of_nonneg_left hXe hb
    have h4 : 2*Dred*Cs^(2*Fintype.card α)*p.control Sall^2*Z^(1+ε)≤
        2*Dred*Cs^(2*Fintype.card α)*p.control Sall^2*(1+|t|+height)^Dall*Z^(1+ε) :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hb hpow0) hX0
    exact h1.trans (h2.le.trans (h3.trans h4))
  have hmass' : physicalMass s state.puncture 1 fixedBadMask 1 Ψ (Z^state.rowWidth) Z (g.μ/64)/volume s≤
      (CM*Z^(1+ε)+CH*(Z^(state.rowWidth+3*g.δ-amp+ε)*EH))*(p.control Sall^2*(1+|t|+height)^Dall) := by
    refine hmT.trans ?_
    have ha : Cm T*Z^(1+ε/2)≤CM*Z^(1+ε) := mul_le_mul hCmT hXe (Real.rpow_nonneg hZ0.le _) hCM
    have hb : Ch T*Z^(state.rowWidth+3*g.δ-amp+ε/2)*EH≤CH*(Z^(state.rowWidth+3*g.δ-amp+ε)*EH) := by
      have h := mul_le_mul hChT hYe (Real.rpow_nonneg hZ0.le _) hCH
      calc Ch T*Z^(state.rowWidth+3*g.δ-amp+ε/2)*EH ≤ CH*Z^(state.rowWidth+3*g.δ-amp+ε)*EH :=
            mul_le_mul_of_nonneg_right h hEH
        _ = _ := by ring
    have hc : p.control (S T)^2*(1+|s.t|+height)^D T≤p.control Sall^2*(1+|t|+height)^Dall :=
      mul_le_mul (pow_le_pow_left₀ hcT0 hcT 2) hpowT (by positivity) (by positivity)
    have hl0 : 0≤Cm T*Z^(1+ε/2)+Ch T*Z^(state.rowWidth+3*g.δ-amp+ε/2)*EH := by
      have := hCm T; have := hCh T; positivity
    exact mul_le_mul (add_le_add ha hb) hc (by positivity) (by positivity)
  have hY' : CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator state.puncture) 1 s.t s.W₁ s.W₂ s.slots
        s.coefficient s.P s.Y₁ s.Y₂ state.radial.keep state.radial.profile (Z^state.rowWidth)≤
      Cy*diagonalControl state.radial.profile*p.control Sall^2*(1+|t|+height)^Dall*Z^(1+ε) := by
    rw [← hsc]
    refine hyc.trans ?_
    gcongr
  have hgoal := hrd.trans (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hmass' hplain) (by positivity))
    (mul_le_mul_of_nonneg_left hY' (by norm_num)))
  refine le_trans (le_of_eq ?_) (hgoal.trans ?_)
  · rw [hsc]; rfl
  · have hA : 0≤diagonalControl state.radial.profile*p.control Sall^2*(1+|t|+height)^Dall := by positivity
    have hC0' : C0*(2*CH/C0)=2*CH := by field_simp
    calc _ = diagonalControl state.radial.profile*p.control Sall^2*(1+|t|+height)^Dall*
            ((C0-1)*Z^(1+ε)+2*CH*(Z^(state.rowWidth+3*g.δ-amp+ε)*EH)) := by rw [hC0_def]; ring
      _ ≤ diagonalControl state.radial.profile*p.control Sall^2*(1+|t|+height)^Dall*
            (C0*Z^(1+ε)+2*CH*(Z^(state.rowWidth+3*g.δ-amp+ε)*EH)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hX0]) hA
      _ = _ := by
        linear_combination (-(diagonalControl state.radial.profile*p.control Sall^2*(1+|t|+height)^Dall*
          Z^(state.rowWidth+3*g.δ-amp+ε)*EH))*hC0'

end
end OAI.SevenEighths.Cycle63InitialMass
