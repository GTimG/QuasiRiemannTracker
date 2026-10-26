/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Positive seed-one restoration retains the original row keep and puncture. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredPositive
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredChild
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.ForwardFull

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Second
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge CenteredMomentCommonRadialData
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
open IdealMobiusDivisorSum
open CenteredMomentSourceMass CenteredMomentRestrictedSource CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationChildInput CenteredMomentSecondHeightFamily
open QRH.Record1252270103Restoration Record1252270103Source
local notation "O" => ActualEisensteinCubic.O
local notation "coefficient" => QRH.Record1252270103Source.High.CoupledFirst.coefficient
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

theorem pure_seed_one_energy (s : Input ι) (R : Ideal O) (τ : Character) (t : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H) (hΦ : ∀x,0≤(Φ x).re) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s (sourceModifier 1 1 1 (fun _=>1)) R 1) (heightCoeff τ t) Φ H/volume s≤
      2*(squarefreeEnergy τ (fixedBadMask*idealGenerator R) 1 t s.W₁ s.W₂
          (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P s.X₁ s.X₂ keep Φ H+
         squarefreeEnergy τ (fixedBadMask*idealGenerator R) 1 t s.W₁ s.W₂
          (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P s.Y₁ s.Y₂ keep Φ H) := by
  have hv : 0<volume s := mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i))
  rw [source_energy_eq_modified_rows,←tsum_div_const]
  have hn (z : O) : ‖modifiedSourceRow s (sourceModifier 1 1 1 (fun _=>1)) R 1 τ t z‖^2/volume s=
    ‖squarefreePositiveSlotRow τ (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂
      (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.X₁ s.X₂-
     squarefreePositiveSlotRow τ (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂
      (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.Y₁ s.Y₂‖^2 := by
    rw [←CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hv,volume,pure_seed_one_row]
  let u := fun z : O=>if keep z then (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0
  let f := fun z=>squarefreePositiveSlotRow τ (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂
    (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.X₁ s.X₂
  let g := fun z=>squarefreePositiveSlotRow τ (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂
    (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.Y₁ s.Y₂
  have hu (z : O) : 0≤u z := by dsimp [u];split_ifs;exact hΦ _;exact le_rfl
  have he : (∑'z : O,(if keep z then
      ‖modifiedSourceRow s (sourceModifier 1 1 1 (fun _=>1)) R 1 τ t z‖^2*
      (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re else 0)/volume s)=
      ∑'z : O,‖f z-g z‖^2*u z := by
    apply tsum_congr
    intro z
    dsimp only [u,f,g]
    split_ifs
    · rw [mul_div_right_comm,hn]
    · simp
  rw [he]
  apply Real.tsum_le_of_sum_le (fun z=>mul_nonneg (sq_nonneg _) (hu z))
  intro T
  calc
    _ ≤ 2*((∑z∈T,‖f z‖^2*u z)+(∑z∈T,‖g z‖^2*u z)) := by
      rw [←Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro z hz
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f z) (g z)) 2
      have hh : ‖f z-g z‖^2≤2*(‖f z‖^2+‖g z‖^2) := by
        nlinarith [sq_nonneg (‖f z‖-‖g z‖)]
      convert mul_le_mul_of_nonneg_right hh (hu z) using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add
      (squarefree_finite_energy_le τ (fixedBadMask*idealGenerator R) 1 s.W₁ s.W₂
        (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.X₁ s.X₂ keep Φ H hH hΦ T)
      (squarefree_finite_energy_le τ (fixedBadMask*idealGenerator R) 1 s.W₁ s.W₂
        (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.Y₁ s.Y₂ keep Φ H hH hΦ T)) (by norm_num)

/-- The analytic inlet is the earlier ordinary source on all literal shorter
positive scales. Both centered endpoints, every marked slot, keep and R remain
unchanged. The squarefree/hole energy is derived rather than assumed. -/
theorem pure_seed_one_restored_energy (s : Input ι) (R : Ideal O) (τ : Character) (t : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H) (hΦ : ∀x,0≤(Φ x).re)
    (E δ B U : ℝ) (hE : 0≤E) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U)
    (hcut : (restoredPlainBound s)^2*s.X₁*s.X₂≤U^B)
    (hordinary : ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      ((X₁≤s.X₁ ∧ X₂≤s.X₂) ∨ (X₁≤s.Y₁ ∧ X₂≤s.Y₂)) →
      CenteredMomentInductionEnergy.energy τ (fixedBadMask*idealGenerator R) 1 t s.W₁ s.W₂
        s.slots (restoredSlotCoeff s) s.P X₁ X₂ keep Φ H≤E) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s (sourceModifier 1 1 1 (fun _=>1)) R 1) (heightCoeff τ t) Φ H/volume s≤
      4*(holeDeletionMass*((QRH.Record1252270103KernelMass.eulerBound 5 (1/2+δ/(B+1))+
        QRH.Record1252270103KernelMass.eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  have hs₁ : Function.support (s.W₁:ℝ→ℂ)⊆Set.Iic (restoredPlainBound s) :=
    fun x hx=>(show x≤s.b₁ from s.support₁ hx).trans (le_max_left _ _)
  have hs₂ : Function.support (s.W₂:ℝ→ℂ)⊆Set.Iic (restoredPlainBound s) :=
    fun x hx=>(show x≤s.b₂ from s.support₂ hx).trans (le_max_right _ _)
  have hx := forward_energy_transfer τ (fixedBadMask*idealGenerator R) 1 s.W₁ s.W₂
    (restoredPlainBound s) hs₁ hs₂ s.slots (restoredSlotCoeff s) s.P s.P_pos t s.X₁ s.X₂
    s.X₁_pos s.X₂_pos keep Φ H hH hΦ E hE δ B U hδ hB hU hcut
    (fun X₁ X₂ h₁ h₂ hx hy=>hordinary X₁ X₂ h₁ h₂ (Or.inl ⟨hx,hy⟩))
  have hy := forward_energy_transfer τ (fixedBadMask*idealGenerator R) 1 s.W₁ s.W₂
    (restoredPlainBound s) hs₁ hs₂ s.slots (restoredSlotCoeff s) s.P s.P_pos t s.Y₁ s.Y₂
    s.Y₁_pos s.Y₂_pos keep Φ H hH hΦ E hE δ B U hδ hB hU
    (by simpa only [mul_assoc,s.same_product] using hcut)
    (fun X₁ X₂ h₁ h₂ hx hy=>hordinary X₁ X₂ h₁ h₂ (Or.inr ⟨hx,hy⟩))
  apply (pure_seed_one_energy s R τ t keep Φ H hH hΦ).trans
  nlinarith

/-- Both retained squarefree projectors bound every actual nonzero column
valuation by two, so complete forced parts divide L² even for overlapping pools. -/
theorem marked_forced_label_dvd_square (s : Input ι) (A₁ A₂ D K R L : Ideal O)
    (F : Ideal O→ℂ) (hL : Squarefree L)
    (C : forcedLabels L (forcedSource s (Collision.markedSourceModifier A₁ A₂ D K F) R L)) :
    (C:Ideal O)∣L^2 := by
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp C.property
  have hcoeff : coefficient s (Collision.markedSourceModifier A₁ A₂ D K F) R L I≠0 :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2
  have hval := Collision.marked_source_column_valuation_bound (Fintype.piFinset s.pools)
    A₁ A₂ D K F
    (CenteredMomentSourceProfileMass.profileCoefficient R s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 L) I hcoeff
  rw [←he]
  apply forcedPart_dvd_power L I hL 2
  intro Q
  by_cases hp : Prime Q
  · exact hval Q hp
  · change (UniqueFactorizationMonoid.normalizedFactors I).count Q≤2
    rw [Multiset.count_eq_zero.mpr
      (fun hm=>hp (UniqueFactorizationMonoid.prime_of_normalized_factor Q hm))]
    omega

theorem marked_forced_allocation_mass_small_power (ε : ℝ) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀(s : Input ι) (A₁ A₂ D K R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → forcedAllocationMass s (Collision.markedSourceModifier A₁ A₂ D K F) R L≤
        K₀*(L.absNorm:ℝ)^ε := by
  obtain ⟨K₀,hK₀,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/8) (by positivity)
  obtain ⟨D₀,hD₀,halloc⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (Fintype.card (ι⊕Fin 2)) (ε/8) (by positivity)
  refine ⟨(K₀*D₀)^2,by positivity,?_⟩
  intro s A₁ A₂ D K R L F hL
  let mod := Collision.markedSourceModifier (ι:=ι) A₁ A₂ D K F
  let T := forcedLabels L (forcedSource s mod R L)
  have hsub : T⊆idealDivisors (L^2) := by
    intro C hC
    exact (mem_idealDivisors (pow_ne_zero 2 hL.ne_zero)).mpr
      (marked_forced_label_dvd_square s A₁ A₂ D K R L F hL ⟨C,hC⟩)
  have hone : (0:ℝ)≤L.absNorm := Nat.cast_nonneg _
  have hr : (((L.absNorm:ℝ)^2):ℝ)^(ε/8)=(L.absNorm:ℝ)^(ε/4) := by
    rw [←Real.rpow_natCast_mul hone]
    congr 1
    norm_num
    ring
  have hcard : (T.card:ℝ)≤K₀*(L.absNorm:ℝ)^(ε/4) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    apply (hdiv (L^2) (pow_ne_zero 2 hL.ne_zero)).trans_eq
    rw [map_pow,Nat.cast_pow,hr]
  have heach (C : T) : ((actualAllocations s.pools (C:Ideal O)).card:ℝ)≤D₀*(L.absNorm:ℝ)^(ε/4) := by
    have hCd := marked_forced_label_dvd_square s A₁ A₂ D K R L F hL C
    have hnorm : ((C:Ideal O).absNorm:ℝ)≤(L.absNorm:ℝ)^2 := by
      have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (pow_ne_zero 2 hL.ne_zero))) (map_dvd Ideal.absNorm hCd)
      simpa only [map_pow,Nat.cast_pow] using (Nat.cast_le (α:=ℝ)).mpr hh
    apply (halloc (le_refl _) s.pools C (forcedLabel_ne_zero L _ C)).trans
    apply mul_le_mul_of_nonneg_left _ hD₀.le
    exact (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm (by positivity)).trans_eq hr
  have hh : forcedAllocationMass s mod R L≤(T.card:ℝ)^2*(D₀*(L.absNorm:ℝ)^(ε/4))^2 := by
    unfold forcedAllocationMass
    apply le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun C _=>pow_le_pow_left₀ (Nat.cast_nonneg _) (heach C) 2)) (Nat.cast_nonneg _))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    dsimp only [T]
    exact le_of_eq (by ring)
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (sq_nonneg _))
  apply le_of_eq
  have hpow : ((L.absNorm:ℝ)^(ε/4))^4=(L.absNorm:ℝ)^ε := by
    rw [←Real.rpow_mul_natCast hone]
    congr 1
    ring
  calc
    _=(K₀*D₀)^2*((L.absNorm:ℝ)^(ε/4))^4 := by ring
    _=_ := by rw [hpow]

/-- Literal marked-source artificial-divisor payment. The input is the
actual seed-one child source after complete common allocation. -/
theorem marked_corrected_forced_source_bound (ε : ℝ) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀(s : Input ι) (A₁ A₂ D K R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → ∀(τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H E : ℝ),
      0<H → 0≤E → (∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re) →
      (∀C : forcedLabels L (forcedSource s (Collision.markedSourceModifier A₁ A₂ D K F) R L),
        ∀B : actualAllocations s.pools (C:Ideal O),
        childDivisorEnergy s (Collision.markedSourceModifier A₁ A₂ D K F) C R 1 B τ t keep Φ H/
          volume (child s C R B τ t)≤E) →
      sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s (Collision.markedSourceModifier A₁ A₂ D K F) R L) (heightCoeff τ t) Φ H/volume s≤
        K₀*(L.absNorm:ℝ)^ε*(forcedProfileCost s*E)/(L.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hbound⟩ := marked_forced_allocation_mass_small_power (ι:=ι) ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro s A₁ A₂ D K R L F hL τ t keep Φ H E hH hE hΦ hchild
  apply (actual_forced_norm_saving s (Collision.markedSourceModifier A₁ A₂ D K F) R L hL.ne_zero
    τ t keep Φ H E hH hE hΦ hchild).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (hbound s A₁ A₂ D K R L F hL)
    (mul_nonneg (forcedProfileCost_nonneg s) hE)

/-- A genuine row-constant factor transfers through the same completed norm.
Unlike a coefficient projector, this equality requires the actual row identity. -/
theorem source_energy_constant_row (s : Input ι) (f g : Tuple ι→ℂ) (R seed : Ideal O)
    (τ : Character) (t : ℝ) (c : ℂ)
    (hrow : ∀z,modifiedSourceRow s f R seed τ t z=c*modifiedSourceRow s g R seed τ t z)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s f R seed) (heightCoeff τ t) Φ H=
      ‖c‖^2*sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s g R seed) (heightCoeff τ t) Φ H := by
  rw [source_energy_eq_modified_rows,source_energy_eq_modified_rows,←tsum_mul_left]
  apply tsum_congr
  intro z
  rw [hrow]
  split_ifs <;> simp only [norm_mul,mul_pow,mul_zero] <;> ring

theorem frozen_source_energy_marked_factor (s : Input ι) (g : Ideal O→ℂ)
    (A₁ A₂ D R : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R)
    (τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s (fun v=>g (∏i,v (Sum.inl i))*sourceModifier A₁ A₂ D (fun _=>1) v) R 1)
      (heightCoeff τ t) Φ H=
      ‖QRH.Record1252270103TwoIdeal.squarefreeIndicator (A₁*A₂)*ordinaryHoleIndicator A₁ A₂‖^2*
        sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s (fun v=>g (∏i,v (Sum.inl i))*sourceModifier 1 1 1 (fun _=>1) v) R 1)
          (heightCoeff τ t) Φ H :=
  source_energy_constant_row s _ _ R 1 τ t _
    (frozen_source_row_marked_factor s g A₁ A₂ D R hA₁ hA₂ hAR τ t) keep Φ H

theorem frozen_seed_one_energy_le (s : Input ι) (A₁ A₂ D R : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R)
    (τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ)
    (hΦ : ∀x,0≤(Φ x).re) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s (sourceModifier A₁ A₂ D (fun _=>1)) R 1) (heightCoeff τ t) Φ H≤
      sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s (sourceModifier 1 1 1 (fun _=>1)) R 1) (heightCoeff τ t) Φ H := by
  have he := frozen_source_energy_marked_factor s (fun _=>1) A₁ A₂ D R hA₁ hA₂ hAR
    τ t keep Φ H
  simp only [one_mul] at he
  rw [he]
  have hc : ‖QRH.Record1252270103TwoIdeal.squarefreeIndicator (A₁*A₂)*ordinaryHoleIndicator A₁ A₂‖^2≤1 := by
    unfold QRH.Record1252270103TwoIdeal.squarefreeIndicator ordinaryHoleIndicator
    split_ifs <;> norm_num
  apply mul_le_of_le_one_left _ hc
  rw [source_energy_eq_modified_rows]
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hΦ _)
  · exact le_rfl

/-- Frozen A₁,A₂ are paid by their actual puncture before invoking ordinary
restoration. This is the positive seed-one analytic boundary for all slots. -/
theorem frozen_seed_one_restored_energy (s : Input ι) (A₁ A₂ D R : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R) (τ : Character) (t : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) (hH : 0<H) (hΦ : ∀x,0≤(Φ x).re)
    (E δ B U : ℝ) (hE : 0≤E) (hδ : 0<δ) (hB : 0≤B) (hU : 1≤U)
    (hcut : (restoredPlainBound s)^2*s.X₁*s.X₂≤U^B)
    (hordinary : ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      ((X₁≤s.X₁ ∧ X₂≤s.X₂) ∨ (X₁≤s.Y₁ ∧ X₂≤s.Y₂)) →
      CenteredMomentInductionEnergy.energy τ (fixedBadMask*idealGenerator R) 1 t s.W₁ s.W₂
        s.slots (restoredSlotCoeff s) s.P X₁ X₂ keep Φ H≤E) :
    sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
      (coefficient s (sourceModifier A₁ A₂ D (fun _=>1)) R 1) (heightCoeff τ t) Φ H/volume s≤
      4*(holeDeletionMass*((QRH.Record1252270103KernelMass.eulerBound 5 (1/2+δ/(B+1))+
        QRH.Record1252270103KernelMass.eulerBound 432 (1/2+δ/(B+1)))*U^δ))^2*E := by
  have hv : 0≤volume s := le_of_lt (mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=>s.P_pos i)))
  exact (div_le_div_of_nonneg_right
    (frozen_seed_one_energy_le s A₁ A₂ D R hA₁ hA₂ hAR τ t keep Φ H hΦ) hv).trans
      (pure_seed_one_restored_energy s R τ t keep Φ H hH hΦ E δ B U hE hδ hB hU hcut hordinary)

/-- The constants precede every dependent live slot type of cardinality at most N. -/
theorem marked_forced_allocation_mass_uniform (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀(α : Type u) [Fintype α],Fintype.card α≤N →∀(s : Input α) (A₁ A₂ D K R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → forcedAllocationMass s (Collision.markedSourceModifier A₁ A₂ D K F) R L≤
        K₀*(L.absNorm:ℝ)^ε := by
  obtain ⟨K₀,hK₀,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/8) (by positivity)
  obtain ⟨D₀,hD₀,halloc⟩ := CenteredMomentAllocationCost.actualAllocations_uniform_small_power
    (N+2) (ε/8) (by positivity)
  refine ⟨(K₀*D₀)^2,by positivity,?_⟩
  intro α _ hα s A₁ A₂ D K R L F hL
  let mod := Collision.markedSourceModifier (ι:=α) A₁ A₂ D K F
  let T := forcedLabels L (forcedSource s mod R L)
  have hsub : T⊆idealDivisors (L^2) := by
    intro C hC
    exact (mem_idealDivisors (pow_ne_zero 2 hL.ne_zero)).mpr
      (marked_forced_label_dvd_square s A₁ A₂ D K R L F hL ⟨C,hC⟩)
  have hone : (0:ℝ)≤L.absNorm := Nat.cast_nonneg _
  have hr : (((L.absNorm:ℝ)^2):ℝ)^(ε/8)=(L.absNorm:ℝ)^(ε/4) := by
    rw [←Real.rpow_natCast_mul hone]
    congr 1
    norm_num
    ring
  have hcard : (T.card:ℝ)≤K₀*(L.absNorm:ℝ)^(ε/4) := by
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    apply (hdiv (L^2) (pow_ne_zero 2 hL.ne_zero)).trans_eq
    rw [map_pow,Nat.cast_pow,hr]
  have heach (C : T) : ((actualAllocations s.pools (C:Ideal O)).card:ℝ)≤D₀*(L.absNorm:ℝ)^(ε/4) := by
    have hCd := marked_forced_label_dvd_square s A₁ A₂ D K R L F hL C
    have hnorm : ((C:Ideal O).absNorm:ℝ)≤(L.absNorm:ℝ)^2 := by
      have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (pow_ne_zero 2 hL.ne_zero))) (map_dvd Ideal.absNorm hCd)
      simpa only [map_pow,Nat.cast_pow] using (Nat.cast_le (α:=ℝ)).mpr hh
    apply (halloc (by simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right hα 2) s.pools C (forcedLabel_ne_zero L _ C)).trans
    apply mul_le_mul_of_nonneg_left _ hD₀.le
    exact (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm (by positivity)).trans_eq hr
  have hh : forcedAllocationMass s mod R L≤(T.card:ℝ)^2*(D₀*(L.absNorm:ℝ)^(ε/4))^2 := by
    unfold forcedAllocationMass
    apply le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun C _=>pow_le_pow_left₀ (Nat.cast_nonneg _) (heach C) 2)) (Nat.cast_nonneg _))
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    dsimp only [T]
    exact le_of_eq (by ring)
  apply hh.trans
  apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) (sq_nonneg _))
  apply le_of_eq
  have hpow : ((L.absNorm:ℝ)^(ε/4))^4=(L.absNorm:ℝ)^ε := by
    rw [←Real.rpow_mul_natCast hone]
    congr 1
    ring
  calc
    _=(K₀*D₀)^2*((L.absNorm:ℝ)^(ε/4))^4 := by ring
    _=_ := by rw [hpow]


theorem marked_corrected_forced_source_uniform (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀(α : Type u) [Fintype α],Fintype.card α≤N →∀(s : Input α) (A₁ A₂ D K R L : Ideal O) (F : Ideal O→ℂ),
      Squarefree L → ∀(τ : Character) (t : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H E : ℝ),
      0<H → 0≤E → (∀z : O,0≤(Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/H)).re) →
      (∀C : forcedLabels L (forcedSource s (Collision.markedSourceModifier A₁ A₂ D K F) R L),
        ∀B : actualAllocations s.pools (C:Ideal O),
        childDivisorEnergy s (Collision.markedSourceModifier A₁ A₂ D K F) C R 1 B τ t keep Φ H/
          volume (child s C R B τ t)≤E) →
      sourceRestrictedEnergy keep (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s (Collision.markedSourceModifier A₁ A₂ D K F) R L) (heightCoeff τ t) Φ H/volume s≤
        K₀*(L.absNorm:ℝ)^ε*(forcedProfileCost s*E)/(L.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hbound⟩ := marked_forced_allocation_mass_uniform N ε hε
  refine ⟨K₀,hK₀,?_⟩
  intro α _ hα s A₁ A₂ D K R L F hL τ t keep Φ H E hH hE hΦ hchild
  apply (actual_forced_norm_saving s (Collision.markedSourceModifier A₁ A₂ D K F) R L hL.ne_zero
    τ t keep Φ H E hH hE hΦ hchild).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (hbound α hα s A₁ A₂ D K R L F hL)
    (mul_nonneg (forcedProfileCost_nonneg s) hE)


end
end OAI.SevenEighths.Record1252270103Second
#print axioms OAI.SevenEighths.Record1252270103Second.pure_seed_one_energy
#print axioms OAI.SevenEighths.Record1252270103Second.pure_seed_one_restored_energy

#print axioms OAI.SevenEighths.Record1252270103Second.marked_corrected_forced_source_bound

#print axioms OAI.SevenEighths.Record1252270103Second.frozen_seed_one_restored_energy

#print axioms OAI.SevenEighths.Record1252270103Second.marked_corrected_forced_source_uniform
