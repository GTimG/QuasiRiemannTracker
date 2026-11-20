/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B000
import Candidate.Bundles.B083
import Candidate.Bundles.B084
import Candidate.Bundles.B085
import Candidate.Bundles.B087
import Candidate.Bundles.B089
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SourceCaps; sha256 01c7379b371ccbc3637745f33e6bf6ce3c626c97d0a397cf1411c5a25279bc31 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                              
                                          
                                             

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentCommonRadialData
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands
open CenteredMomentAmplificationChildSourceCaps Cycle61InitialSource
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O

section Literal
variable {ι : Type*} [Fintype ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance : Finite (O ⧸ rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z bΦ a b : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0 < a)
variable (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂

theorem affine_literal_fields :
    (∀ i, (inp).M i = CenteredMomentEnergyNaturalInputMatches.profileBound
      W hW aslot bslot lo hi haslot hWs) ∧
    (inp).upper = bslot ∧ (∀ i, (inp).hi i = bslot) ∧
    (inp).b₁ = b ∧ (inp).b₂ = b ∧ (inp).W₁ = p.profile 0 ∧ (inp).W₂ = p.profile 1 ∧
    (∀ i, (inp).P i = Z^(w i)) ∧ (inp).η = state.character ∧ (inp).m = state.mask ∧
    (inp).t = t ∧
    CenteredMomentAllocatedRayDictionary.Matches rayM H hH inp η₀ θ w σ freq W bslot Z := by
  refine ⟨fun _ => rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, rfl, rfl, rfl, ?_⟩
  constructor <;> intros <;> rfl

theorem affine_endpoints (hbslot : 0 ≤ bslot) (hb : 0 ≤ b) :
    Endpoints (max 1 bslot) b b inp := by
  exact ⟨le_max_right _ _, fun _ => hbslot, hb, le_rfl, hb, le_rfl⟩

/-- The comparison rectangle is bounded from its actual equal-product formula. -/
theorem affine_plain_caps (Mmax : ℝ) (hZ : 1 < Z) (hM : 0 ≤ M) (hmax : M ≤ Mmax)
    (hn₁ : length Z X₁ ≤ (44/100)*M) (hn₂ : length Z X₂ ≤ (44/100)*M) :
    ∀ second j, Cycle61.Physical.sourcePlainScales (inp).toData.toSource second j ≤ Z^Mmax := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hx (X : ℝ) : X ≤ Z^(length Z X) := by
    rw [length, Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hx₁ : X₁ ≤ Z^((44/100)*M) := (hx X₁).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hn₁)
  have hx₂ : X₂ ≤ Z^((44/100)*M) := (hx X₂).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hn₂)
  have hfirst : comparisonFirst Z M ≤ Z^Mmax := by
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hprod : X₁*X₂ ≤ Z^((44/100)*M+(44/100)*M) := by
    rw [Real.rpow_add hz]
    exact mul_le_mul hx₁ hx₂ hX₂.le (Real.rpow_nonneg hz.le _)
  have hsecond : comparisonSecond Z M X₁ X₂ ≤ Z^Mmax := by
    unfold comparisonSecond comparisonFirst
    calc
      _ ≤ Z^((44/100)*M+(44/100)*M)/Z^(M/4) :=
        div_le_div_of_nonneg_right hprod (Real.rpow_nonneg hz.le _)
      _ = Z^((44/100)*M+(44/100)*M-M/4) := (Real.rpow_sub hz _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have h₁ : X₁ ≤ Z^Mmax := hx₁.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have h₂ : X₂ ≤ Z^Mmax := hx₂.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  intro second j
  cases second <;> fin_cases j
  · exact h₁
  · exact h₂
  · exact hfirst
  · exact hsecond
end Literal

/-- The fixed caps precede every live slot subset and all source parameters. -/
theorem fixed_affine_source_caps {α : Type*} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi a b : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hbslot : 0 ≤ bslot) (ha : 0 < a) (hb : 1 ≤ b) :
    ∃ Cs bs bp : ℝ, 1 ≤ Cs ∧ 1 ≤ bs ∧ 1 ≤ bp ∧
    ∀ (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
      {Z bΦ : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b)
      (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
    let inp := affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂
    Fintype.card T ≤ Fintype.card α ∧ (∀ i, (inp).M i ≤ Cs) ∧ (inp).upper ≤ bs ∧
    Endpoints bs bp bp inp ∧ (inp).b₁ = bp ∧ (inp).b₂ = bp ∧
    (inp).W₁ = p.profile 0 ∧ (inp).W₂ = p.profile 1 ∧ (inp).η = state.character ∧
    CenteredMomentAllocatedRayDictionary.Matches rayM H hH inp η₀ θ w σ freq W bslot Z := by
  let Cs := CenteredMomentEnergyNaturalInputMatches.profileBound
    W hW aslot bslot lo hi haslot hWs
  refine ⟨Cs, max 1 bslot, b,
    CenteredMomentEnergyNaturalInputMatches.profileBound_ge_one
      W hW aslot bslot lo hi haslot hWs, le_max_left _ _, hb, ?_⟩
  intro T η₀ θ w σ freq hσ Z bΦ state p M t X₁ X₂ hX₁ hX₂
  refine ⟨Fintype.card_le_of_injective (fun i : T => i.val) Subtype.val_injective,
    fun _ => le_rfl, le_max_right _ _, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · exact affine_endpoints rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ hbslot (zero_le_one.trans hb)
  · constructor <;> intros <;> rfl

#print axioms affine_literal_fields
#print axioms affine_endpoints
#print axioms affine_plain_caps
#print axioms fixed_affine_source_caps
end
end OAI.SevenEighths.Cycle61InitialMass

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SourceCaps -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineCaps; sha256 58875907b9a8f02fe921adc187f599d87a99fe5b0eb7f0a7de01781cc3565249 -/
section
                                              
                                                     
                                                             

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSourceRectangle CenteredMomentAddedZeroUniform
open CenteredMomentEnergyInputParentCapacity Cycle61InitialSource
local notation "O" => HeckeFamily.O
local instance geometryAffineCapsDecidableEq {α : Type*} : DecidableEq α := Classical.decEq _

private theorem plain_pool_norm_le (b X Y L : ℝ) (hb : 0 ≤ b)
    (hX : X ≤ L) (hY : Y ≤ L) (I : Ideal O)
    (hI : I ∈ plainSupportPool b X Y) : (I.absNorm : ℝ) ≤ b*L := by
  rcases Finset.mem_union.mp hI with hx | hy
  · exact ((mem_idealBall _ _).mp hx).2.trans (mul_le_mul_of_nonneg_left hX hb)
  · exact ((mem_idealBall _ _).mp hy).2.trans (mul_le_mul_of_nonneg_left hY hb)

/-- Multiplying the actual slot cutoffs retains their total width, including
all stored columns at which the smooth coefficient vanishes. -/
theorem weighted_padded_columns_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Input ι) (w : ι → ℝ) (N : ℕ) (Z bs bp e₁ e₂ : ℝ)
    (hN : Fintype.card ι ≤ N) (hZ : 0 < Z) (hbs : 1 ≤ bs) (hbp : 0 ≤ bp)
    (hslot : ∀ i I, I ∈ s.slots i → (I.absNorm : ℝ) ≤ bs*Z^(w i))
    (hp₁ : ∀ I ∈ s.plain₁, (I.absNorm : ℝ) ≤ bp*Z^e₁)
    (hp₂ : ∀ I ∈ s.plain₂, (I.absNorm : ℝ) ≤ bp*Z^e₂) :
    ∀ I ∈ finiteColumns (Fintype.piFinset s.pools),
      (I.absNorm : ℝ) ≤ bs^N*bp^2*Z^((∑ i, w i)+e₁+e₂) := by
  intro I hI
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hI
  have hv' := Fintype.mem_piFinset.mp hv
  have hslots : (∏ i : ι, ((v (Sum.inl i)).absNorm : ℝ)) ≤ bs^N*Z^(∑ i, w i) := by
    calc
      _ ≤ ∏ i : ι, bs*Z^(w i) := Finset.prod_le_prod₀
        (fun _ _ => Nat.cast_nonneg _) (fun i _ => hslot i _ (hv' (Sum.inl i)))
      _ = bs^Fintype.card ι*Z^(∑ i, w i) := by
        rw [Finset.prod_mul_distrib]
        simp only [Finset.prod_const, Finset.card_univ]
        rw [Real.rpow_sum_of_pos hZ]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hbs hN)
        (Real.rpow_nonneg hZ.le _)
  have h₁ := hp₁ _ (hv' (Sum.inr 0))
  have h₂ := hp₂ _ (hv' (Sum.inr 1))
  have hnorm : ((finiteTupleProduct v).absNorm : ℝ) =
      (∏ i : ι, ((v (Sum.inl i)).absNorm : ℝ))*
        ((v (Sum.inr 0)).absNorm : ℝ)*((v (Sum.inr 1)).absNorm : ℝ) := by
    simp only [finiteTupleProduct, Fintype.prod_sum_type, Fin.prod_univ_two,
      map_mul, map_prod, Nat.cast_mul, Nat.cast_prod]
    ring
  rw [hnorm]
  calc
    _ ≤ (bs^N*Z^(∑ i, w i))*(bp*Z^e₁)*(bp*Z^e₂) :=
      mul_le_mul (mul_le_mul hslots h₁ (Nat.cast_nonneg _)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hbs) _) (Real.rpow_nonneg hZ.le _)))
        h₂ (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_add hZ, Real.rpow_add hZ]; ring

section Affine
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (rayM : Ideal O) [NeZero rayM]
local instance geometryAffineCapsFiniteQuotient : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
variable (η₀ : Character) (θ : ι → RayQuotient.Characters rayM H)
variable (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi : ℝ)
variable (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
variable (w σ freq : ι → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
variable {Z bΦ a b : ℝ} (state : NaturalState Z 0 bΦ) (p : Profiles a b) (ha : 0 < a)
variable (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
local notation "inp" => affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
  w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂
local notation "V" => CenteredMomentAmplificationChildInput.volume inp

omit [DecidableEq ι] in
theorem affine_volume_log_exact (hZ : 1 < Z) (hM : 0 < M)
    (hlo₁ : (41/100)*M ≤ length Z X₁) (hlo₂ : (41/100)*M ≤ length Z X₂) :
    Real.logb Z V = length Z X₁+length Z X₂+∑ i, w i := by
  rw [input_volume_log]
  have h₁ := initial_scale_exact Z X₁ M hZ hM hlo₁
  have h₂ := initial_scale_exact Z X₂ M hZ hM hlo₂
  change Real.logb Z X₁+Real.logb Z X₂+(∑ i, Real.logb Z (Z^(w i))) = _
  conv_lhs => rw [h₁, h₂]
  simp only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

omit [DecidableEq ι] in
theorem affine_original_volume_caps (Mmax : ℝ) (hZ : 1 < Z) (hM : 0 < M)
    (hmax : M ≤ Mmax) (hw : ∀ i, 0 ≤ w i)
    (hlo₁ : (41/100)*M ≤ length Z X₁) (hlo₂ : (41/100)*M ≤ length Z X₂)
    (hhi₁ : length Z X₁ ≤ (44/100)*M) (hhi₂ : length Z X₂ ≤ (44/100)*M)
    (hslots : (∑ i, w i) ≤ M/25) :
    1 ≤ V ∧ |Real.logb Z V| ≤ (23/25)*Mmax ∧ V ≤ Z^(Mmax+1) := by
  have he := affine_volume_log_exact rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ hZ hM hlo₁ hlo₂
  have hn : 0 ≤ Real.logb Z V := by
    rw [he]
    exact add_nonneg (add_nonneg (length_nonneg Z X₁ hZ) (length_nonneg Z X₂ hZ))
      (Finset.sum_nonneg (fun i _ => hw i))
  have hv : 1 ≤ V := by
    calc
      1 ≤ Z^(Real.logb Z V) := Real.one_le_rpow hZ.le hn
      _ = V := Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
        (CenteredMomentAmplificationChildInput.volume_pos inp)
  refine ⟨hv, ?_, ?_⟩
  · rw [abs_of_nonneg hn, he]
    linarith
  · exact affine_volume_bound Z M Mmax X₁ X₂ w hZ hM.le hmax hX₁ hX₂ hhi₁ hhi₂ hslots

theorem affine_padded_columns_norm (N : ℕ) (hN : Fintype.card ι ≤ N)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hb : 0 ≤ b)
    (hhi₁ : length Z X₁ ≤ (44/100)*M) (hhi₂ : length Z X₂ ≤ (44/100)*M)
    (hslots : (∑ i, w i) ≤ M/25) :
    ∀ I ∈ finiteColumns (Fintype.piFinset (inp).pools),
      (I.absNorm : ℝ) ≤ (max 1 bslot)^N*b^2*Z^((111/100)*M) := by
  have hz := zero_lt_one.trans hZ
  have hx (X : ℝ) : X ≤ Z^(length Z X) := by
    rw [length, Real.rpow_logb hz hZ.ne' (zero_lt_one.trans_le (le_max_left _ _))]
    exact le_max_right _ _
  have hx₁ : X₁ ≤ Z^((44/100)*M) := (hx X₁).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hhi₁)
  have hx₂ : X₂ ≤ Z^((44/100)*M) := (hx X₂).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le hhi₂)
  have hy₁ : comparisonFirst Z M ≤ Z^((44/100)*M) :=
    Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hx₂' : X₂ ≤ Z^((63/100)*M) := hx₂.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hy₂ : comparisonSecond Z M X₁ X₂ ≤ Z^((63/100)*M) := by
    unfold comparisonSecond comparisonFirst
    calc
      _ ≤ (Z^((44/100)*M)*Z^((44/100)*M))/Z^(M/4) :=
        div_le_div_of_nonneg_right (mul_le_mul hx₁ hx₂ hX₂.le
          (Real.rpow_nonneg hz.le _)) (Real.rpow_nonneg hz.le _)
      _ = Z^((44/100)*M+(44/100)*M-M/4) := by
        rw [←Real.rpow_add hz, ←Real.rpow_sub hz]
      _ = _ := by congr 1; ring
  have hslot : ∀ i I, I ∈ (inp).slots i → (I.absNorm : ℝ) ≤ max 1 bslot*Z^(w i) := by
    intro i I hI
    change I ∈ CenteredMomentPrimeSlot.primePool rayM H bslot (Z^(w i)) at hI
    have hp := (Finset.mem_filter.mp hI).1
    exact (Nat.cast_le.mpr (mem_idealsUpTo.mp hp).2).trans
      (Nat.floor_le (by positivity))
  have hp₁ : ∀ I ∈ (inp).plain₁, (I.absNorm : ℝ) ≤ b*Z^((44/100)*M) := by
    intro I hI
    change I ∈ plainSupportPool b X₁ (comparisonFirst Z M) at hI
    exact plain_pool_norm_le b _ _ _ hb hx₁ hy₁ I hI
  have hp₂ : ∀ I ∈ (inp).plain₂, (I.absNorm : ℝ) ≤ b*Z^((63/100)*M) := by
    intro I hI
    change I ∈ plainSupportPool b X₂ (comparisonSecond Z M X₁ X₂) at hI
    exact plain_pool_norm_le b _ _ _ hb hx₂' hy₂ I hI
  intro I hI
  have hh := weighted_padded_columns_norm inp w N Z (max 1 bslot) b
    ((44/100)*M) ((63/100)*M) hN hz (le_max_left _ _) hb hslot hp₁ hp₂ I hI
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
    (by positivity)

theorem affine_polynomial_source_caps (N : ℕ) (Mmax : ℝ) (hN : Fintype.card ι ≤ N)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hmax : M ≤ Mmax) (hbslot : 0 ≤ bslot) (hb : 1 ≤ b)
    (hfactor : (max 1 bslot)^N*b^2 ≤ Z)
    (hhi₁ : length Z X₁ ≤ (44/100)*M) (hhi₂ : length Z X₂ ≤ (44/100)*M)
    (hslots : (∑ i, w i) ≤ M/25) :
    V ≤ Z^(Mmax+1) ∧ sourceRadius inp ≤ Z^(Mmax+2) ∧
      ∀ I ∈ finiteColumns (Fintype.piFinset (inp).pools),
        (I.absNorm : ℝ) ≤ Z^(2*Mmax+1) := by
  have hz := zero_lt_one.trans hZ
  have hv : V ≤ Z^(Mmax+1) :=
    affine_volume_bound Z M Mmax X₁ X₂ w hZ hM hmax hX₁ hX₂ hhi₁ hhi₂ hslots
  have he := affine_endpoints rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ hbslot (zero_le_one.trans hb)
  have hr := (radius_bound N (max 1 bslot) b b (le_max_left _ _) hb hb inp hN he).2
  have hfactor' : (max 1 bslot)^N*b*b ≤ Z := by simpa [pow_two, mul_assoc] using hfactor
  refine ⟨hv, ?_, ?_⟩
  · calc
      _ ≤ ((max 1 bslot)^N*b*b)*V := hr
      _ ≤ Z*Z^(Mmax+1) := mul_le_mul hfactor' hv
        (CenteredMomentAmplificationChildInput.volume_pos inp).le hz.le
      _ = Z^(1 : ℝ)*Z^(Mmax+1) := by rw [Real.rpow_one]
      _ = Z^(1+(Mmax+1)) := (Real.rpow_add hz _ _).symm
      _ = _ := by congr 1; ring
  · intro I hI
    have hp := affine_padded_columns_norm rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
      w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ N hN hZ hM (zero_le_one.trans hb)
      hhi₁ hhi₂ hslots I hI
    calc
      _ ≤ ((max 1 bslot)^N*b^2)*Z^((111/100)*M) := hp
      _ ≤ Z*Z^((111/100)*M) := mul_le_mul_of_nonneg_right hfactor
        (Real.rpow_nonneg hz.le _)
      _ = Z^(1 : ℝ)*Z^((111/100)*M) := by rw [Real.rpow_one]
      _ = Z^(1+(111/100)*M) := (Real.rpow_add hz _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
end Affine

theorem eventual_affine_endpoint_factor (N : ℕ) (bslot b : ℝ) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ (max 1 bslot)^N*b^2 ≤ Z := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop ((max 1 bslot)^N*b^2)] with Z hZ hfactor
  exact ⟨hZ, hfactor⟩

/-- The exponent caps precede the dictionary size. Only the scale threshold
uses that size and the fixed support endpoints. -/
theorem eventual_affine_polynomial_caps {α : Type*} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O ⧸ rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (hW : Continuous W) (aslot bslot lo hi a b Mmax : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hbslot : 0 ≤ bslot) (ha : 0 < a) (hb : 1 ≤ b) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (T : Finset α) (η₀ : Character) (θ : T → RayQuotient.Characters rayM H)
      (w σ freq : T → ℝ) (hσ : ∀ i, σ i ∈ Set.Icc lo hi)
      (bΦ : ℝ) (state : NaturalState Z 0 bΦ) (p : Profiles a b)
      (M t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      0 < M → M ≤ Mmax → (∀ i, 0 ≤ w i) →
      (41/100)*M ≤ length Z X₁ → (41/100)*M ≤ length Z X₂ →
      length Z X₁ ≤ (44/100)*M → length Z X₂ ≤ (44/100)*M →
      (∑ i, w i) ≤ M/25 →
      let inp := affineInput rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
        w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂
      let V := CenteredMomentAmplificationChildInput.volume inp
      1 ≤ V ∧ |Real.logb Z V| ≤ (23/25)*Mmax ∧ V ≤ Z^(Mmax+1) ∧
      sourceRadius inp ≤ Z^(Mmax+2) ∧
      ∀ I ∈ finiteColumns (Fintype.piFinset inp.pools),
        (I.absNorm : ℝ) ≤ Z^(2*Mmax+1) := by
  filter_upwards [eventual_affine_endpoint_factor (Fintype.card α) bslot b] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro T η₀ θ w σ freq hσ bΦ state p M t X₁ X₂ hX₁ hX₂ hM hmax hw hlo₁ hlo₂ hhi₁ hhi₂ hslots
  have hN : Fintype.card T ≤ Fintype.card α :=
    Fintype.card_le_of_injective (fun i : T => i.val) Subtype.val_injective
  have hv := affine_original_volume_caps rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ Mmax hZ.1 hM hmax hw hlo₁ hlo₂ hhi₁ hhi₂ hslots
  have hc := affine_polynomial_source_caps rayM H hH η₀ θ W hW aslot bslot lo hi haslot hWs
    w σ freq hσ state p ha M t X₁ X₂ hX₁ hX₂ (Fintype.card α) Mmax hN hZ.1 hM.le hmax
    hbslot hb hZ.2 hhi₁ hhi₂ hslots
  exact ⟨hv.1, hv.2.1, hv.2.2, hc.2.1, hc.2.2⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.weighted_padded_columns_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_volume_log_exact
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_original_volume_caps
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_padded_columns_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.affine_polynomial_source_caps
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_affine_endpoint_factor
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_affine_polynomial_caps

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineCaps -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryBudgetContraction; sha256 0a74fc4365fe68330bbccfa74c0d13ee3d89832e8ee542814c0ef8e587894f30 -/
section
                                                   

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open MeasureTheory HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentScale
open CenteredMomentFirstSourceReduction CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentSourceLiveColumn
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

/-- The two actual first-source budgets pass through their own Mellin
windows and the cross-label normalization, with no per-label Cauchy shortcut. -/
theorem actual_first_energy_from_geometry_budgets {ι : Type*}[Fintype ι]
    (s : Input ι) (R seed : Ideal O)(K Z ξ B M A : ℝ)(hK : 0< K)(hZ : 1< Z)
    (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle61JointSource.SourceCoordinate s R seed K Z ξ→ℂ)
    (N : ℕ)(a b : ℝ)(ha : 0< a)(hcard : Fintype.card ι≤ N)
    (haS : a≤ s.lower)(hbS : s.upper≤ b)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^B)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus)
    (t : ℝ)(J : ℕ)(E H : ℝ)(hE : 0≤ E)(hH : 0< H)
    (hleft : ∀u : ℝ,geometryLiveBudget false s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-t))≤(E*H)*(1+‖u‖)^(2*J))
    (hright : ∀u : ℝ,geometryLiveBudget true s R seed K Z ξ M A hK key weight N b
      (s.t+2*Real.pi*(u-(-t)))≤(E/H)*(1+‖u‖)^(2*J)) :
    firstActiveEnergyPair (geometryFirstSource s R seed K Z ξ hK key)
      (fun q=>weight q.val) (fun _=>logAnnulus) t ≤
      32*Z^M*(volume s*E)*
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖| *
        |∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (logAnnulus x))
          (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
          (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖| := by
  have hz : 0< Z := zero_lt_one.trans hZ
  have hL := actual_geometry_left_budget_window s R seed K Z ξ M A hK hz key weight
    N a b ha hcard haS hbS hs hz₁ hz₂ hc hsm t J (E*H) (mul_nonneg hE hH.le) hleft
  have hR := actual_geometry_right_budget_window s R seed K Z ξ M A hK hz key weight
    N a b ha hcard haS hbS hs hz₁ hz₂ hc hsm t J (E/H) (div_nonneg hE hH.le) hright
  let IL := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^J*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  have hv := volume_pos s
  have hve : 0≤ volume s*E := mul_nonneg hv.le hE
  have hLe : geometryLeftEnergy s R seed K Z ξ M A hK key (fun q=>weight q.val)
      (fun _=>logAnnulus) t≤(volume s*(E*H))*IL^2 := by
    have hh := (div_le_iff₀ hv).mp hL
    simpa only [IL,mul_assoc,mul_comm,mul_left_comm] using hh
  have hRe : geometryRightEnergy s R seed K Z ξ A hK key (fun _=>logAnnulus) t≤
      (volume s*(E/H))*IR^2 := by
    have hh := (div_le_iff₀ hv).mp hR
    simpa only [IR,mul_assoc,mul_comm,mul_left_comm] using hh
  have hLs := Real.sqrt_le_sqrt hLe
  have hRs := Real.sqrt_le_sqrt hRe
  rw [Real.sqrt_mul (mul_nonneg hv.le (mul_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hLs
  rw [Real.sqrt_mul (mul_nonneg hv.le (div_nonneg hE hH.le)),Real.sqrt_sq_eq_abs] at hRs
  have hprod := mul_le_mul hLs hRs (Real.sqrt_nonneg _) (by positivity)
  have hh := actual_first_energy_geometry_payment s R seed K Z ξ B M A hK hZ hs hz₁ hz₂
    hsource key (fun q=>weight q.val) (fun _=>logAnnulus) t
  apply hh.trans
  calc
    _≤(32*Z^M)*((Real.sqrt (volume s*(E*H))*|IL|)*(Real.sqrt (volume s*(E/H))*|IR|)) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (by positivity : 0≤32*Z^M)
    _=_ := by
      have heq : (Real.sqrt (volume s*(E*H))*|IL|)*(Real.sqrt (volume s*(E/H))*|IR|)=
          (volume s*E)*|IL| *|IR| := by
        have hp : (volume s*(E*H))*(volume s*(E/H))=(volume s*E)^2 := by
          field_simp
        have hr : Real.sqrt (volume s*(E*H))*Real.sqrt (volume s*(E/H))=volume s*E := by
          rw [←Real.sqrt_mul (mul_nonneg hv.le (mul_nonneg hE hH.le)),hp,Real.sqrt_sq hve]
        calc
          _=(Real.sqrt (volume s*(E*H))*Real.sqrt (volume s*(E/H)))*|IL| *|IR| := by ring
          _=_ := by rw [hr]
      rw [heq]
      dsimp only [IL,IR]
      ring


/-- The remaining analytic input is a bound on the literal normalized
live-source budgets. Both Mellin integrals and original physical contraction
are discharged here, uniformly before moving sources and geometry bins. -/
theorem actual_physical_mass_from_geometry_budgets {ι : Type*}[Fintype ι][DecidableEq ι]
    (W : 𝓢(ℝ,ℂ))(decay degree windowDegree : ℕ)
    (hc : HasCompactSupport logAnnulus)(hsm : ContDiff ℝ ∞ logAnnulus) :
    ∃C : ℝ,0≤ C ∧ ∀(s : Input ι)(R seed : Ideal O)(K Z ξ B M A : ℝ)
      (hK : 0< K)(hZ : 1< Z)(N : ℕ)(a b : ℝ),0< a → Fintype.card ι≤ N →
      a≤ s.lower → s.upper≤ b → Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      CenteredMomentOriginalCommonHarmonic.sourceRadius s≤ Z^B →
      ∀E H : ℤ×(Fin 5→ℤ)→ℝ,(∀key∈commonGeometryBins s R seed K Z ξ,0≤ E key) →
      (∀key∈commonGeometryBins s R seed K Z ξ,0< H key) →
      (∀key∈commonGeometryBins s R seed K Z ξ,∀(reflected : Bool)(t u : ℝ),
        geometryLiveBudget reflected s R seed K Z ξ M A hK key
          (fun q=>normPhase (coordinateBlock s R seed W K Z ξ q)) N b
          (s.t+2*Real.pi*(u-(if reflected then -t else t)))≤
          ((if reflected then E key/H key else E key*H key)*(1+‖t‖)^degree)*(1+‖u‖)^(2*windowDegree)) →
      physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator R) 1 W K Z ξ ≤
        C*Z^M*volume s*∑key∈commonGeometryBins s R seed K Z ξ,
          E key/(1+dyadicScale key.1)^decay := by
  obtain ⟨C,hC,hphysical⟩ := actual_physical_mass_geometry_contraction (ι:=ι) W decay degree
  let IL := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity logAnnulus hc hsm u‖
  let IR := ∫u : ℝ,(1+‖u‖)^windowDegree*‖columnDensity (fun x=>star (logAnnulus x))
    (CenteredMomentConjugateWindow.conjugate_compact logAnnulus hc)
    (CenteredMomentConjugateWindow.conjugate_smooth logAnnulus hsm) u‖
  refine ⟨C*32*|IL| *|IR|,by positivity,?_⟩
  intro s R seed K Z ξ B M A hK hZ N a b ha hn haS hbS hs hz₁ hz₂ hsource E H hE hH hbudget
  let factor := 32*Z^M*volume s*|IL| *|IR|
  have hf : 0≤ factor := by
    have hv := (volume_pos s).le
    have hz := (zero_lt_one.trans hZ).le
    dsimp [factor]
    positivity
  have hh := hphysical s R seed K Z ξ hK (fun key=>factor*E key)
    (fun key hk=>mul_nonneg hf (hE key hk)) (by
      intro key hk t
      have he := actual_first_energy_from_geometry_budgets s R seed K Z ξ B M A hK hZ
        key (fun q=>normPhase (coordinateBlock s R seed W K Z ξ q)) N a b ha hn haS hbS
        hs hz₁ hz₂ hsource hc hsm t windowDegree (E key*(1+‖t‖)^degree) (H key)
        (mul_nonneg (hE key hk) (by positivity)) (hH key hk)
        (fun u=>by simpa only [Bool.false_eq_true,ite_false,mul_assoc,mul_comm,mul_left_comm] using hbudget key hk false t u)
        (fun u=>by simpa only [ite_true,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hbudget key hk true t u)
      apply he.trans_eq
      dsimp only [factor,IL,IR]
      ring)
  apply hh.trans_eq
  simp only [mul_div_assoc,←Finset.mul_sum]
  dsimp only [factor]
  ring


/-- Separate the original height, outer Mellin height and column-window
height with one fixed factor; both reflection signs have the same cost. -/
lemma geometry_mellin_height (base height t u scale : ℝ)(hh : 0≤ height) :
    1+|base+scale*(u-t)|+height≤
      (1+|base|+height)*(1+|scale|)*(1+‖t‖)*(1+‖u‖) := by
  have hsub : |u-t|≤|u|+|t| := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le u (-t)
  have hab : |base+scale*(u-t)|≤|base|+|scale| *(|u|+|t|) := by
    calc
      _≤|base|+|scale*(u-t)| := abs_add_le _ _
      _≤ _ := by rw [abs_mul]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub (abs_nonneg scale))
  have ht : 0≤|t| := abs_nonneg t
  have hu : 0≤|u| := abs_nonneg u
  have hs : 0≤|scale| := abs_nonneg scale
  have hbase : 1≤1+|base|+height := by linarith [abs_nonneg base]
  have hprod : 0≤|t| *|u| := mul_nonneg ht hu
  have hprodS : 0≤|scale| *(|t| *|u|) := mul_nonneg hs hprod
  have hinner : 1+|scale| *(|u|+|t|)≤(1+|scale|)*(1+|t|)*(1+|u|) := by nlinarith
  have hfirst : 1+|base+scale*(u-t)|+height≤
      (1+|base|+height)*(1+|scale| *(|u|+|t|)) := by
    have hmul := mul_le_mul_of_nonneg_right hbase (mul_nonneg hs (add_nonneg hu ht))
    nlinarith
  apply hfirst.trans
  simpa only [Real.norm_eq_abs,mul_assoc] using
    mul_le_mul_of_nonneg_left hinner (zero_le_one.trans hbase)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_first_energy_from_geometry_budgets

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_physical_mass_from_geometry_budgets

#print axioms OAI.SevenEighths.Cycle61InitialMass.geometry_mellin_height

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryBudgetContraction -/

/- BEGIN ORIGINAL Cycle61.Physical.AmplifierSupport; sha256 e46223f1eed0039e9b5d810020aa8b416b50d733c658bd2ed114f566c7f06e88 -/
section
                                       
                                                                   

namespace Cycle61.Physical
noncomputable section
open Filter Cycle61.Arithmetic
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open CenteredMomentPrimePool

/-- One threshold controls every amplifier width in the compact cell family. -/
theorem uniform_amplifier_norm_lower (amin : ℝ) (hmin : 0 < amin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ a : ℝ, amin ≤ a →
      ∀ n : ℝ, Z^a/2 ≤ n → Z^(3*a/4) ≤ n := by
  filter_upwards [(tendsto_rpow_atTop (show 0 < amin/4 by linarith)).eventually
    (eventually_ge_atTop (2:ℝ)), eventually_gt_atTop (1:ℝ)] with Z hpow hZ
  refine ⟨hZ,?_⟩
  intro a ha n hn
  have hZ0 : 0 < Z := zero_lt_one.trans hZ
  have hsmall : 2 ≤ Z^(a/4) := hpow.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))
  have hid : Z^(3*a/4)*Z^(a/4) = Z^a := by
    rw [←Real.rpow_add hZ0]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_left hsmall
    (Real.rpow_nonneg hZ0.le (3*a/4))
  rw [hid] at hm
  linarith

/-- The literal annular prime pool supplies the stronger 3a/4 lower width
needed by all three extracted errors. No separately assumed prime range. -/
theorem actual_amplifier_prime_width
    (rayModulus : Ideal O) [NeZero rayModulus]
    (H : Subgroup (O ⧸ rayModulus)ˣ) (Sbad : Finset (Ideal O))
    (Mmin : ℝ) (hMmin : 0 < Mmin) :
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ M b : ℝ, Mmin ≤ M →
      3401/100000 ≤ b → b ≤ 1/25 →
      ∀ P ∈ primePool rayModulus H Sbad (1/2) 1 (Z^(M*amp b)),
        3*(M*amp b)/4 ≤ Real.logb Z (P.absNorm:ℝ) ∧
          Real.logb Z (P.absNorm:ℝ) ≤ M*amp b := by
  have hmin : 0 < Mmin*(62485051/9854400000) := by positivity
  filter_upwards [uniform_amplifier_norm_lower _ hmin] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro M b hM hb₁ hb₂ P hP
  have ha := amp_bounds ⟨hb₁,hb₂⟩
  have hamp : Mmin*(62485051/9854400000) ≤ M*amp b := by
    have hm : 0 ≤ M := hMmin.le.trans hM
    nlinarith
  have hs := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) (M*amp b))
    (Finset.mem_sdiff.mp hP).1
  have hlo : Z^(M*amp b)/2 ≤ (P.absNorm:ℝ) := by linarith [hs.1]
  have hup : (P.absNorm:ℝ) ≤ Z^(M*amp b) := by simpa only [mul_one] using hs.2
  have hnorm : 0 < (P.absNorm:ℝ) :=
    lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _) (by norm_num)) hlo
  exact ⟨(Real.le_logb_iff_rpow_le hZ.1 hnorm).mpr (hZ.2 _ hamp _ hlo),
    (Real.logb_le_iff_le_rpow hZ.1 hnorm).mpr hup⟩

end
end Cycle61.Physical

#print axioms Cycle61.Physical.actual_amplifier_prime_width

end
/- END ORIGINAL Cycle61.Physical.AmplifierSupport -/
