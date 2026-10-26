import Candidate.Cycle63.Physical.InitialMass.SourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryAdmission
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.InputParentCapacity

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentFiniteProfileExceptional CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildSourceCaps CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSourceRectangle CenteredMomentAddedZeroUniform
open CenteredMomentEnergyInputParentCapacity Cycle63InitialSource
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
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.weighted_padded_columns_norm
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_volume_log_exact
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_original_volume_caps
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_padded_columns_norm
#print axioms OAI.SevenEighths.Cycle63InitialMass.affine_polynomial_source_caps
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_affine_endpoint_factor
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_affine_polynomial_caps
