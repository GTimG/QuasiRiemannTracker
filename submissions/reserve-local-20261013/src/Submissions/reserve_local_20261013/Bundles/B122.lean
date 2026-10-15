/-
Reserve-balanced affine local-capacity adaptation for Kari Roegnvaldsson, with AI assistance.
Based on nielstron local44-20261013 and Kari Roegnvaldsson affine-local-20261013 at c707738.
Retains the amplifier and final savings while reallocating intermediate reserves.
Status: candidate under verification; no admission is claimed here.
All inherited attribution and Apache-2.0 notices are retained below.
Section hashes identify original, pre-adaptation module snapshots.
-/
/- Deterministically bundled proof sources; original notices are retained below.
Affine-capacity adaptation: the source module hashes below identify the
pre-adaptation provenance, not the modified declarations in this file. -/
import Submissions.reserve_local_20261013.Bundles.B011
import Submissions.reserve_local_20261013.Bundles.B072
import Submissions.reserve_local_20261013.Bundles.B076
import Submissions.reserve_local_20261013.Bundles.B078
import Submissions.reserve_local_20261013.Bundles.B121
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PlainGlobalEnergy

/- BEGIN ORIGINAL MODULE Analytic.JointIndependentMoment ; sha256 4110957ad055718ed496a8fed5c83d1b6c39cca6ec132bc32abaca767bf536fa -/
section



/-! The affine local moment with independent plain norm heights.
Both diagonal capacities are explicit. This is the subwindow used by
physical capacity selection, whose two lengths share one common upper bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentOriginalCommonHarmonic
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
variable (M : Ideal O) [NeZero M]
local instance independentMomentFinite : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Fixed-profile independent-height moment with a mesh independent of the
slot type. All three heights and all source data are live after the degree,
constant and scale threshold. No moment or profile-uniform estimate is a premise. -/
theorem actual_local_independent_plain_moment
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (Wslot : ℝ → ℂ) (aslot bslot lo hi a b bΦ Bmask ε : ℝ)
    (haslot : 0 < aslot) (hsSlot : Function.support Wslot ⊆ Set.Icc aslot bslot)
    (hcSlot : ContDiff ℝ ∞ Wslot) (hbslot : 0 < bslot)
    (ha : 0 < a) (hlo : a ≤ 1/4) (hhi : 1 ≤ b)
    (hbΦ : 0 < bΦ) (hBmask : 0 ≤ Bmask) (hε : 0 < ε)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta) (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (ηfirst η₀ : Character) (Q : Ideal O) (hQM : Q ≤ M)
    (hQzero : internalQ Q η₀ ≠ 0) (hQtop : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})
    (hQη : internalQ Q η₀ ≤ ηfirst.modulus)
    (p : Profiles a b) (Wradial : 𝓢(ℝ,ℂ)) (hWradial : ∀ x, 0 ≤ (Wradial x).re) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (θ : α → RayQuotient.Characters M H) (w σ freq : α → ℝ) (t₁ t₂ height : ℝ),
      (∀ i,0 ≤ w i) → (∀ i,w i ≤ meshGuaranteed Bmask ε) →
    ∀ (hσlo : ∀ i,lo ≤ σ i) (hσhi : ∀ i,σ i ≤ hi),
      0 ≤ height → (∀ i,|freq i| ≤ height) →
    ∀ (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂),
      410/1000 ≤ Real.logb Z X₁ → 410/1000 ≤ Real.logb Z X₂ →
      Real.logb Z X₁ ≤ 423/1000 → Real.logb Z X₂ ≤ 423/1000 →
      (∑ i,w i) ≤ 37/1000 →
      localRegion (Real.logb Z X₁) (Real.logb Z X₁) (∑ i,w i) →
      localRegion (Real.logb Z X₂) (Real.logb Z X₂) (∑ i,w i) →
    ∀ s : NaturalState Z Bmask bΦ,
      s.fixedModulus = internalQ Q η₀ → s.character = ηfirst → s.rowWidth = 1 →
      s.characterWidth = Real.logb Z (ηfirst.modulus.absNorm : ℝ) → s.radial.profile = Wradial →
      independentPlainEnergy s.character s.mask 1 (p.profile 0) (p.profile 1)
        (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i => Z^(w i)) t₁ t₂ X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
        C*(1+|t₁|+|t₂|+height)^J*Z^(1+ε) := by
  obtain ⟨J₁,C₁,hC₁,hfirst⟩ := actual_local_natural_moment_all_heights_explicit_mesh
    (α := α) M H hH Wslot aslot bslot lo hi a b bΦ Bmask ε
    haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε hbeta hbetaTop
    ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη (diagonalProfiles p 0) Wradial
  obtain ⟨J₂,C₂,hC₂,hsecond⟩ := actual_local_natural_moment_all_heights_explicit_mesh
    (α := α) M H hH Wslot aslot bslot lo hi a b bΦ Bmask ε
    haslot hsSlot hcSlot hbslot ha hlo hhi hbΦ hBmask hε hbeta hbetaTop
    ηfirst η₀ Q hQM hQzero hQtop hQ72 hQη (diagonalProfiles p 1) Wradial
  let J := max J₁ J₂
  refine ⟨J,(C₁+C₂)*2^J,by positivity,?_⟩
  filter_upwards [hfirst,hsecond] with Z hfirst hsecond
  refine ⟨hfirst.1,?_⟩
  intro θ w σ freq t₁ t₂ height hw hwmesh hσlo hσhi hheight hfreq
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcapacity₁ hcapacity₂
    s hQ hη hrow hwidth hradial
  have hf (t : ℝ) (i : α) : |freq i-t| ≤ height+|t| :=
    (abs_sub (freq i) t).trans (by linarith [hfreq i])
  have he₁ := hfirst.2 θ w σ (fun i => freq i-t₁) t₁ (height+|t₁|)
    hw hwmesh hσlo hσhi (by positivity) (hf t₁) X₁ X₁ hX₁ hX₁
    hn₁lo hn₁lo hn₁hi hn₁hi hsum hcapacity₁
    s hQ hη hrow hwidth hradial
  have he₂ := hsecond.2 θ w σ (fun i => freq i-t₂) t₂ (height+|t₂|)
    hw hwmesh hσlo hσhi (by positivity) (hf t₂) X₂ X₂ hX₂ hX₂
    hn₂lo hn₂lo hn₂hi hn₂hi hsum hcapacity₂
    s hQ hη hrow hwidth hradial
  have hpair := independent_energy_le_diagonal_energies s.character s.mask 1
    (p.profile 0) (p.profile 1) Wslot b b (fun x hx => (p.support 0 hx).2)
    (fun x hx => (p.support 1 hx).2)
    (fun i => CenteredMomentPrimeSlot.primePool M H bslot (Z^(w i)))
    (fun i I hI => (Finset.mem_filter.mp hI).2.1.ne_zero)
    (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I)
    (fun i => Z^(w i)) σ freq (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans hfirst.1) _)
    t₁ t₂ X₁ X₂ hX₁ hX₂ s.radial.keep s.radial.profile s.radial.scale s.radial.scale_pos
    (by simpa only [hradial] using hWradial)
  apply hpair.trans ((add_le_add he₁ he₂).trans ?_)
  have hbase : 1 ≤ 1+|t₁|+|t₂|+height := by linarith [abs_nonneg t₁,abs_nonneg t₂]
  have hpow₁ : (1+|t₁|+(height+|t₁|))^J₁ ≤ 2^J*(1+|t₁|+|t₂|+height)^J := by
    calc
      _ ≤ (2*(1+|t₁|+|t₂|+height))^J₁ := by gcongr; linarith [abs_nonneg t₂]
      _ ≤ (2*(1+|t₁|+|t₂|+height))^J :=
        pow_le_pow_right₀ (by linarith) (Nat.le_max_left _ _)
      _ = _ := mul_pow _ _ _
  have hpow₂ : (1+|t₂|+(height+|t₂|))^J₂ ≤ 2^J*(1+|t₁|+|t₂|+height)^J := by
    calc
      _ ≤ (2*(1+|t₁|+|t₂|+height))^J₂ := by gcongr; linarith [abs_nonneg t₁]
      _ ≤ (2*(1+|t₁|+|t₂|+height))^J :=
        pow_le_pow_right₀ (by linarith) (Nat.le_max_right _ _)
      _ = _ := mul_pow _ _ _
  have hZpow : 0 ≤ Z^(1+ε) := Real.rpow_nonneg (zero_lt_one.trans hfirst.1).le _
  calc
    _ ≤ C₁*(2^J*(1+|t₁|+|t₂|+height)^J)*Z^(1+ε)+
        C₂*(2^J*(1+|t₁|+|t₂|+height)^J)*Z^(1+ε) := by gcongr
    _ = _ := by ring

#print axioms actual_local_independent_plain_moment
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointIndependentMoment -/

/- BEGIN ORIGINAL MODULE Physical.LocalMomentInput ; sha256 85c0e18bf0d8fa46ec1dfce8c8115e7cda82222b1039e51772834e970bc92aca -/
section




/-! Dictionary and finite-row restriction for the actual independent-height
local moment. The natural ramified zeros and initial nonexceptional mask are
preserved in every identity. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Physical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentPositiveSummability CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeExpansion CenteredMomentSourceMass
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentRowNorm
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCubic
open Local44.Analytic Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

lemma independent_row_bounded {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (b₁ b₂ t₁ t₂ X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ∃ B : ℝ, ∀ z : O,
      ‖independentPlainRow η m A z W₁ W₂ S β P t₁ t₂ X₁ X₂‖ ≤ B := by
  refine ⟨(‖(Real.sqrt X₁ : ℂ)⁻¹‖ *
    (∑ I ∈ idealBall (b₁*X₁), ‖W₁ ((I.absNorm : ℝ)/X₁)‖)) *
    (‖(Real.sqrt X₂ : ℂ)⁻¹‖ *
    (∑ I ∈ idealBall (b₂*X₂), ‖W₂ ((I.absNorm : ℝ)/X₂)‖)) *
    ∏ i, ‖(Real.sqrt (P i) : ℂ)⁻¹‖ * (∑ I ∈ S i, ‖β i I‖), ?_⟩
  intro z
  simp only [independentPlainRow, normalizedSlot, norm_mul, norm_prod]
  apply mul_le_mul
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (plain_finite_norm η m A z t₁ W₁ b₁ X₁ hs₁ hX₁) (norm_nonneg _)
    · exact mul_le_mul_of_nonneg_left
        (plain_finite_norm η m A z t₂ W₂ b₂ X₂ hs₂ hX₂) (norm_nonneg _)
    · positivity
    · positivity
  · apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
    intro i _
    exact mul_le_mul_of_nonneg_left (slot_finite_norm η m A z 0 (S i) (β i))
      (norm_nonneg _)
  · positivity
  · positivity

lemma actual_independent_pair_norm {ι : Type*} [Fintype ι]
    (η : Character) (u : FreeRow) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (a b t₁ t₂ X₁ X₂ : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hc₁ : ContDiff ℝ ∞ W₁) (hc₂ : ContDiff ℝ ∞ W₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) :
    ‖independentPlainRow η (fixedBadMask*idealGenerator 1) 1 u.val
      W₁ W₂ S β P t₁ t₂ X₁ X₂‖ =
    ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 t₁ *
      polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 t₂ *
      ∏ i, normalizedSlot η rowMaskElement 1 u.val (S i) (β i) 0 (P i)‖ := by
  have hmask : independentPlainRow η (fixedBadMask*idealGenerator 1) 1 u.val
      W₁ W₂ S β P t₁ t₂ X₁ X₂ =
      independentPlainRow η rowMaskElement 1 u.val W₁ W₂ S β P t₁ t₂ X₁ X₂ := by
    rw [rowMaskElement_eq_fixed]
    simp only [independentPlainRow, rowTwistedSum, normalizedSlot,
      CenteredMomentHeckeSlots.rowSlot, one_mul,
      natural_unit_mask_coefficient (naturalRow η u.val u.property.1)]
  rw [hmask]
  have hrow : ∀ n, elementCoeff ((momentData η).character (momentElement u)) n =
      CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η)
        rowMaskElement 1 (1*u.val) n := by
    simpa only [momentData,momentElement,one_mul] using
      (momentData η).character_spec (momentElement u)
  simp only [independentPlainRow]
  rw [rowTwistedSum_eq η _ rowMaskElement 1 u.val hrow,
    rowTwistedSum_eq η _ rowMaskElement 1 u.val hrow,
    norm_mul, norm_mul,
    CenteredMomentPlainGlobalEnergy.plain_height_norm _ W₁ a b ha hs₁ hc₁ t₁ X₁ hX₁,
    CenteredMomentPlainGlobalEnergy.plain_height_norm _ W₂ a b ha hs₂ hc₂ t₂ X₂ hX₂,
    norm_mul, norm_mul]

/-- Arbitrary independent heights on the actual finite physical row set are
bounded by the exact natural radial energy, with its original keep predicate. -/
theorem finite_actual_independent_pair_le_energy {ι : Type*} [Fintype ι]
    (rows : Finset FreeRow) (η : Character) (Q : Ideal O)
    (Φ : 𝓢(ℝ,ℂ)) (U : ℝ) (hU : 0 < U)
    (hp : ∀ x, 0 ≤ (Φ x).re)
    (hrows : ∀ u ∈ rows, rowNorm u ≤ U)
    (hkeep : ∀ u ∈ rows, initialKeep η Q u.val)
    (hone : ∀ x ∈ Set.Icc (0:ℝ) 1, Φ x = 1)
    (W₁ W₂ : ℝ → ℂ) (a b t₁ t₂ X₁ X₂ : ℝ) (ha : 0 < a)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hc₁ : ContDiff ℝ ∞ W₁) (hc₂ : ContDiff ℝ ∞ W₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) :
    (∑ u ∈ rows, ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 t₁ *
      polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 t₂ *
      ∏ i, normalizedSlot η rowMaskElement 1 u.val (S i) (β i) 0 (P i)‖^2) ≤
    independentPlainEnergy η (fixedBadMask*idealGenerator 1) 1 W₁ W₂ S β P
      t₁ t₂ X₁ X₂ (initialKeep η Q) Φ U := by
  let m := fixedBadMask*idealGenerator (1:Ideal O)
  let f (z : O) : ℝ := if initialKeep η Q z then
    ‖independentPlainRow η m 1 z W₁ W₂ S β P t₁ t₂ X₁ X₂‖^2 *
      (Φ (‖eisEmbedding z‖^2/U)).re else 0
  obtain ⟨B,hB⟩ := independent_row_bounded η m 1 W₁ W₂ S β P b b t₁ t₂ X₁ X₂
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2) hX₁ hX₂
  have hsum : Summable f := bounded_radial_summable _ B hB (initialKeep η Q) Φ U hU
  have hf0 (z : O) : 0 ≤ f z := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hp _)
    · exact le_rfl
  have he (u : FreeRow) (hu : u ∈ rows) : f u.val =
      ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 t₁ *
        polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 t₂ *
        ∏ i, normalizedSlot η rowMaskElement 1 u.val (S i) (β i) 0 (P i)‖^2 := by
    have hx : ‖eisEmbedding u.val‖^2/U ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hU.le, (div_le_one hU).mpr ?_⟩
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    dsimp [f]
    rw [if_pos (hkeep u hu),hone _ hx,Complex.one_re,mul_one]
    exact congrArg (fun x : ℝ => x^2)
      (actual_independent_pair_norm η u W₁ W₂ S β P a b t₁ t₂ X₁ X₂
        ha hs₁ hs₂ hc₁ hc₂ hX₁ hX₂)
  calc
    _ = ∑ u ∈ rows, f u.val := Finset.sum_congr rfl (fun u hu => (he u hu).symm)
    _ = ∑ z ∈ rows.image Subtype.val, f z := by
      rw [Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)]
    _ ≤ ∑' z, f z := Summable.sum_le_tsum _ (fun z _ => hf0 z) hsum
    _ = _ := rfl

end SevenEighths.Local44.Physical
end
end OAI

#print axioms OAI.SevenEighths.Local44.Physical.actual_independent_pair_norm
#print axioms OAI.SevenEighths.Local44.Physical.finite_actual_independent_pair_le_energy
end
/- END ORIGINAL MODULE Physical.LocalMomentInput -/

/- BEGIN ORIGINAL MODULE Analytic.JointIndependentUniform ; sha256 f80884f70998dd5b2ba3fe8862deae3c390ae146d649a31537c88f0941d9dc22 -/
section


/-! Elementary finite-family and height-factor transport for the independent
plain-height moment. These lemmas preserve the quantifier order needed by
selected physical slots and the finite annulus derivative family. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OAI
noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.Local44.Analytic

/-- A finite family of eventual estimates admits one degree, one positive
constant and one threshold. `P` may include a different live-data type at
each index, as happens for the subtype of a selected finite slot set. -/
theorem finite_uniform_polynomial_bound {ι : Type*} [Fintype ι]
    (P : ι → ℕ → ℝ → ℝ → Prop)
    (hmono : ∀ i J K C D Z, 0 ≤ C → J ≤ K → C ≤ D → P i J C Z → P i K D Z)
    (h : ∀ i, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, P i J C Z) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ∀ i, P i J C Z := by
  choose J C hC hP using h
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨Finset.univ.sup J,1+∑ i,C i,by linarith,?_⟩
  filter_upwards [Filter.eventually_all.mpr hP] with Z hZ
  intro i
  have hJi : J i ≤ Finset.univ.sup J := Finset.le_sup (f := J) (Finset.mem_univ i)
  have hCi : C i ≤ 1+∑ i,C i := by
    have hh := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => (hC i).le)
      (Finset.mem_univ i)
    linarith
  exact hmono i _ _ _ _ Z (hC i).le hJi hCi (hZ i)

/-- Split the common polynomial height budget into three independent
polynomial factors. -/
lemma independent_height_factor (t₁ t₂ height : ℝ) (J : ℕ) (hheight : 0 ≤ height) :
    (1+|t₁|+|t₂|+height)^J ≤ (1+height)^J*(1+|t₁|)^J*(1+|t₂|)^J := by
  have hbase : 1+|t₁|+|t₂|+height ≤ (1+height)*(1+|t₁|)*(1+|t₂|) := by
    nlinarith [mul_nonneg (abs_nonneg t₁) (abs_nonneg t₂),
      mul_nonneg hheight (abs_nonneg t₁),mul_nonneg hheight (abs_nonneg t₂),
      mul_nonneg hheight (mul_nonneg (abs_nonneg t₁) (abs_nonneg t₂))]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase J

/-- Fourier heights ±2πv, ±2πw have independently polynomial growth,
with a constant fixed before the two frequencies or the contour height. -/
lemma independent_fourier_height_factor (v w height : ℝ) (J : ℕ) (hheight : 0 ≤ height) :
    (1+|-2*Real.pi*v|+|-2*Real.pi*w|+height)^J ≤
      (1+2*Real.pi)^(2*J)*(1+height)^J*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  have hv : 1+|-2*Real.pi*v| ≤ (1+2*Real.pi)*(1+‖v‖) := by
    rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_pos Real.pi_pos,←Real.norm_eq_abs]
    nlinarith [Real.pi_pos,norm_nonneg v]
  have hw : 1+|-2*Real.pi*w| ≤ (1+2*Real.pi)*(1+‖w‖) := by
    rw [abs_mul,abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_pos Real.pi_pos,←Real.norm_eq_abs]
    nlinarith [Real.pi_pos,norm_nonneg w]
  have hvpow : (1+‖v‖)^J ≤ ((1+‖v‖)^J)^2 := by
    have hh : 1 ≤ (1+‖v‖)^J := one_le_pow₀ (by linarith [norm_nonneg v])
    nlinarith
  have hwpow : (1+‖w‖)^J ≤ ((1+‖w‖)^J)^2 := by
    have hh : 1 ≤ (1+‖w‖)^J := one_le_pow₀ (by linarith [norm_nonneg w])
    nlinarith
  calc
    _ ≤ (1+height)^J*(1+|-2*Real.pi*v|)^J*(1+|-2*Real.pi*w|)^J :=
      independent_height_factor _ _ _ J hheight
    _ ≤ (1+height)^J*((1+2*Real.pi)*(1+‖v‖))^J*
        ((1+2*Real.pi)*(1+‖w‖))^J := by gcongr
    _ = (1+2*Real.pi)^(2*J)*(1+height)^J*(1+‖v‖)^J*(1+‖w‖)^J := by
      simp only [mul_pow,pow_mul,pow_two]
      ring
    _ ≤ _ := by gcongr

#print axioms finite_uniform_polynomial_bound
#print axioms independent_fourier_height_factor
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointIndependentUniform -/

/- BEGIN ORIGINAL MODULE Physical.LocalCertifiedPair ; sha256 b25f7a7d30f0544720a3e3d49548c40c8210c7f93dd4da6f33e10e277422fa34 -/
section




/-! The new local moment applied to literal physical prime-slot coefficients.
No analytic estimate is retained as a premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Filter
namespace SevenEighths.Local44.Physical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeSlots CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentDetectorDictionary QuadraticInitialBound
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentRowNorm ConcretePrimeRowBridge
open Local44.Analytic Cycle25WeightedNumeratorPhysical
local notation "O" => HeckeFamily.O

lemma independent_energy_relative_pool {α : Type*} [Fintype α]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H)
    (η η₀ : Character) (θ : α → RayQuotient.Characters M H) (m A : O)
    (W₁ W₂ : ℝ → ℂ) (b P : α → ℝ) (β : α → Ideal O → ℂ)
    (t₁ t₂ X₁ X₂ : ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    independentPlainEnergy η m A W₁ W₂
      (fun i => CenteredMomentPrimeSlot.primePool M H (b i) (P i))
      (fun i I => idealCoeff η₀.inverse I*β i I) P t₁ t₂ X₁ X₂ keep Φ K =
    independentPlainEnergy η m A W₁ W₂
      (fun i => CenteredMomentPrimeSlot.primePool M H (b i) (P i))
      (fun i I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I)
      P t₁ t₂ X₁ X₂ keep Φ K := by
  have hslot (z : O) (i : α) :
      normalizedSlot η m A z (CenteredMomentPrimeSlot.primePool M H (b i) (P i))
        (fun I => idealCoeff η₀.inverse I*β i I) 0 (P i) =
      normalizedSlot η m A z (CenteredMomentPrimeSlot.primePool M H (b i) (P i))
        (fun I => idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*β i I) 0 (P i) := by
    unfold normalizedSlot rowSlot
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    dsimp only
    rw [CenteredMomentDetectorPlainRelativeClass.relative_pool M H hH η₀ (θ i) (b i) (P i) I hI]
  simp only [independentPlainEnergy,independentPlainRow,hslot]

/-- A fixed pair of smooth profiles, arbitrary independent heights and all
finite natural physical row sets. The explicit mesh precedes the slot type. -/
theorem certified_local_physical_pair {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {D : Cycle25.Weighted.MomentData} (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (η : Character) (ε : ℝ) (hε : 0 < ε)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (p : Profiles (1/4) (9/4)) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
    ∀ (width : α → ℝ) (z : α → ℂ) (t₁ t₂ height : ℝ),
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ meshGuaranteed 0 ε) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
    ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
      410/1000 ≤ Real.logb U X₁ → 410/1000 ≤ Real.logb U X₂ →
      Real.logb U X₁ ≤ 423/1000 → Real.logb U X₂ ≤ 423/1000 →
      (∑ i, width i) ≤ 37/1000 →
      localRegion (Real.logb U X₁) (Real.logb U X₁) (∑ i, width i) →
      localRegion (Real.logb U X₂) (Real.logb U X₂) (∑ i, width i) →
    (∑ u ∈ rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 t₁ *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 t₂ *
      ∏ i, normalizedSlot η rowMaskElement 1 u.val
        (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) ≤
      C*(1+|t₁|+|t₂|+height)^J*U^(1+ε) := by
  obtain ⟨bΦ,hbΦ,hsΦ⟩ := radialMajorant_support_bound
  have hsupport : Function.support (fun x => conj (F.W x)) ⊆ Set.Icc (1:ℝ) 2 := by
    intro x hx
    exact F.complex_support (by simpa using hx)
  obtain ⟨J,C,hC,hbound⟩ := actual_local_independent_plain_moment (α := α)
    F.modulus ⊤ le_top (fun x => conj (F.W x)) 1 2 (33/50) (33/50)
    (1/4) (9/4) bΦ 0 ε (by norm_num) hsupport
    (Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hbΦ (by norm_num) hε hbeta hbetaTop
    η η (weighted_sourceFixedIdeal F) (weighted_sourceFixedIdeal_le_modulus F)
    (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 (weighted_source_fixed_gates F η).2.2.1
    p radialMajorant radialMajorant_nonneg
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hbound,eventually_fixed_source_keep F η] with U hbound hkeep
  have hU := hbound.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows width z t₁ t₂ height hw hwmax hz hheight hzim
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂
  have hN : (1:ℝ) ≤ η.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hNpos : 0 < (η.modulus.absNorm:ℝ) := zero_lt_one.trans_le hN
  let δ := Real.logb U (η.modulus.absNorm:ℝ)
  have hδ : 0 ≤ δ := Real.logb_nonneg hU hN
  have hη : (η.modulus.absNorm:ℝ) ≤ U^δ :=
    le_of_eq (Real.rpow_logb hUp hU.ne' hNpos).symm
  let s := initialState η (internalQ (weighted_sourceFixedIdeal F) η)
    radialMajorant bΦ U δ hU.le hδ hsΦ radialMajorant_nonneg hη
  have he := hbound.2 (fun _ => 1) width (fun _ => 33/50) (fun i => -(z i).im)
    t₁ t₂ height hw hwmax (fun _ => le_rfl) (fun _ => le_rfl) hheight
    (fun i => by simpa only [abs_neg] using hzim i)
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂
    s rfl rfl rfl rfl rfl
  have hfinite := finite_actual_independent_pair_le_energy rows η
    (internalQ (weighted_sourceFixedIdeal F) η) radialMajorant U hUp
    radialMajorant_nonneg (fun u hu => (hrows u hu).2)
    (fun u hu => hkeep u (hrows u hu).1) radialMajorant_one
    (p.profile 0) (p.profile 1) (1/4) (9/4) t₁ t₂ X₁ X₂ (by norm_num)
    (p.support 0) (p.support 1) ((p.profile 0).smooth ⊤) ((p.profile 1).smooth ⊤)
    hX₁ hX₂ (fun i => CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
    (fun i => physicalSlotCoefficient η F.W (U^(width i)) (z i)) (fun i => U^(width i))
  apply hfinite.trans
  have hcoef : (fun (i : α) I => physicalSlotCoefficient η F.W (U^(width i)) (z i) I) =
      (fun (i : α) I => idealCoeff η.inverse I*HeckePrimeAnnular.annularWeight
        (fun x => conj (F.W x)) (U^(width i)) (33/50) (-(z i).im) I) := by
    funext i I
    rw [weighted_physical_annular_all F η _ (Real.rpow_pos_of_pos hUp _) (z i) I,hz i]
    norm_num
  rw [hcoef,independent_energy_relative_pool F.modulus ⊤ le_top η η (fun (_ : α) => 1)]
  exact he

end SevenEighths.Local44.Physical
end
end OAI

#print axioms OAI.SevenEighths.Local44.Physical.certified_local_physical_pair
end
/- END ORIGINAL MODULE Physical.LocalCertifiedPair -/

/- BEGIN ORIGINAL MODULE Physical.LocalCertifiedFourier ; sha256 d0087740c29effceaeaa4f0f4bbe27ac667620325a4460cc4b7ffebc116074cb -/
section



/-! Certified local reflected Fourier moments. The selected slot set and
both annulus derivative indices are chosen after one common degree,
constant and eventual threshold. The two Fourier frequencies are unbounded. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Local44.Physical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentFiniteProfileExceptional CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentRowNorm CenteredMomentDetectorDictionary
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open Local44.Analytic Cycle25WeightedNumeratorPhysical

/-- The four fixed profile pairs; Fourier modulation is carried by the
independent live heights, not by a moving choice of profile. -/
def numeratorBaseProfiles (j k : Fin 2) : Profiles (1/4) (9/4) where
  profile i := if i=0 then numeratorAnnular j else numeratorAnnular k
  support := by
    intro i x hx
    split_ifs at hx
    · exact numeratorAnnular_support j hx
    · exact numeratorAnnular_support k hx

@[simp] lemma numeratorBaseProfiles_zero (j k : Fin 2) :
    (numeratorBaseProfiles j k).profile 0 = numeratorAnnular j := by
  simp [numeratorBaseProfiles]

@[simp] lemma numeratorBaseProfiles_one (j k : Fin 2) :
    (numeratorBaseProfiles j k).profile 1 = numeratorAnnular k := by
  simp [numeratorBaseProfiles]

/-- A literal reflected Fourier estimate for fixed slot and derivative
choices. This is a proposition abbreviation, not an analytic hypothesis. -/
def localReflectedFourierAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (ε : ℝ)
    (T : Finset (Fin D.N)) (j k : Fin 2) (J : ℕ) (C U : ℝ) : Prop :=
    1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
    ∀ (width : T → ℝ) (z : T → ℂ) (height : ℝ),
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ meshGuaranteed 0 ε) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
    ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
      410/1000 ≤ Real.logb U X₁ → 410/1000 ≤ Real.logb U X₂ →
      Real.logb U X₁ ≤ 423/1000 → Real.logb U X₂ ≤ 423/1000 →
      (∑ i, width i) ≤ 37/1000 →
      localRegion (Real.logb U X₁) (Real.logb U X₁) (∑ i, width i) →
      localRegion (Real.logb U X₂) (Real.logb U X₂) (∑ i, width i) →
    ∀ v w : ℝ,
      (∑ u ∈ rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y : ℝ => (annulus y : ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏ i, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) ≤
        C*(1+|-2*Real.pi*v|+|-2*Real.pi*w|+height)^J*U^(1+ε)

lemma localReflectedFourierAt_mono {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (ε : ℝ)
    (T : Finset (Fin D.N)) (j k : Fin 2) (J K : ℕ) (C E U : ℝ)
    (hC : 0 ≤ C) (hJK : J ≤ K) (hCE : C ≤ E)
    (h : localReflectedFourierAt F ε T j k J C U) :
    localReflectedFourierAt F ε T j k K E U := by
  refine ⟨h.1,?_⟩
  intro rows hrows width z height hw hwmax hz hh hzim
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂ v w
  apply (h.2 rows hrows width z height hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂
    hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂ v w).trans
  have hb : 1 ≤ 1+|-2*Real.pi*v|+|-2*Real.pi*w|+height := by
    linarith [abs_nonneg (-2*Real.pi*v),abs_nonneg (-2*Real.pi*w)]
  have hp := pow_le_pow_right₀ hb hJK
  have hU : 0 ≤ U^(1+ε) := Real.rpow_nonneg (zero_lt_one.trans h.1).le _
  have hE : 0 ≤ E := hC.trans hCE
  gcongr

/-- The fixed-choice reflected estimate is discharged by the actual
independent-height physical pair theorem. -/
theorem certified_local_reflected_fourier_fixed {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (ε : ℝ) (hε : 0 < ε)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8)
    (T : Finset (Fin D.N)) (hT : T.Nonempty) (j k : Fin 2) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      localReflectedFourierAt F ε T j k J C U := by
  letI : Nonempty T := ⟨⟨hT.choose,hT.choose_spec⟩⟩
  let η := fixedSourcePrincipal F.S F.exclusions.prime
  obtain ⟨J,C,hC,hpair⟩ := certified_local_physical_pair (α := T) F η ε hε hbeta hbetaTop
    (numeratorBaseProfiles j k)
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hpair] with U hpair
  refine ⟨hpair.1,?_⟩
  intro rows hrows width z height hw hwmax hz hh hzim
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂ v w
  have he := hpair.2 rows hrows width z (-2*Real.pi*v) (-2*Real.pi*w) height
    hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂
  have heq :
      (∑ u ∈ rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y : ℝ => (annulus y : ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏ i, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) =
      (∑ u ∈ rows, ‖polynomial ((momentData η).character (momentElement u)) false
        ((numeratorBaseProfiles j k).profile 0) X₁ 0 (-2*Real.pi*v) *
        polynomial ((momentData η).character (momentElement u)) false
          ((numeratorBaseProfiles j k).profile 1) X₂ 0 (-2*Real.pi*w) *
        ∏ i, normalizedSlot η rowMaskElement 1 u.val
          (CenteredMomentPrimeSlot.primePool F.modulus ⊤ 2 (U^(width i)))
          (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2) := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp only [η]
    simp_rw [numeratorBaseProfiles_zero,numeratorBaseProfiles_one,numeratorAnnular_apply,
      source_physical_slot_conj F u _ _ (Real.rpow_pos_of_pos (zero_lt_one.trans hpair.1) _),
      norm_mul,inverse_annular_norm_eq F u j v X₁ hX₁,
      inverse_annular_norm_eq F u k w X₂ hX₂,←map_prod,Complex.norm_conj]
  exact heq ▸ he

/-- The selected slot set, both derivative choices, both independent Fourier
frequencies and the contour height are live after one uniform constant and
scale threshold. The estimate has no analytic premise. -/
theorem certified_local_reflected_fourier_moment {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (ε : ℝ) (hε : 0 < ε)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ degree J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ T : Finset (Fin D.N), T.Nonempty →
      ∀ (width : T → ℝ) (z : T → ℂ) (height : ℝ),
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ meshGuaranteed 0 ε) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
      410/1000 ≤ Real.logb U X₁ → 410/1000 ≤ Real.logb U X₂ →
      Real.logb U X₁ ≤ 423/1000 → Real.logb U X₂ ≤ 423/1000 →
      (∑ i, width i) ≤ 37/1000 →
      localRegion (Real.logb U X₁) (Real.logb U X₁) (∑ i, width i) →
      localRegion (Real.logb U X₂) (Real.logb U X₂) (∑ i, width i) →
      ∀ j k : Fin 2, ∀ v w : ℝ,
      (∑ u ∈ rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y : ℝ => (annulus y : ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏ i, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) ≤
        (C*(1+height)^degree*U^(1+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  let Choice := {T : Finset (Fin D.N) // T.Nonempty} × (Fin 2 × Fin 2)
  let P : Choice → ℕ → ℝ → ℝ → Prop := fun i =>
    localReflectedFourierAt F ε i.1.val i.2.1 i.2.2
  obtain ⟨J,C,hC,huniform⟩ := finite_uniform_polynomial_bound P
    (fun i J K C E U hC hJK hCE h =>
      localReflectedFourierAt_mono F ε i.1.val i.2.1 i.2.2 J K C E U hC hJK hCE h)
    (fun i => certified_local_reflected_fourier_fixed F ε hε hbeta hbetaTop
      i.1.val i.1.property i.2.1 i.2.2)
  refine ⟨J,J,C*(1+2*Real.pi)^(2*J),by positivity,?_⟩
  filter_upwards [huniform,eventually_gt_atTop (1:ℝ)] with U huniform hU
  refine ⟨hU,?_⟩
  intro rows hrows T hT width z height hw hwmax hz hh hzim
    X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂ j k v w
  have he := (huniform (⟨⟨T,hT⟩,j,k⟩ : Choice)).2 rows hrows width z height
    hw hwmax hz hh hzim X₁ X₂ hX₁ hX₂ hn₁lo hn₂lo hn₁hi hn₂hi hsum hcap₁ hcap₂ v w
  apply he.trans
  have hheight := independent_fourier_height_factor v w height J hh
  have hUp : 0 ≤ U^(1+ε) := Real.rpow_nonneg (zero_lt_one.trans hU).le _
  calc
    _ ≤ C*((1+2*Real.pi)^(2*J)*(1+height)^J*
        ((1+‖v‖)^J)^2*((1+‖w‖)^J)^2)*U^(1+ε) := by gcongr
    _ = _ := by ring

end SevenEighths.Local44.Physical
end
end OAI

#print axioms OAI.SevenEighths.Local44.Physical.certified_local_reflected_fourier_moment
end
/- END ORIGINAL MODULE Physical.LocalCertifiedFourier -/

/- BEGIN ORIGINAL MODULE Physical.LocalTransportFourier ; sha256 0b2bc4d0d1477cd6467c11213509366b198e5b08f1977dbf4a22c1445e37868d -/
section




/-! A genuine reflected Fourier estimate throughout the physical transport
capacity range, using the local, incumbent and empty-slot estimates. -/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Local44.Physical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentRowNorm CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentEnergyBands
open Local44.Analytic Cycle25WeightedNumeratorPhysical

/-- A common explicit mesh for both nonempty transport branches. -/
def transportMomentMesh (ε : ℝ) : ℝ :=
  min (meshGuaranteed 0 ε) (Cycle25.Energy.commonMesh 2 0 1 (ε/4))

lemma transportMomentMesh_pos (ε : ℝ) (hε : 0 < ε) : 0 < transportMomentMesh ε :=
  lt_min (meshGuaranteed_pos 0 ε (by norm_num) hε)
    (Cycle25.Energy.commonMesh_pos 2 0 1 (ε/4) (by norm_num) (by norm_num) (by positivity))

lemma transportMomentMesh_le_local (ε : ℝ) : transportMomentMesh ε ≤ meshGuaranteed 0 ε :=
  min_le_left _ _

lemma transportMomentMesh_le_old (ε : ℝ) :
    transportMomentMesh ε ≤ Cycle25.Energy.commonMesh 2 0 1 (ε/4) := min_le_right _ _

private lemma transport_fourier_rhs_mono (C E U ε height v w : ℝ) (d degree J K : ℕ)
    (hC : 0 ≤ C) (hCE : C ≤ E) (hU : 0 ≤ U) (hh : 0 ≤ height)
    (hd : d ≤ degree) (hJ : J ≤ K) :
    (C*(1+height)^d*U^(1+ε))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 ≤
      (E*(1+height)^degree*U^(1+ε))*((1+‖v‖)^K)^2*((1+‖w‖)^K)^2 := by
  have hE : 0 ≤ E := hC.trans hCE
  have hhpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1+height by linarith) hd
  have hvpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1+‖v‖ by linarith [norm_nonneg v]) hJ
  have hwpow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 1+‖w‖ by linarith [norm_nonneg w]) hJ
  have hUp : 0 ≤ U^(1+ε) := Real.rpow_nonneg hU _
  gcongr

/-- Every live selected family is handled at its transported capacity. The
degrees, constant and threshold precede the rows, shifts, slots and Fourier
parameters, and there is no analytic estimate among the premises. -/
theorem certified_transport_reflected_fourier_moment {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D)
    (hbeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hbetaTop : HeckeZeroSupremum.beta ≤ 7/8) :
    ∃ degree J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100 : ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ n t : ℝ, _root_.Local44.Physical.BareWindow n → 0 ≤ t → n+t ≤ 2 →
      ∀ T : Finset (Fin D.N), ∀ (width : T → ℝ) (z : T → ℂ) (height : ℝ),
      (∀ i, 0 < width i) → (∀ i, width i ≤ transportMomentMesh D.t) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      (∑ i, width i) ≤ _root_.Local44.Physical.transportCapacity n t →
      ∀ X₁ X₂ : ℝ, 1 ≤ X₁ → 1 ≤ X₂ →
      Real.logb U X₁ ≤ n+t → Real.logb U X₂ ≤ n+t →
      ∀ j k : Fin 2, ∀ v w : ℝ,
      (∑ u ∈ rows, ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
          (scaleTest (fun y : ℝ => (annulus y : ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏ i, HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (U^(width i)) (z i)‖^2) ≤
        (C*(1+height)^degree*U^(1+D.t))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨dl,Jl,Cl,hCl,hlocal⟩ := certified_local_reflected_fourier_moment
    F D.t D.t_pos hbeta hbetaTop
  obtain ⟨do_,Jo,Co,hCo,hold⟩ := certified_reflected_fourier_moment F (3/4)
    (by norm_num) le_rfl hbeta (by linarith)
  obtain ⟨Jz,Cz,hCz,hzero⟩ := certified_reflected_zero_fourier_moment F
  refine ⟨dl+do_,Jl+Jo+Jz,Cl+Co+Cz,by positivity,?_⟩
  filter_upwards [hlocal,hold,hzero] with U hlocal hold hzero
  have hU := hlocal.1
  have hUp : 0 < U := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows n t hn ht hnt T width z height hw hwmax hz hh hzim hsum
    X₁ X₂ hX₁ hX₂ hn₁ hn₂ j k v w
  have hw0 : ∀ i, 0 ≤ width i := fun i => (hw i).le
  have hsum0 : 0 ≤ ∑ i, width i := Finset.sum_nonneg (fun i _ => hw0 i)
  have hX₁pos : 0 < X₁ := zero_lt_one.trans_le hX₁
  have hX₂pos : 0 < X₂ := zero_lt_one.trans_le hX₂
  have hn₁0 : 0 ≤ Real.logb U X₁ := Real.logb_nonneg hU hX₁
  have hn₂0 : 0 ≤ Real.logb U X₂ := Real.logb_nonneg hU hX₂
  have hxpow (X a : ℝ) (hX : 0 < X) (ha : Real.logb U X ≤ a) : X ≤ U^a := by
    calc
      X = U^(Real.logb U X) := (Real.rpow_logb hUp hU.ne' hX).symm
      _ ≤ U^a := Real.rpow_le_rpow_of_exponent_le hU.le ha
  have hlocalmax : ∀ i, width i ≤ meshGuaranteed 0 D.t :=
    fun i => (hwmax i).trans (transportMomentMesh_le_local D.t)
  have holdmax : ∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (D.t/4) :=
    fun i => (hwmax i).trans (transportMomentMesh_le_old D.t)
  rcases _root_.Local44.Physical.transport_pair_diagonal_dispatch hn ht hsum0 hn₁ hn₂ hsum with
    hloc | hcap | hsumzero
  · obtain ⟨hn₁lo,hn₁hi,hn₂lo,hn₂hi,hslo,hshi,hcap₁,hcap₂⟩ := hloc
    have hregion₁ : localRegion (Real.logb U X₁) (Real.logb U X₁) (∑ i,width i) := by
      constructor <;> linarith [hcap₁.1,hcap₁.2]
    have hregion₂ : localRegion (Real.logb U X₂) (Real.logb U X₂) (∑ i,width i) := by
      constructor <;> linarith [hcap₂.1,hcap₂.2]
    have hT : T.Nonempty := by
      by_contra hT
      have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      subst T
      norm_num at hslo
    have hb := hlocal.2 rows hrows T hT width z height hw0 hlocalmax hz hh hzim
      X₁ X₂ hX₁pos hX₂pos (by linarith) (by linarith) hn₁hi hn₂hi hshi hregion₁ hregion₂ j k v w
    exact hb.trans (transport_fourier_rhs_mono Cl (Cl+Co+Cz) U D.t height v w dl (dl+do_)
      Jl (Jl+Jo+Jz) hCl.le (by linarith) hUp.le hh (by omega) (by omega))
  · have hn₁one : Real.logb U X₁ ≤ 1 := by linarith
    have hn₂one : Real.logb U X₂ ≤ 1 := by linarith
    have hX₁max : X₁ ≤ U := by simpa only [Real.rpow_one] using hxpow X₁ 1 hX₁pos hn₁one
    have hX₂max : X₂ ≤ U := by simpa only [Real.rpow_one] using hxpow X₂ 1 hX₂pos hn₂one
    have hcapacity : length U X₁+length U X₂+6*(3/4)*(∑ i,width i) ≤ 1 := by
      simp only [length,max_eq_right hX₁,max_eq_right hX₂]
      linarith only [hcap]
    have hb := hold.2 rows hrows T width z height hw0 holdmax hz hh hzim
      X₁ X₂ hX₁pos hX₂pos hX₁max hX₂max hcapacity j k v w
    exact hb.trans (transport_fourier_rhs_mono Co (Cl+Co+Cz) U D.t height v w do_ (dl+do_)
      Jo (Jl+Jo+Jz) hCo.le (by linarith) hUp.le hh (by omega) (by omega))
  · have hempty : IsEmpty T := ⟨fun i => by
      have hi := Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
      linarith [hw i]⟩
    let : IsEmpty T := hempty
    have hX₁max := hxpow X₁ 2 hX₁pos (hn₁.trans hnt)
    have hX₂max := hxpow X₂ 2 hX₂pos (hn₂.trans hnt)
    have hb := hzero.2 rows hrows X₁ X₂ hX₁pos hX₂pos hX₁max hX₂max j k v w
    simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]
    apply hb.trans
    simpa only [pow_zero,mul_one] using
      transport_fourier_rhs_mono Cz (Cl+Co+Cz) U D.t height v w 0 (dl+do_)
        Jz (Jl+Jo+Jz) hCz.le (by linarith) hUp.le hh (Nat.zero_le _) (by omega)

end SevenEighths.Local44.Physical
end
end OAI

#print axioms OAI.SevenEighths.Local44.Physical.certified_transport_reflected_fourier_moment
end
/- END ORIGINAL MODULE Physical.LocalTransportFourier -/
