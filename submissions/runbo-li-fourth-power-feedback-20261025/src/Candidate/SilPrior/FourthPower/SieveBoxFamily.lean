/- Copyright (c) 2026 Sil. Apache-2.0.
Actual-length form of the uniform weighted cross-family estimate.
ColumnBox stores only elementary support and size facts, no analytic input.
-/
import Candidate.SilPrior.FourthPower.SieveColumnGeometry
import Candidate.SilPrior.FourthPower.SieveFrequencyGeometry

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.SieveBoxFamily
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic CompletedGauss ConcreteTraceCRT
open ConcretePrimeRowBridge CanonicalRowCompletion CanonicalQuadraticSieve
open SexticSieve SieveOperator SieveUncoupling SievePoissonBound
open EisensteinSchwartzPoisson SieveWindow
local notation "Id" => Ideal ActualEisensteinCubic.O
local notation "O" => ActualEisensteinCubic.O

structure ColumnBox where
  repeated : Finset Id
  radical : Finset Id
  scale : ℝ
  upper : ℝ
  scale_pos : 0 < scale
  upper_nonneg : 0 ≤ upper
  residue : EisensteinEPrimaryPhase.Coord
  repeated_good : ∀ U ∈ repeated, Supported U
  repeated_le : ∀ U ∈ repeated, (Ideal.absNorm U : ℝ) ≤ upper
  radical_good : ∀ R ∈ radical, Supported R ∧ PowerFree 6 R
  radical_bounds : ∀ R ∈ radical, scale ≤ (Ideal.absNorm R : ℝ) ∧ (Ideal.absNorm R : ℝ) ≤ 2*scale
  radical_ray : ∀ R ∈ radical, ray R = residue

abbrev Coefficients (B : ColumnBox) := ↥B.repeated × ↥B.radical → ℂ

def cost (ε : ℝ) (hε : 0 < ε) (C : ℝ) (B : ColumnBox) (L : ℝ) : ℝ :=
  C*L^ε*SieveRanges.lambda L (2*B.scale)*
    (IdealCoprimeSieveOperator.supportConstant ε hε*(2*B.scale)^ε)

def boxFamily (B₁ B₂ : ColumnBox) (Ks : Finset Id) (a : Coefficients B₁) (b : Coefficients B₂)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (c : O) : ℝ :=
  ∑ u : B₁.repeated, ∑ v : B₂.repeated, ∑ k : Ks,
    ‖∑ r : B₁.radical, ∑ s : B₂.radical,
      (if IsCoprime r.val s.val then star (a (u,r))*b (v,s)*crossKernel u.val v.val r.val s.val k.val else 0)*
        paperRadialFourier W (M*‖eisEmbedding c‖^2*(Ideal.absNorm k.val : ℝ)/
          ((Ideal.absNorm r.val : ℝ)*(Ideal.absNorm s.val : ℝ)))‖

theorem log_ratio_bound (P X : ℝ) (hP : 0 < P) (hX : P ≤ X) (hX' : X ≤ 2*P) :
    |Real.log (X/P)| ≤ Real.log 2 :=
  log_bound ((le_div_iff₀ hP).mpr (by simpa using hX)) ((div_le_iff₀ hP).mpr hX')

theorem radial_log_identity (M Q K₀ P₁ P₂ R T K : ℝ)
    (hK₀ : 0 < K₀) (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hR : 0 < R) (hT : 0 < T) (hK : 0 < K) :
    (M*Q*K₀/(P₁*P₂))*Real.exp (Real.log (K/K₀)-Real.log (R/P₁)-Real.log (T/P₂)) =
      M*Q*K/(R*T) := by
  rw [Real.exp_sub,Real.exp_sub,Real.exp_log (div_pos hK hK₀),
    Real.exp_log (div_pos hR hP₁),Real.exp_log (div_pos hT hP₂)]
  field_simp

theorem product_frequency_geometry (B : ColumnBox) (Ks : Finset Id) (K₀ : ℝ) (hK₀ : 0 < K₀)
    (hK : ∀ K ∈ Ks, Supported K ∧ K₀ ≤ (Ideal.absNorm K : ℝ) ∧ (Ideal.absNorm K : ℝ) ≤ 2*K₀) :
    ∀ U ∈ B.repeated, ∀ K ∈ Ks, Supported (U*K) ∧ (Ideal.absNorm (U*K) : ℝ) ≤ 2*B.upper*K₀ := by
  intro U hU K hKs
  refine ⟨(supported_mul_iff U K).mpr ⟨B.repeated_good U hU,(hK K hKs).1⟩,?_⟩
  rw [map_mul,Nat.cast_mul]
  calc
    _ ≤ B.upper*(2*K₀) := mul_le_mul (B.repeated_le U hU) (hK K hKs).2.2 (by positivity) B.upper_nonneg
    _ = _ := by ring

theorem weighted_box_bound (ε : ℝ) (hε : 0 < ε) (W : 𝓢(ℝ, ℂ)) (m : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ (B₁ B₂ : ColumnBox) (Ks : Finset Id)
      (K₀ : ℝ), 0 < K₀ →
      (∀ K ∈ Ks, Supported K ∧ K₀ ≤ (Ideal.absNorm K : ℝ) ∧ (Ideal.absNorm K : ℝ) ≤ 2*K₀) →
      ∀ (M : ℝ), 0 < M → ∀ (c : O), c ≠ 0 →
      ∀ (a : Coefficients B₁) (b : Coefficients B₂),
      (boxFamily B₁ B₂ Ks a b W M c)^2 ≤
        (D/(1+M*‖eisEmbedding c‖^2*K₀/(B₁.scale*B₂.scale))^m)^2 *
          ((cost ε hε C B₁ (2*B₂.upper*K₀)*∑ p, ‖a p‖^2)*
            (cost ε hε C B₂ (2*B₁.upper*K₀)*∑ p, ‖b p‖^2)) := by
  obtain ⟨C,D,hC,hD,h⟩ := coherent_weighted_bound ε hε W m
  refine ⟨C,D,hC,hD,?_⟩
  intro B₁ B₂ Ks K₀ hK₀ hK M hM c hc a b
  let x (r : B₁.radical) := Real.log ((Ideal.absNorm r.val : ℝ)/B₁.scale)
  let y (s : B₂.radical) := Real.log ((Ideal.absNorm s.val : ℝ)/B₂.scale)
  let z (k : Ks) := Real.log ((Ideal.absNorm k.val : ℝ)/K₀)
  let H := M*‖eisEmbedding c‖^2*K₀/(B₁.scale*B₂.scale)
  have hB₁ := B₁.scale_pos
  have hB₂ := B₂.scale_pos
  have hu₁ := B₁.upper_nonneg
  have hu₂ := B₂.upper_nonneg
  have hc' : 0 < ‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
  have hH : 0 < H := by dsimp only [H]; positivity
  have hb := h B₁.repeated B₂.repeated Ks B₁.radical B₂.radical
    (2*B₂.upper*K₀) (2*B₁.upper*K₀) (2*B₁.scale) (2*B₂.scale)
    (by positivity) (by positivity) (by positivity) (by positivity)
    B₁.repeated_good B₂.repeated_good
    (product_frequency_geometry B₂ Ks K₀ hK₀ hK) (product_frequency_geometry B₁ Ks K₀ hK₀ hK)
    (fun R hR => ⟨(B₁.radical_good R hR).1,(B₁.radical_good R hR).2,(B₁.radical_bounds R hR).2⟩)
    (fun T hT => ⟨(B₂.radical_good T hT).1,(B₂.radical_good T hT).2,(B₂.radical_bounds T hT).2⟩)
    B₁.residue B₂.residue B₁.radical_ray B₂.radical_ray a b x y z
    (fun r => log_ratio_bound _ _ hB₁ (B₁.radical_bounds r.val r.property).1 (B₁.radical_bounds r.val r.property).2)
    (fun s => log_ratio_bound _ _ hB₂ (B₂.radical_bounds s.val s.property).1 (B₂.radical_bounds s.val s.property).2)
    (fun k => log_ratio_bound _ _ hK₀ (hK k.val k.property).2.1 (hK k.val k.property).2.2) H hH
  have he (k : Ks) (r : B₁.radical) (s : B₂.radical) :
      H*Real.exp (z k-x r-y s) =
        M*‖eisEmbedding c‖^2*(Ideal.absNorm k.val : ℝ)/
          ((Ideal.absNorm r.val : ℝ)*(Ideal.absNorm s.val : ℝ)) := by
    exact radial_log_identity _ _ _ _ _ _ _ _ hK₀ hB₁ hB₂
      (hB₁.trans_le (B₁.radical_bounds r.val r.property).1)
      (hB₂.trans_le (B₂.radical_bounds s.val s.property).1)
      (hK₀.trans_le (hK k.val k.property).2.1)
  simp_rw [he] at hb
  exact hb

open SieveDualGeometry SieveColumnGeometry SieveCoupling SievePairPoisson

/-- The dual Poisson family on fixed finite labels is bounded by the
already estimated cross-family. Both original coefficient vectors and
their canonical column support are preserved exactly. -/
theorem actual_family_le_box {n m : Type*} [Fintype n] [Fintype m]
    (cols : n → Id) (cols' : m → Id)
    (hc : ∀ i, Supported (cols i)) (hc' : ∀ j, Supported (cols' j))
    (hf : ∀ i, PowerFree 6 (cols i)) (hf' : ∀ j, PowerFree 6 (cols' j))
    (B₁ B₂ : ColumnBox)
    (hU : ∀ i, sharp (cols i) ∈ B₁.repeated) (hR : ∀ i, (cols i).radical ∈ B₁.radical)
    (hV : ∀ j, sharp (cols' j) ∈ B₂.repeated) (hT : ∀ j, (cols' j).radical ∈ B₂.radical)
    (l₁ l₂ : SieveRayCoupling.Label)
    (hl₁ : ∀ i, SieveRayCoupling.label (cols i) (hc i) = l₁)
    (hl₂ : ∀ j, SieveRayCoupling.label (cols' j) (hc' j) = l₂)
    (Ks : Finset Id) (hKs : ∀ K ∈ Ks, Supported K)
    (a : n → ℂ) (b : m → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (c : O) :
    (∑ k : Ks, ‖∑ i, ∑ j, if IsCoprime (cols i) (cols' j) then
      dualTerm (cols i) (cols' j) (hc i) (hc' j) (a i) (b j) W M (c*primaryGenerator k.val) else 0‖) ≤
      boxFamily B₁ B₂ Ks
        (coefficients cols B₁.repeated B₁.radical hU hR (fun i => dualCoefficient (cols i) (hc i) (a i) c))
        (coefficients cols' B₂.repeated B₂.radical hV hT (fun j => dualCoefficient (cols' j) (hc' j) (b j) c))
        W M c := by
  let A (i : n) := dualCoefficient (cols i) (hc i) (a i) c
  let B (j : m) := dualCoefficient (cols' j) (hc' j) (b j) c
  let a' := coefficients cols B₁.repeated B₁.radical hU hR A
  let b' := coefficients cols' B₂.repeated B₂.radical hV hT B
  let F (k : Ks) (U V R T : Id) : ℂ :=
    if IsCoprime R T then crossKernel U V R T k.val *
      paperRadialFourier W (M*‖eisEmbedding c‖^2*(Ideal.absNorm k.val : ℝ)/
        ((Ideal.absNorm R : ℝ)*(Ideal.absNorm T : ℝ))) else 0
  have he (k : Ks) :
      (∑ i, ∑ j, if IsCoprime (cols i) (cols' j) then
        dualTerm (cols i) (cols' j) (hc i) (hc' j) (a i) (b j) W M (c*primaryGenerator k.val) else 0) =
      SieveRayCoupling.eta l₁ l₂ *
        (∑ p : ↥B₁.repeated × ↥B₁.radical, ∑ q : ↥B₂.repeated × ↥B₂.radical,
          star (a' p)*b' q*F k p.1.val q.1.val p.2.val q.2.val) := by
    rw [coefficients_pair cols cols' B₁.repeated B₂.repeated B₁.radical B₂.radical hU hR hV hT A B (F k)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : IsCoprime (cols i) (cols' j)
    · have hr := (coprime_radicals_iff (cols i) (cols' j)).mpr h
      rw [ite_eq_left h,dualTerm_cross _ _ _ (hc i) (hc' j) (hKs _ k.property) (hf i) (hf' j) h,
        hl₁ i,hl₂ j]
      simp only [F,ite_eq_left hr,A,B]
      ring
    · have hr : ¬IsCoprime (cols i).radical (cols' j).radical := fun h' =>
        h ((coprime_radicals_iff (cols i) (cols' j)).mp h')
      simp only [ite_eq_right h,F,ite_eq_right hr,mul_zero]
  have ht := blocks_triangle
    (fun (k : Ks) (p : ↥B₁.repeated × ↥B₁.radical) (q : ↥B₂.repeated × ↥B₂.radical) =>
      star (a' p)*b' q*F k p.1.val q.1.val p.2.val q.2.val)
  have hi : (∑ k : Ks, ‖∑ i, ∑ j, if IsCoprime (cols i) (cols' j) then
      dualTerm (cols i) (cols' j) (hc i) (hc' j) (a i) (b j) W M (c*primaryGenerator k.val) else 0‖) ≤
      ∑ k : Ks, ‖∑ p : ↥B₁.repeated × ↥B₁.radical, ∑ q : ↥B₂.repeated × ↥B₂.radical,
        star (a' p)*b' q*F k p.1.val q.1.val p.2.val q.2.val‖ := by
    apply Finset.sum_le_sum
    intro k _
    rw [he,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (SieveRayCoupling.eta_norm_le l₁ l₂)
  apply (hi.trans ht).trans_eq
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : IsCoprime r.val s.val <;> simp only [F,h,ite_true,ite_false,zero_mul,mul_zero]
  ring

/-- Finite geometric location and injectivity of an actual column family.
No moment estimate or large-sieve assumption is a field of this structure. -/
structure Location {n : Type*} (B : ColumnBox) (cols : n → Id) where
  supported : ∀ i, Supported (cols i)
  free : ∀ i, PowerFree 6 (cols i)
  injective : Function.Injective cols
  repeated_mem : ∀ i, sharp (cols i) ∈ B.repeated
  radical_mem : ∀ i, (cols i).radical ∈ B.radical
  label : SieveRayCoupling.Label
  labels : ∀ i, SieveRayCoupling.label (cols i) (supported i) = label

def locatedCoefficients {n : Type*} [Fintype n] (B : ColumnBox) (cols : n → Id)
    (h : Location B cols) (a : n → ℂ) (c : O) : Coefficients B :=
  coefficients cols B.repeated B.radical h.repeated_mem h.radical_mem
    (fun i => dualCoefficient (cols i) (h.supported i) (a i) c)

theorem locatedCoefficients_mass {n : Type*} [Fintype n] (B : ColumnBox) (cols : n → Id)
    (h : Location B cols) (a : n → ℂ) (c : O) :
    (∑ p, ‖locatedCoefficients B cols h a c p‖^2) ≤ (1/B.scale)*∑ i, ‖a i‖^2 := by
  unfold locatedCoefficients
  rw [coefficients_mass cols h.injective h.supported]
  exact dualCoefficient_family_mass cols h.supported h.free a c B.scale B.scale_pos
    (fun i => (B.radical_bounds (cols i).radical (h.radical_mem i)).1)

theorem cost_nonneg (ε : ℝ) (hε : 0 < ε) (C : ℝ) (hC : 0 ≤ C) (B : ColumnBox)
    (L : ℝ) (hL : 0 ≤ L) : 0 ≤ cost ε hε C B L := by
  have hs := B.scale_pos
  have hl := SieveRanges.lambda_nonneg L (2*B.scale)
  have hc := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  dsimp only [cost]
  positivity

/-- A complete uniform bound for the actual dual family in one geometric
box, expressed in the original coefficient masses. The only norms on the
right are the concrete completed norms lambda, not unproved sieve bounds. -/
theorem actual_box_bound (ε : ℝ) (hε : 0 < ε) (W : 𝓢(ℝ, ℂ)) (d : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
      ∀ {n m : Type*} [Fintype n] [Fintype m] (B₁ B₂ : ColumnBox)
        (cols : n → Id) (cols' : m → Id) (h₁ : Location B₁ cols) (h₂ : Location B₂ cols')
        (Ks : Finset Id) (K₀ : ℝ), 0 < K₀ →
        (∀ K ∈ Ks, Supported K ∧ K₀ ≤ (Ideal.absNorm K : ℝ) ∧ (Ideal.absNorm K : ℝ) ≤ 2*K₀) →
        ∀ (M : ℝ), 0 < M → ∀ (c : O), c ≠ 0 → ∀ (a : n → ℂ) (b : m → ℂ),
        (∑ k : Ks, ‖∑ i, ∑ j, if IsCoprime (cols i) (cols' j) then
          dualTerm (cols i) (cols' j) (h₁.supported i) (h₂.supported j) (a i) (b j)
            W M (c*primaryGenerator k.val) else 0‖)^2 ≤
        (D/(1+M*‖eisEmbedding c‖^2*K₀/(B₁.scale*B₂.scale))^d)^2 *
          ((cost ε hε C B₁ (2*B₂.upper*K₀)/B₁.scale*∑ i, ‖a i‖^2)*
            (cost ε hε C B₂ (2*B₁.upper*K₀)/B₂.scale*∑ j, ‖b j‖^2)) := by
  obtain ⟨C,D,hC,hD,h⟩ := weighted_box_bound ε hε W d
  refine ⟨C,D,hC,hD,?_⟩
  intro n m _ _ B₁ B₂ cols cols' h₁ h₂ Ks K₀ hK₀ hKs M hM c hc a b
  let a' := locatedCoefficients B₁ cols h₁ a c
  let b' := locatedCoefficients B₂ cols' h₂ b c
  have hb := actual_family_le_box cols cols' h₁.supported h₂.supported h₁.free h₂.free
    B₁ B₂ h₁.repeated_mem h₁.radical_mem h₂.repeated_mem h₂.radical_mem
    h₁.label h₂.label h₁.labels h₂.labels Ks (fun K hK => (hKs K hK).1) a b W M c
  have hp := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hb 2
  have hbox := h B₁ B₂ Ks K₀ hK₀ hKs M hM c hc a' b'
  have hA := locatedCoefficients_mass B₁ cols h₁ a c
  have hB := locatedCoefficients_mass B₂ cols' h₂ b c
  have hu₁ := B₁.upper_nonneg
  have hu₂ := B₂.upper_nonneg
  have hs₁ := B₁.scale_pos
  have hs₂ := B₂.scale_pos
  have hc₁ := cost_nonneg ε hε C hC.le B₁ (2*B₂.upper*K₀) (by positivity)
  have hc₂ := cost_nonneg ε hε C hC.le B₂ (2*B₁.upper*K₀) (by positivity)
  have hleft : cost ε hε C B₁ (2*B₂.upper*K₀)*(∑ p, ‖a' p‖^2) ≤
      cost ε hε C B₁ (2*B₂.upper*K₀)/B₁.scale*(∑ i, ‖a i‖^2) :=
    (mul_le_mul_of_nonneg_left hA hc₁).trans_eq (by ring)
  have hright : cost ε hε C B₂ (2*B₁.upper*K₀)*(∑ p, ‖b' p‖^2) ≤
      cost ε hε C B₂ (2*B₁.upper*K₀)/B₂.scale*(∑ i, ‖b i‖^2) :=
    (mul_le_mul_of_nonneg_left hB hc₂).trans_eq (by ring)
  apply (hp.trans hbox).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact mul_le_mul hleft hright (by positivity) (by positivity)

end
end Candidate.SilPrior.FourthPower.SieveBoxFamily
