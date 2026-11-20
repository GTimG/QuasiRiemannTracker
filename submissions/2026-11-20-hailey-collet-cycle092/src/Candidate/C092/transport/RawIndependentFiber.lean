/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Before response classification, open both cofactor holes and the punctured
prime product on the same rows. Each child is exactly a finite two-character
energy at its own shortened lengths and surviving whole slots. -/
import Candidate.C092.transport.StrongPairFinite
import Candidate.C092.transport.CofactorOriginalLift
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion IdealMobiusDivisorSum
open QRH.Cycle092 QRH.Cycle092.OrdinaryColumn QRH.Cycle092.WholeSlot
namespace QRH.Cycle092.RawIndependentFiber
local notation "O" => HeckeFamily.O
local notation "mask₀" => fixedBadMask*idealGenerator 1
local instance c092LocalInst_Candidate_C092_transport_RawIndependentFiber_2e4ea00788d6486e_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem actual_independent_fiber {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (W : ℝ→ℂ) (hW : Continuous W) (hsW : Function.support W ⊆ Set.Icc (1:ℝ) 2)
    (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℝ, 1 ≤ U → ∀ B : NonzeroIdeal, (B.val.absNorm:ℝ) ≤ U^L →
    ∀ (η₁ η₂ ηmark base : Character) (θ : ι → RayQuotient.Characters M H) (w σ v : ι → ℝ)
      (W₁ W₂ : ℝ→ℂ) (t₁ t₂ tMark X₁ X₂ b₁ b₂ K : ℝ) (s : Finset FreeRow),
      (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ σ i) → Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 ≤ K →
      let mark := fun i z => normalizedSlot ηmark mask₀ 1 z (originalPools M H 2 U w i)
        (originalCoefficients M H hH base θ W U w σ v i) tMark (U^(w i))
      (∀ D ∈ idealDivisors B.val,∀ F ∈ idealDivisors B.val,∀ T : Finset ι,
        StrongPair.finiteEnergyOn T s η₁ η₂ W₁ W₂ t₁ t₂ (X₁/(D.absNorm:ℝ)) (X₂/(F.absNorm:ℝ))
          (fun i r => mark i r.val) ≤ K) →
      (∑ z ∈ s,(∏ i, ‖mark i (rowMap (z,B))‖^2) *
        ‖original η₁ mask₀ 1 (rowMap (z,B)) W₁ t₁ X₁ * original η₂ mask₀ 1 (rowMap (z,B)) W₂ t₂ X₂‖^2) ≤ C*U^ε*K := by
  obtain ⟨δ,hδ,hbd⟩ := CofactorOrdinary.total_budget (Fintype.card ι) L ε hL hε
  obtain ⟨J,hJ,hslots⟩ := CofactorPrime.original_cofactor_subpower (Slot:=ι) M H hH W hW hsW δ L hδ hL
  obtain ⟨C,hC,hbudget⟩ := hbd (max 1 J) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro U hU B hB η₁ η₂ ηmark base θ w σ v W₁ W₂ t₁ t₂ tMark X₁ X₂ b₁ b₂ K s hw hσ hs₁ hs₂ hx hy hK
  let mark := fun i z => normalizedSlot ηmark mask₀ 1 z (originalPools M H 2 U w i)
      (originalCoefficients M H hH base θ W U w σ v i) tMark (U^(w i))
  dsimp only
  intro hsrc
  have hLam : goodLambda ∣ mask₀ := (dvd_mul_right _ _ : goodLambda ∣ fixedBadMask).trans (dvd_mul_right _ _)
  have ht : (2:O) ∣ mask₀ := (dvd_mul_left _ _ : (2:O)∣fixedBadMask).trans (dvd_mul_right _ _)
  let E := max 1 J * U^δ
  have hE : 1 ≤ E := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hU hδ.le)
  have hdiff (z : FreeRow) (_hz : z∈s) (i : ι) : ‖mark i (rowMap (z,B))-mark i z.val‖ ≤ E := by
    rw [norm_sub_rev];unfold mark rowMap;rw [mul_comm z.val]
    have h := hslots U hU ηmark base θ w σ v mask₀ 1 (idealGenerator B.val) z.val tMark hw hσ hLam ht
      (idealGenerator_ne_zero _ B.property) (by simpa only [span_idealGenerator] using hB) i
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (zero_le_one.trans hU) _))
  have hr := CofactorOrdinary.pair_energy η₁ η₂ mask₀ 1 1 hLam ht B s
    (fun z => ∏ i,‖mark i (rowMap (z,B))‖^2) (fun _ _ => Finset.prod_nonneg (fun _ _ => sq_nonneg _))
    W₁ W₂ t₁ t₂ b₁ b₂ X₁ X₂ ((2*E^2)^Fintype.card ι*2^Fintype.card ι*K) hs₁ hs₂ hx hy (by
      intro D hD F hF
      apply CofactorOrdinary.weighted_marked_subsets s (fun z i => mark i (rowMap (z,B))) (fun z i => mark i z.val) _ E K hE
        (fun _ _ => sq_nonneg _) hdiff
      intro T
      apply (le_of_eq ?_).trans (hsrc D hD F hF T)
      unfold StrongPair.finiteEnergyOn
      apply Finset.sum_congr rfl
      intro z hz
      dsimp only [mark]; simp only [norm_mul,mul_pow]; ring)
  refine hr.trans ?_
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right (hbudget U hU B hB) hK

#print axioms actual_independent_fiber
end QRH.Cycle092.RawIndependentFiber
end
