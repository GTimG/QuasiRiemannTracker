/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The H23 retained-long fourth uses repetitions of one actual attaining native
descriptor, on the original flagged regular rows. -/
import Candidate.C092.transport.CofactorIndependentMarked

namespace QRH.Cycle092.MediumInversePrice
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip QRH.Cycle092.CofactorOrdinary
local notation "O" => ActualEisensteinCubic.O

/-- A real native supplier, including arbitrary fixed repetition counts and
the zero-repeat unmarked face. No moment estimate is an input. -/
theorem repeated_native_fourth
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {N quota Vmin : ℝ} (hN : N ≤ 1/2) (hq0 : 0 ≤ quota)
    (hqcap : quota < 3/20) (hqmean : quota < (1-2*N)/2) (hVmin : 0 < Vmin)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ mesh : ℝ, 0 < mesh ∧ ∀ k : ℕ,
    ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
      (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
    ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ →
      Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ →
    ∀ (η η₀ : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ᶠ U : ℝ in atTop, ∀ V : ℝ, Vmin ≤ V →
    ∀ (θ : RayQuotient.Characters rayM Hr) (w σ v t height e buffer : ℝ),
      0 ≤ w → w/V ≤ mesh → (33/50 : ℝ) ≤ σ → σ ≤ (33/50 : ℝ) →
      0 ≤ height → |v| ≤ height → (k : ℝ)*w ≤ V*quota →
    ∀ (p : Profiles (1/4) (9/4)) (j : Fin 2) (X : ℝ),
      0 < X → length (U^V) X ≤ N →
    ∀ (s : Finset FreeRow),
      (∀ u ∈ s, initialKeep η (internalQ Q η₀) u.val) →
      (∀ u ∈ s, rowNorm u ≤ U^V) →
      (∀ u ∈ s, U^(e*w-buffer) ≤
        ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
          (CenteredMomentPrimeSlot.primePool rayM Hr 2 (U^w))
          (fun I => idealCoeff (relativeCharacter rayM Hr hHr η₀ θ) I *
            HeckePrimeAnnular.annularWeight W (U^w) σ v I) t (U^w)‖^2) →
    (∑ u ∈ s, ‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree*
        U^(V*(1+ε)-(k : ℝ)*(e*w-buffer)) := by
  have hmean : quota < (1-N-N)/2 := by linarith
  obtain ⟨mesh,hm,hsource⟩ := QRH.Cycle092.LowActual.native_mean_box hβ hN hN hq0 hqcap hmean ε hε
  refine ⟨mesh,hm,?_⟩
  intro k rayM _ Hr hHr W hW hWs bΦ hbΦ hsΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hsource⟩ := hsource (Fin k) rayM Hr hHr W hW hWs
    bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degree,controls,C,hC,?_⟩
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp hsource
  have hlarge := (tendsto_rpow_atTop hVmin).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hlarge,eventually_gt_atTop (1 : ℝ)] with U hlarge hU
  intro V hV θ w σ v t height e buffer hw hwm hσlo hσhi hh hv hquota p j X hX hXN s hk hy hamp
  have hVp : 0 < V := hVmin.trans_le hV
  have hUp : 0 < U := zero_lt_one.trans hU
  have hUV : 1 < U^V := Real.one_lt_rpow hU hVp
  have hsrc := hZ₀ (U^V) (hlarge.trans (Real.rpow_le_rpow_of_exponent_le hU.le hV))
  have hbox : Box N N (V*quota) (length (U^V) X) (length (U^V) X)
      (∑ _ : Fin k, w) := by
    refine ⟨length_nonneg _ _ hUV,length_nonneg _ _ hUV,Or.inl ⟨hXN,hXN⟩,?_,?_⟩
    · exact Finset.sum_nonneg (fun _ _ => hw)
    · simpa using hquota
  have hE := labelled_retained_energy rayM Hr hHr hsrc (Finset.univ : Finset (Fin k))
    (fun _ => θ) (fun _ => w) (fun _ => σ) (fun _ => v) t height
    (fun _ => hw) (fun _ => hwm) (fun _ => hσlo) (fun _ => hσhi) hh (fun _ => hv)
    radialMajorant hsΦ radialMajorant_nonneg (repeatedProfile p j) X X hX hX hUp hVp hbox
  rw [repeated_control,←pow_mul] at hE
  have hfinite := finite_selected_energy (Finset.univ : Finset (Fin k)) η
    (fixedBadMask*idealGenerator 1) 1 (p.profile j) (p.profile j)
    (originalPools rayM Hr 2 U (fun _ : Fin k => w))
    (originalCoefficients rayM Hr hHr η₀ (fun _ : Fin k => θ) W U
      (fun _ => w) (fun _ => σ) (fun _ => v)) (fun _ => U^w)
    t X X (9/4) (9/4) (U^V) (fun _ hx => (p.support j hx).2)
    (fun _ hx => (p.support j hx).2) hX hX (fun _ => Real.rpow_pos_of_pos hUp _)
    (Real.rpow_pos_of_pos hUp _) s (initialKeep η (internalQ Q η₀)) hk hy
  have hweighted : U^((k : ℝ)*(e*w-buffer))*
      (∑ u ∈ s, ‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4) ≤
      C*QuadraticInitialBound.diagonalControl radialMajorant*
        (sourceControl controls (p.profile j))^4*(1+|t|+height)^degree*U^(V*(1+ε)) := by
    apply le_trans ?_ (hfinite.trans hE)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro u hu
    have hl := pow_le_pow_left₀ (Real.rpow_pos_of_pos hUp _).le (hamp u hu) k
    rw [←Real.rpow_mul_natCast hUp.le] at hl
    have he : (e*w-buffer)*(k : ℝ)=(k : ℝ)*(e*w-buffer) := mul_comm _ _
    rw [he] at hl
    change U^((k : ℝ)*(e*w-buffer))*
      ‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^4 ≤
      (∏ _ : Fin k, ‖normalizedSlot η (fixedBadMask*idealGenerator 1) 1 u.val
        (CenteredMomentPrimeSlot.primePool rayM Hr 2 (U^w))
        (fun I => idealCoeff (relativeCharacter rayM Hr hHr η₀ θ) I *
          HeckePrimeAnnular.annularWeight W (U^w) σ v I) t (U^w)‖^2)*
      ‖original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X*
        original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X‖^2
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_mul]
    convert mul_le_mul_of_nonneg_right hl
      (pow_nonneg (norm_nonneg (original η (fixedBadMask*idealGenerator 1) 1 u.val (p.profile j) t X)) 4) using 1 <;> ring
  have hden : 0 < U^((k : ℝ)*(e*w-buffer)) := Real.rpow_pos_of_pos hUp _
  rw [Real.rpow_sub hUp,←mul_div_assoc]
  exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hweighted)

#print axioms repeated_native_fourth
end
end QRH.Cycle092.MediumInversePrice
