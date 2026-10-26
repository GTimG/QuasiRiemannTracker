import Candidate.Cycle63.Density.ActualZeros
import Candidate.Cycle63.Marked.DeletionAnnular

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Deletion26
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open LocalMoment ConcretePrimeRowBridge
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- Exact weighted sixth-power decomposition. -/
theorem raw_sixth_weighted_sum (R : Finset NonzeroFrequency)
    (f : NonzeroFrequency → ℝ) :
    (∑h∈R,f h) = ∑B∈(sixthPairs R).image Prod.snd,
      ∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B)) := by
  have hp : (∑p∈sixthPairs R,f (sixthFrequencyEquiv p)) = ∑h∈R,f h := by
    rw [sixthPairs,Finset.sum_image]
    · simp only [Equiv.apply_symm_apply]
    · exact fun _ _ _ _ h=>sixthFrequencyEquiv.symm.injective h
  rw [←hp,←Finset.sum_fiberwise_of_maps_to
    (s:=sixthPairs R) (t:=(sixthPairs R).image Prod.snd) (g:=Prod.snd)
    (fun p hp=>Finset.mem_image.mpr ⟨p,hp,rfl⟩)]
  apply Finset.sum_congr rfl
  intro B hB
  rw [sixthFreeFiber,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    exact congrArg (fun q=>f (sixthFrequencyEquiv q))
      (Prod.ext rfl (Finset.mem_filter.mp hp).2)
  · intro p hp q hq he
    exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)

/-- A uniform ideal tail bound, with the full power beyond the pole at one.
The constant is independent of the varying density exponent. -/
theorem ideal_sixth_tail_uniform (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀(ρ X : ℝ),1+ε≤6*ρ → 1≤X →
      ∀S : Finset NZIdeal,(∀B∈S,X≤(B.val.absNorm : ℝ)) →
        (∑B∈S,(B.val.absNorm : ℝ)^(-6*ρ)) ≤ D*X^(-(6*ρ-1-ε)) := by
  let w : NZIdeal → ℝ := fun B=>(B.val.absNorm : ℝ)^(-(1+ε))
  have hw : Summable w := by
    convert ideal_sixth_power_summable ((1+ε)/6) (by linarith) using 1
    funext B
    dsimp [w]
    congr 1
    ring
  have hw0 (B : NZIdeal) : 0≤w B := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let D : ℝ := (∑'B:NZIdeal,w B)+1
  have hsum : 0≤∑'B:NZIdeal,w B := tsum_nonneg hw0
  refine ⟨D,by dsimp [D];linarith,?_⟩
  intro ρ X hρ hX S hS
  have hXp : 0<X := zero_lt_one.trans_le hX
  have hB (B : NZIdeal) : 0<(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hterm (B : NZIdeal) (hmem:B∈S) :
      (B.val.absNorm : ℝ)^(-6*ρ) ≤ w B*X^(-(6*ρ-1-ε)) := by
    have he : -6*ρ = -(1+ε)+ -(6*ρ-1-ε) := by ring
    rw [he,Real.rpow_add (hB B)]
    apply mul_le_mul_of_nonneg_left _ (hw0 B)
    exact Real.rpow_le_rpow_of_nonpos hXp (hS B hmem) (by linarith)
  calc
    _ ≤ ∑B∈S,w B*X^(-(6*ρ-1-ε)) := Finset.sum_le_sum hterm
    _ = (∑B∈S,w B)*X^(-(6*ρ-1-ε)) := by rw [Finset.sum_mul]
    _ ≤ (∑'B:NZIdeal,w B)*X^(-(6*ρ-1-ε)) :=
      mul_le_mul_of_nonneg_right (hw.sum_le_tsum _ (fun B _=>hw0 B))
        (Real.rpow_nonneg hXp.le _)
    _ ≤ D*X^(-(6*ρ-1-ε)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hXp.le _)
      dsimp [D]
      linarith

/-- A marked free-row estimate is needed only below the root cutoff.
Beyond it the ordinary density and pointwise slot envelope suffice. -/
theorem raw_marked_split_lift (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀(U C ρ κ A gain : ℝ),1≤U → 0≤C → 0≤κ →
      1+ε≤6*ρ → ∀(R : Finset NonzeroFrequency)(f : NonzeroFrequency→ℝ),
      (∀B : NZIdeal, (B.val.absNorm : ℝ)≤U^κ →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          C*U^(A-gain)*(U/(B.val.absNorm : ℝ)^6)^ρ) →
      (∀B : NZIdeal, U^κ<(B.val.absNorm : ℝ) →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          C*U^A*(U/(B.val.absNorm : ℝ)^6)^ρ) →
      (∑h∈R,f h) ≤ C*D*U^(ρ+A-min gain (κ*(6*ρ-1-ε))) := by
  obtain ⟨D,hD,htail⟩ := ideal_sixth_tail_uniform ε hε
  refine ⟨2*D,by positivity,?_⟩
  intro U C ρ κ A gain hU hC hκ hρ R f hsmall hlarge
  have hUp : 0<U := zero_lt_one.trans_le hU
  let S := (sixthPairs R).image Prod.snd
  let S₀ := S.filter (fun B=>(B.val.absNorm : ℝ)≤U^κ)
  let S₁ := S.filter (fun B=>¬(B.val.absNorm : ℝ)≤U^κ)
  have hBone (B : NZIdeal) : 1≤(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hBpos (B : NZIdeal) : 0<(B.val.absNorm : ℝ) := zero_lt_one.trans_le (hBone B)
  have hsum₀ := htail ρ 1 hρ le_rfl S₀ (fun B _=>hBone B)
  rw [Real.one_rpow,mul_one] at hsum₀
  have hsum₁ := htail ρ (U^κ) hρ (Real.one_le_rpow hU hκ) S₁
    (fun B hB=>(lt_of_not_ge (Finset.mem_filter.mp hB).2).le)
  have hpart : (∑h∈R,f h) =
      (∑B∈S₀,∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B)))+
      (∑B∈S₁,∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) := by
    rw [raw_sixth_weighted_sum]
    exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have hb₀ : (∑B∈S₀,∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
      C*D*U^(ρ+A-gain) := by
    calc
      _ ≤ ∑B∈S₀,C*U^(A-gain)*(U/(B.val.absNorm : ℝ)^6)^ρ :=
        Finset.sum_le_sum (fun B hB=>hsmall B (Finset.mem_filter.mp hB).2)
      _ = (C*U^(ρ+A-gain))*(∑B∈S₀,(B.val.absNorm : ℝ)^(-6*ρ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        rw [sixth_window_power U _ ρ hUp (hBpos B)]
        rw [show ρ+A-gain = (A-gain)+ρ by ring,Real.rpow_add hUp]
        ring
      _ ≤ (C*U^(ρ+A-gain))*D := mul_le_mul_of_nonneg_left hsum₀ (by positivity)
      _ = _ := by ring
  have hb₁ : (∑B∈S₁,∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
      C*D*U^(ρ+A-κ*(6*ρ-1-ε)) := by
    calc
      _ ≤ ∑B∈S₁,C*U^A*(U/(B.val.absNorm : ℝ)^6)^ρ :=
        Finset.sum_le_sum (fun B hB=>hlarge B (lt_of_not_ge (Finset.mem_filter.mp hB).2))
      _ = (C*U^(ρ+A))*(∑B∈S₁,(B.val.absNorm : ℝ)^(-6*ρ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B hB
        rw [sixth_window_power U _ ρ hUp (hBpos B),Real.rpow_add hUp]
        ring
      _ ≤ (C*U^(ρ+A))*(D*(U^κ)^(-(6*ρ-1-ε))) :=
        mul_le_mul_of_nonneg_left hsum₁ (by positivity)
      _ = C*D*(U^(ρ+A)*(U^κ)^(-(6*ρ-1-ε))) := by ring
      _ = _ := by
        congr 1
        rw [←Real.rpow_mul hUp.le,←Real.rpow_add hUp]
        congr 1
        ring
  rw [hpart]
  have ha₀ : U^(ρ+A-gain)≤U^(ρ+A-min gain (κ*(6*ρ-1-ε))) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith [min_le_left gain (κ*(6*ρ-1-ε))])
  have ha₁ : U^(ρ+A-κ*(6*ρ-1-ε))≤U^(ρ+A-min gain (κ*(6*ρ-1-ε))) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith [min_le_right gain (κ*(6*ρ-1-ε))])
  have hcD : 0≤C*D := mul_nonneg hC hD.le
  calc
    _ ≤ C*D*U^(ρ+A-gain)+C*D*U^(ρ+A-κ*(6*ρ-1-ε)) := add_le_add hb₀ hb₁
    _ ≤ C*D*U^(ρ+A-min gain (κ*(6*ρ-1-ε)))+
          C*D*U^(ρ+A-min gain (κ*(6*ρ-1-ε))) :=
      add_le_add (mul_le_mul_of_nonneg_left ha₀ hcD) (mul_le_mul_of_nonneg_left ha₁ hcD)
    _ = _ := by ring

end
end OAI.SevenEighths.Deletion26
#print axioms OAI.SevenEighths.Deletion26.raw_marked_split_lift
