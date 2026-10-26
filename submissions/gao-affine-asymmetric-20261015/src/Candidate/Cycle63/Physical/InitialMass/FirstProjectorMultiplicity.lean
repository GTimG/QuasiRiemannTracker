import Candidate.Cycle63.Moment.JointSourceCount
import Candidate.Cycle63.Moment.JointAllocationEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

/-- Only the first projector has this divisor provenance. No divisibility
of the residual second projector is asserted here. -/
theorem actual_first_projector_dvd_joint_row (left : Bool) (u₀ : O)
    (unit : FirstSourceLabel→O) (l : JointSourceLabel) (L : Ideal O)
    (hL : Squarefree L) (hC : Supported l.2.1.1) (hD : l.2.1.2≠0)
    (hLC : L∣l.2.1.1) (hLD : L∣l.2.1.2) :
    L∣Ideal.span {jointSourceRow left u₀ unit l} := by
  have hd := Cycle63.Physical.first_projector_dvd_frequency L _ _ hL hC hD hLC hLD
  apply hd.trans
  obtain ⟨v,hv⟩ := joint_source_second_generator_dvd left u₀ unit l
  rw [hv,←Ideal.span_singleton_mul_span_singleton]
  exact dvd_mul_right _ _

theorem first_projector_small_power (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀Z : ℝ,1≤Z → ∀w : O,w≠0 →
      ((Ideal.span {w}).absNorm:ℝ)≤Z^B → ∀Ls : Finset (Ideal O),
      (∀L∈Ls,Squarefree L) → (∀L∈Ls,L∣Ideal.span {w}) →
      (Ls.card:ℝ)≤K*Z^ε := by
  let δ := ε/(B+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨K,hK,hbound⟩ := SquarefreeDivisorBound.squarefree_divisor_small_power δ hδ
  refine ⟨K,hK,?_⟩
  intro Z hZ w hw hnorm Ls hL hd
  have hN : Ideal.span {w}≠0 := Ideal.span_singleton_eq_bot.not.mpr hw
  have hsub : Ls⊆(idealDivisors (Ideal.span {w})).filter Squarefree := by
    intro L hl
    exact Finset.mem_filter.mpr ⟨(mem_idealDivisors hN).mpr (hd L hl),hL L hl⟩
  have hc : (Ls.card:ℝ)≤((idealDivisors (Ideal.span {w})).filter Squarefree).card := by
    exact_mod_cast Finset.card_le_card hsub
  have he : B*δ≤ε := by
    have hid : δ*(B+1)=ε := by dsimp [δ]; field_simp
    nlinarith
  calc
    _≤K*((Ideal.span {w}).absNorm:ℝ)^δ := hc.trans (hbound _ hN)
    _≤K*(Z^B)^δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hδ.le) hK.le
    _=K*Z^(B*δ) := by rw [←Real.rpow_mul (zero_le_one.trans hZ)]
    _≤K*Z^ε := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ he) hK.le

/-- Repeated first-projector labels cost only the divisor small power.
The selected energy estimate is still a single joint row estimate. -/
theorem actual_first_projector_joint_selection (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀Z : ℝ,1≤Z → ∀{Label : Type*}[Fintype Label]
      (row : Label→O) (Ls : Label→Finset (Ideal O))
      (cost : (l : Label)→Ls l→ℝ) (E : ℝ),
      (∀l,row l≠0) → (∀l,((Ideal.span {row l}).absNorm:ℝ)≤Z^B) →
      (∀l,Ls l⊆(idealDivisors (Ideal.span {row l})).filter Squarefree) →
      (∀l L,0≤cost l L) →
      (∀S : Finset Label,∀pick : (l : S)→Ls l.val,(∑l : S,cost l.val (pick l))≤E) →
      (∑l,∑L : Ls l,cost l L)≤(K*Z^ε)*E := by
  obtain ⟨K,hK,hbound⟩ := first_projector_small_power B ε hB hε
  refine ⟨K,hK,?_⟩
  intro Z hZ Label _ row Ls cost E hrow hnorm hLs hc he
  have hh := joint_weighted_selection (fun l (_L : Ls l)=>(1:ℝ)) cost (K*Z^ε) E
    (mul_nonneg hK.le (Real.rpow_nonneg (zero_le_one.trans hZ) _))
    (fun _ _=>zero_le_one) hc ?_ he
  · simpa only [one_mul] using hh
  intro l
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,mul_one]
  exact hbound Z hZ (row l) (hrow l) (hnorm l) (Ls l)
    (fun L hL=>(Finset.mem_filter.mp (hLs l hL)).2)
    (fun L hL=>(mem_idealDivisors (Ideal.span_singleton_eq_bot.not.mpr (hrow l))).mp
      (Finset.mem_filter.mp (hLs l hL)).1)

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_projector_dvd_joint_row
#print axioms OAI.SevenEighths.Cycle63InitialMass.first_projector_small_power
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_first_projector_joint_selection
