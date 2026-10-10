import Cycle25.Numerator.Imported.RowConductor
import OAI.NumberTheory.DirichletL.PrimeRows.RowCount

noncomputable section
set_option maxHeartbeats 800000
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.Numerator.PhysicalTail
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open CenteredMomentUniformReflectionApproximation CenteredMomentNaturalPrimitive
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectionMass
local notation "O" => HeckeFamily.O

/-- The exact coefficient cutoff bounds every discarded dual length uniformly.
Neither a scale-bin assumption nor a pointwise critical-line L-bound is needed. -/
theorem discardedSchwartz_active_negligible (xi saving epsilon b Ccond : ℝ)
    (hxi : 0<xi) (heps : 0<epsilon) (hb : 0<b) (hCcond : 0<Ccond) :
    ∃H : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀(τ ψ : Character)(G : 𝓢(ℝ,ℂ))(Y N U : ℝ),
      0<Y → 0<N → N≤b*Y → 1≤U →
      (ψ.modulus.absNorm:ℝ)*(redundantIdeal τ.modulus ψ.modulus).absNorm≤Ccond*U →
      ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤
        C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*U^(epsilon-saving) := by
  obtain ⟨H,C,hC,hbound⟩ := deleted_discarded_negligible xi saving 1 (b*Ccond) epsilon
    hxi (mul_pos hb hCcond) heps
  refine ⟨H,C*Ccond^epsilon,by positivity,?_⟩
  intro τ ψ G Y N U hY hN hcut hU hcap
  let S := redundantSet τ.modulus ψ.modulus
  have hS : ∀P∈S,Prime P := redundantSet_prime _ _
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hQone : (1:ℝ)≤ψ.modulus.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hnorm : (Ideal.absNorm (∏P∈S,P):ℝ)≤Ccond*U := by
    have hr : 0≤(Ideal.absNorm (∏P∈S,P):ℝ) := by positivity
    have hl := mul_le_mul_of_nonneg_right hQone hr
    exact (show (Ideal.absNorm (∏P∈S,P):ℝ)≤(ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ) by simpa only [one_mul] using hl).trans hcap
  have hYX : 1≤b*(Y/N) := by
    rw [←mul_div_assoc,le_div_iff₀ hN]
    simpa using hcut
  have hscale : (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈S,P):ℝ)≤
      (b*Ccond)*U^(1:ℝ)*(Y/N) := by
    calc
      _ ≤ Ccond*U := hcap
      _ ≤ (Ccond*U)*(b*(Y/N)) := le_mul_of_one_le_right (by positivity) hYX
      _ = _ := by rw [Real.rpow_one];ring
  have hh := (hbound G S hS ψ ψ.inverse τ.inverse (ψ.modulus.absNorm:ℝ) (Y/N) U
    hU hQ (div_pos hY hN) hscale).2
  change ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤_ at hh
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  have hU0 : 0<U := zero_lt_one.trans_le hU
  calc
    _ ≤ C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*
        (Ideal.absNorm (∏P∈S,P):ℝ)^epsilon*U^(-saving) := hh
    _ ≤ C*H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G*(Ccond*U)^epsilon*U^(-saving) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow hCcond.le hU0.le,Real.rpow_sub hU0]
      rw [Real.rpow_neg hU0.le]
      ring


/-- Once the physical profile is fixed, the complete discarded packet has an
arbitrary inverse-power bound at every active coefficient scale. -/
theorem discardedSchwartz_fixed_profile (xi saving b Ccond : ℝ)
    (hxi : 0<xi) (hb : 0<b) (hCcond : 0<Ccond) (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0<C ∧ ∀(τ ψ : Character)(Y N U : ℝ),
      0<Y → 0<N → N≤b*Y → 1≤U →
      (ψ.modulus.absNorm:ℝ)*(redundantIdeal τ.modulus ψ.modulus).absNorm≤Ccond*U →
      ‖discardedSchwartz τ ψ G (Y/N) (U^(xi/2))‖≤C*U^(-saving) := by
  obtain ⟨H,C,hC,hbound⟩ := discardedSchwartz_active_negligible xi (saving+1) 1 b Ccond
    hxi (by norm_num) hb hCcond
  have hG : 0≤H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G := apply_nonneg _ _
  refine ⟨C*(H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G+1),by positivity,?_⟩
  intro τ ψ Y N U hY hN hcut hU hcap
  have hh := hbound τ ψ G Y N U hY hN hcut hU hcap
  rw [show (1:ℝ)-(saving+1) = -saving by ring] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G≤
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) G+1) hC.le) (by positivity))

lemma fourth_norm_add (a b : ℂ) : ‖a+b‖^4≤8*(‖a‖^4+‖b‖^4) := by
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 4).trans
    (by convert add_pow_le (norm_nonneg a) (norm_nonneg b) 4 using 1 <;> norm_num)

theorem weighted_fourth_add {ι : Type*} (s : Finset ι) (R T Q : ι→ℂ) (Er Et : ℝ)
    (hr : (∑i∈s,‖R i‖^4*‖Q i‖^2)≤Er)
    (ht : (∑i∈s,‖T i‖^4*‖Q i‖^2)≤Et) :
    (∑i∈s,‖R i+T i‖^4*‖Q i‖^2)≤8*(Er+Et) := by
  calc
    _ ≤ ∑i∈s,8*(‖R i‖^4+‖T i‖^4)*‖Q i‖^2 :=
      Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (fourth_norm_add _ _) (sq_nonneg _))
    _ = 8*((∑i∈s,‖R i‖^4*‖Q i‖^2)+(∑i∈s,‖T i‖^4*‖Q i‖^2)) := by
      simp only [Finset.mul_sum,Finset.sum_add_distrib,add_mul,mul_add]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
    _ ≤ _ := by linarith

/-- Polynomial pointwise tails are negligible even with all selected factors. -/
theorem selected_tail_fourth {ι : Type*} (s : Finset ι) (T Q : ι→ℂ)
    (U r q saving Ccard Ctail Cslot : ℝ) (hU : 0<U)
    (hc : 0≤Ccard) (ht : 0≤Ctail) (hq : 0≤Cslot)
    (hcard : (s.card:ℝ)≤Ccard*U^r)
    (htail : ∀i∈s,‖T i‖≤Ctail*U^(-saving))
    (hslot : ∀i∈s,‖Q i‖≤Cslot*U^q) :
    (∑i∈s,‖T i‖^4*‖Q i‖^2)≤Ccard*Ctail^4*Cslot^2*U^(r+2*q-4*saving) := by
  calc
    _ ≤ ∑i∈s,(Ctail*U^(-saving))^4*(Cslot*U^q)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (htail i hi) 4)
        (pow_le_pow_left₀ (norm_nonneg _) (hslot i hi) 2) (sq_nonneg _) (by positivity)
    _ = (s.card:ℝ)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) := by simp
    _ ≤ (Ccard*U^r)*((Ctail*U^(-saving))^4*(Cslot*U^q)^2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hpow (e : ℝ) (n : ℕ) : (U^e)^n=U^(e*n) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hU.le]
      rw [mul_pow,mul_pow,hpow,hpow]
      calc
        _ = Ccard*Ctail^4*Cslot^2*(U^r*U^(-saving*4)*U^(q*2)) := by ring
        _ = _ := by rw [←Real.rpow_add hU,←Real.rpow_add hU];congr 2;ring


/-- The crude lattice count alone suffices for all discarded selected moments;
its constant is independent of any source-moment constant C0. -/
theorem row_discarded_fourth_negligible (xi saving q b Ccond Cslot : ℝ)
    (hxi : 0<xi) (hb : 0<b) (hCcond : 0<Ccond) (hslot0 : 0<Cslot)
    (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0<C ∧ ∀(rows : Finset FreeRow)(τ ψ : FreeRow→Character)
      (N : FreeRow→ℝ)(Q : FreeRow→ℂ)(Y U : ℝ),
      0<Y → 1≤U → (∀u∈rows,0<N u ∧ N u≤b*Y) →
      (∀u∈rows,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤U) →
      (∀u∈rows,((ψ u).modulus.absNorm:ℝ)*
        (redundantIdeal (τ u).modulus (ψ u).modulus).absNorm≤Ccond*U) →
      (∀u∈rows,‖Q u‖≤Cslot*U^q) →
      (∑u∈rows,‖discardedSchwartz (τ u) (ψ u) G (Y/N u) (U^(xi/2))‖^4*‖Q u‖^2)≤C*U^(-saving) := by
  let s : ℝ := (1+2*q+saving)/4
  obtain ⟨C,hC,hbound⟩ := discardedSchwartz_fixed_profile xi s b Ccond hxi hb hCcond G
  refine ⟨128*C^4*Cslot^2,by positivity,?_⟩
  intro rows τ ψ N Q Y U hY hU hN hrows hcap hslot
  have hh := selected_tail_fourth rows
    (fun u=>discardedSchwartz (τ u) (ψ u) G (Y/N u) (U^(xi/2))) Q
    U 1 q s 128 C Cslot (zero_lt_one.trans_le hU) (by norm_num) hC.le hslot0.le
    (by simpa using ProbeHighRowFamily.freeRow_count rows U hU hrows)
    (fun u hu=>hbound (τ u) (ψ u) Y (N u) U hY (hN u hu).1 (hN u hu).2 hU (hcap u hu)) hslot
  convert hh using 1
  dsimp only [s]
  congr 2
  ring


theorem subtype_discarded_fourth_negligible (xi saving q b Ccond Cslot : ℝ)
    (hxi : 0<xi) (hb : 0<b) (hCcond : 0<Ccond) (hslot0 : 0<Cslot)
    (G : 𝓢(ℝ,ℂ)) :
    ∃C : ℝ,0<C ∧ ∀(rows : Finset FreeRow)(τ ψ : rows→Character)
      (N : rows→ℝ)(Q : rows→ℂ)(Y U : ℝ),
      0<Y → 1≤U → (∀i,0<N i ∧ N i≤b*Y) →
      (∀u∈rows,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤U) →
      (∀i,((ψ i).modulus.absNorm:ℝ)*
        (redundantIdeal (τ i).modulus (ψ i).modulus).absNorm≤Ccond*U) →
      (∀i,‖Q i‖≤Cslot*U^q) →
      (∑i:rows,‖discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/2))‖^4*‖Q i‖^2)≤C*U^(-saving) := by
  let s : ℝ := (1+2*q+saving)/4
  obtain ⟨C,hC,hbound⟩ := discardedSchwartz_fixed_profile xi s b Ccond hxi hb hCcond G
  refine ⟨128*C^4*Cslot^2,by positivity,?_⟩
  intro rows τ ψ N Q Y U hY hU hN hrows hcap hslot
  have hh := selected_tail_fourth Finset.univ
    (fun i:rows=>discardedSchwartz (τ i) (ψ i) G (Y/N i) (U^(xi/2))) Q
    U 1 q s 128 C Cslot (zero_lt_one.trans_le hU) (by norm_num) hC.le hslot0.le
    (by simpa using ProbeHighRowFamily.freeRow_count rows U hU hrows)
    (fun i _=>hbound (τ i) (ψ i) Y (N i) U hY (hN i).1 (hN i).2 hU (hcap i))
    (fun i _=>hslot i)
  convert hh using 1
  dsimp only [s]
  congr 2
  ring

/-- Exact unit-modulus reflection transfers the retained weighted fourth moment
to the original polynomial, with a separately certified tail contribution. -/
theorem original_split_weighted_fourth {ι : Type*} (s : Finset ι)
    (P R T g Q : ι→ℂ) (D : ι→ℝ) (Er Et : ℝ)
    (hD : ∀i∈s,1≤D i) (hg : ∀i∈s,‖g i‖=1)
    (heq : ∀i∈s,P i=g i*(R i+T i))
    (hr : (∑i∈s,‖R i/(D i:ℂ)‖^4*‖Q i‖^2)≤Er)
    (ht : (∑i∈s,‖T i‖^4*‖Q i‖^2)≤Et) :
    (∑i∈s,‖P i/(D i:ℂ)‖^4*‖Q i‖^2)≤8*(Er+Et) := by
  have htail : (∑i∈s,‖T i/(D i:ℂ)‖^4*‖Q i‖^2)≤Et := by
    apply (Finset.sum_le_sum (fun i hi=>?_)).trans ht
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (hD i hi))]
    exact div_le_self (norm_nonneg _) (hD i hi)
  have hnorm (i : ι) (hi : i∈s) : ‖P i/(D i:ℂ)‖=‖R i/(D i:ℂ)+T i/(D i:ℂ)‖ := by
    rw [heq i hi,mul_div_assoc,norm_mul,hg i hi,one_mul,add_div]
  simp_rw [Finset.sum_congr rfl (fun i hi=>congrArg (fun t : ℝ=>t^4*‖Q i‖^2) (hnorm i hi))]
  exact weighted_fourth_add s (fun i=>R i/(D i:ℂ)) (fun i=>T i/(D i:ℂ)) Q Er Et hr htail

end Cycle25.Weighted.Numerator.PhysicalTail
end

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 keeps the original physical family and explicit variable-kappa capacity. -/
