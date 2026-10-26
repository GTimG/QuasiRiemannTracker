/- Actual ordinary sixth-root fibers adapted from PR63 Target830/Marked/RawOrdinary.lean, Apache-2.0. Reuses existing checked Cycle61 density at its exact lower boundary33/40; the endpointHIGH range lies inside this boundary. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.RootCompletion
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Density.ActualZeros

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Record12518109GainActualRoot
noncomputable section
open scoped Classical BigOperators
open Set Filter HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open LocalMoment ConcretePrimeRowBridge Record12518109GainRoot
open Record12518109Gain
local notation "NZIdeal" => HeckeInverseAmplification.NonzeroIdeal

/-- The fixed inducing exceptions inside a natural-core fiber are paid by
the same full gain. Their finite cardinality is independent of the root. -/
theorem gain_core_with_exceptions {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (ν S F U C : ℝ)
    (hν0 : 31/50≤ν) (hν1 : ν≤3/4) (hF : 0≤F) (hU : 1≤U)
    (rows : Finset FreeRow) (f : FreeRow→ℝ)
    (hf : ∀u∈rows,f u≤U^(ν*S))
    (hregular : (∑u∈rows.filter (fun u=>¬D.exceptionalCore u),f u)≤
      C*U^(rho ν*F+ν*S-gain ν S F)) :
    (∑u∈rows,f u)≤(C+(D.exceptional_cores_finite.toFinset.card:ℝ))*
      U^(rho ν*F+ν*S-gain ν S F) := by
  let E := D.exceptional_cores_finite.toFinset
  let removed := rows.filter D.exceptionalCore
  have hsub : removed⊆E := by
    intro u hu
    exact (Set.Finite.mem_toFinset _).mpr (Finset.mem_filter.mp hu).2
  have hcard : (removed.card:ℝ)≤(E.card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
  have hgap : 0≤rho ν-coeffC ν := by linarith [(root_series_gap hν0 hν1).1]
  have hpay : U^(ν*S)≤U^(rho ν*F+ν*S-gain ν S F) :=
    Real.rpow_le_rpow_of_exponent_le hU (by nlinarith [gain_le_C ν S F,mul_nonneg hgap hF])
  have he : (∑u∈removed,f u)≤(E.card:ℝ)*U^(rho ν*F+ν*S-gain ν S F) := by
    calc
      _ ≤ ∑u∈removed,U^(ν*S) := Finset.sum_le_sum
        (fun u hu=>hf u (Finset.mem_filter.mp hu).1)
      _ = (removed.card:ℝ)*U^(ν*S) := by simp
      _ ≤ (E.card:ℝ)*U^(rho ν*F+ν*S-gain ν S F) :=
        mul_le_mul hcard hpay (Real.rpow_nonneg (zero_le_one.trans hU) _) (Nat.cast_nonneg _)
  have hpart := Finset.sum_filter_add_sum_filter_not rows D.exceptionalCore f
  calc
    _ = (∑u∈removed,f u)+(∑u∈rows.filter (fun u=>¬D.exceptionalCore u),f u) := hpart.symm
    _ ≤ (E.card:ℝ)*U^(rho ν*F+ν*S-gain ν S F)+C*U^(rho ν*F+ν*S-gain ν S F) :=
      add_le_add he hregular
    _ = _ := by ring

/-- All actual zero cores, including the finite inducing exceptions,
satisfy the ordinary density bound on every window of size at least one. -/
theorem actual_core_density_uniform {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0<loss) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀(a T Y : ℝ),33/40≤a → a≤7/8 → 0≤T → 1≤Y →
      ∀F : Finset FreeRow,
      (∀u∈F,rowNorm u≤Y ∧
        (rawZeroBin D.data a (7/8) T ⟨u.val,u.property.1⟩ ∨ D.exceptionalCore u)) →
      (F.card : ℝ)≤C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hf⟩ := LocalMoment.fixed_dictionary_eventual_with_exceptions D loss hloss
  let P : LocalMoment.DensityParameter → FreeRow → Prop := fun p u=>
    rawZeroBin D.data p.val.1 (7/8) p.val.2 ⟨u.val,u.property.1⟩ ∨ D.exceptionalCore u
  let exponent : LocalMoment.DensityParameter → ℝ := fun p=>unmarkedDensity (2*p.val.1-1)+loss
  let weight : LocalMoment.DensityParameter → ℝ := fun p=>(1+p.val.2)^J
  have hρ (p : LocalMoment.DensityParameter) : 2/7≤exponent p := by
    dsimp [exponent]
    linarith [unmarkedDensity_ge_two_sevenths
      (show 2*p.val.1-1≤3/4 by linarith [p.property.2.1])]
  have hw (p : LocalMoment.DensityParameter) : 1≤weight p := one_le_pow₀ (by linarith [p.property.2.2])
  have hevent : ∀ᶠY : ℝ in atTop,∀p : LocalMoment.DensityParameter,∀F : Finset FreeRow,
      (∀u∈F,rowNorm u≤Y ∧ P p u) → (F.card : ℝ)≤C*weight p*Y^exponent p := by
    filter_upwards [hf] with Y hf
    intro p
    exact hf p.val.1 p.val.2 p.property.1 p.property.2.1 p.property.2.2
  obtain ⟨C',hC',_,hfree⟩ := uniform_free_density_weighted_of_eventually P C exponent weight
    (fun p=>by linarith [hρ p]) hw hevent
  refine ⟨J,C',hC',?_⟩
  intro a T Y ha ha' hT hY F hF
  exact hfree Y hY ⟨(a,T),ha,ha',hT⟩ F hF

/-- The large-root half of the marked raw convolution is unconditional:
actual zero transport, all exceptional cores, and the ordinary pointwise
slot envelope supply its fiber estimate. -/
theorem actual_ordinary_weighted_fibers {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0<loss) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀(reverse : Label→Bool)(a T H envelope : ℝ),
      33/40≤a → a≤7/8 → 0≤T → 0<H → 0≤envelope →
      ∀(R : Finset NonzeroFrequency)(f : NonzeroFrequency→ℝ),
      (∀u∈R,rawFrequencyNorm u≤H ∧ orientedActualZeroRow D.data reverse a T u) →
      (∀u∈R,f u≤envelope) → ∀B : NZIdeal,
      (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
        (C*(1+T)^J)*envelope*(H/(B.val.absNorm : ℝ)^6)^(unmarkedDensity (2*a-1)+loss) := by
  obtain ⟨J,C,hC,hfree⟩ := actual_core_density_uniform D loss hloss
  refine ⟨J,C,hC,?_⟩
  intro reverse a T H envelope ha ha' hT hH henv R f hR hf B
  let Y : ℝ := H/(B.val.absNorm : ℝ)^6
  have hBp : 0<(B.val.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
  have hraw (u : FreeRow) (hu : u∈sixthFreeFiber R B) : sixthFrequencyEquiv (u,B)∈R := by
    obtain ⟨p,hp,hpu⟩ := Finset.mem_image.mp hu
    obtain ⟨hp,hpB⟩ := Finset.mem_filter.mp hp
    have he : p=(u,B) := Prod.ext hpu hpB
    subst p
    exact (mem_sixthPairs R (u,B)).mp hp
  have hmem (u : FreeRow) (hu : u∈sixthFreeFiber R B) : rowNorm u≤Y ∧
      (rawZeroBin D.data a (7/8) T ⟨u.val,u.property.1⟩ ∨ D.exceptionalCore u) := by
    have hr := hR _ (hraw u hu)
    rw [raw_sixth_norm] at hr
    refine ⟨(le_div_iff₀ (pow_pos hBp 6)).mpr hr.1,?_⟩
    simpa only [Equiv.symm_apply_apply] using
      LocalMoment.oriented_zero_core_predicate D reverse a T ha (sixthFrequencyEquiv (u,B)) hr.2
  by_cases hY : 1≤Y
  · have hc := hfree a T Y ha ha' hT hY (sixthFreeFiber R B) hmem
    calc
      _ ≤ ∑u∈sixthFreeFiber R B,envelope := Finset.sum_le_sum (fun u hu=>hf _ (hraw u hu))
      _ = ((sixthFreeFiber R B).card : ℝ)*envelope := by simp
      _ ≤ (C*(1+T)^J*Y^(unmarkedDensity (2*a-1)+loss))*envelope :=
        mul_le_mul_of_nonneg_right hc henv
      _ = _ := by dsimp [Y];ring
  · have hempty : sixthFreeFiber R B=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hY ((rowNorm_ge_one u).trans (hmem u hu).1)
    rw [hempty,Finset.sum_empty]
    positivity

theorem actual_full_gain_raw_from_small_roots {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (loss : ℝ) (hloss : 0<loss) :
    ∃J₀ : ℕ,∃C₀ K : ℝ,0<C₀ ∧ 0<K ∧
      ∀(J : ℕ)(C : ℝ),0≤C →∀(reverse : Label→Bool)(a T U S F : ℝ),
      33/40≤a →a≤7/8 →0≤T →1<U →0≤F →
      ∀(R : Finset NonzeroFrequency)(f : NonzeroFrequency→ℝ),
      (∀u∈R,rawFrequencyNorm u≤U^F ∧ orientedActualZeroRow D.data reverse a T u) →
      (∀u∈R,f u≤U^((2*a-1)*S)) →
      (∀B : NZIdeal,(B.val.absNorm : ℝ)≤U^(F/12) →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          (C*(1+T)^J)*U^(rho (2*a-1)*(F-6*Real.logb U (B.val.absNorm : ℝ))+(2*a-1)*S-
            gain (2*a-1) S (F-6*Real.logb U (B.val.absNorm : ℝ))+loss*F)) →
      (∑u∈R,f u)≤(C+C₀)*K*(1+T)^(J+J₀)*
        U^(rho (2*a-1)*F+(2*a-1)*S-gain (2*a-1) S F+loss*F) := by
  obtain ⟨J₀,C₀,hC₀,hordinary⟩ := actual_ordinary_weighted_fibers D loss hloss
  obtain ⟨K,hK,hlift⟩ := full_gain_root_completion
  refine ⟨J₀,C₀,K,hC₀,hK,?_⟩
  intro J C hC reverse a T U S F ha ha' hT hU hF R f hR hf hsmall
  let ν := 2*a-1
  let Cnow := (C+C₀)*(1+T)^(J+J₀)*U^(loss*F)
  have hUp : 0<U := zero_lt_one.trans hU
  have hν0 : 31/50≤ν := by dsimp [ν]; linarith
  have hν1 : ν≤3/4 := by dsimp [ν]; linarith
  have hbase : 1≤1+T := by linarith
  have hheight₁ : C*(1+T)^J≤(C+C₀)*(1+T)^(J+J₀) := by
    exact mul_le_mul (le_add_of_nonneg_right hC₀.le)
      (pow_le_pow_right₀ hbase (Nat.le_add_right J J₀)) (by positivity) (by positivity)
  have hheight₀ : C₀*(1+T)^J₀≤(C+C₀)*(1+T)^(J+J₀) := by
    exact mul_le_mul (le_add_of_nonneg_left hC)
      (pow_le_pow_right₀ hbase (Nat.le_add_left J₀ J)) (by positivity) (by positivity)
  have hs (B : NZIdeal) (hB : (B.val.absNorm : ℝ)≤U^(F/12)) :
      (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
        Cnow*U^(rho ν*(F-6*Real.logb U (B.val.absNorm : ℝ))+ν*S-
          gain ν S (F-6*Real.logb U (B.val.absNorm : ℝ))) := by
    have hh := hsmall B hB
    rw [Real.rpow_add hUp] at hh
    calc
      _ ≤ (C*(1+T)^J*U^(loss*F))*U^(rho ν*(F-6*Real.logb U (B.val.absNorm : ℝ))+ν*S-
          gain ν S (F-6*Real.logb U (B.val.absNorm : ℝ))) := by convert hh using 1 <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hheight₁ (Real.rpow_nonneg hUp.le _))
        (Real.rpow_nonneg hUp.le _)
  have hl (B : NZIdeal) (_hB : U^(F/12)<(B.val.absNorm : ℝ)) :
      (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
        Cnow*U^(rho ν*F+ν*S)*(B.val.absNorm : ℝ)^(-6*rho ν) := by
    have hBp : 0<(B.val.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    have hB1 : 1≤(B.val.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    have hh := hordinary reverse a T (U^F) (U^(ν*S)) ha ha' hT
      (Real.rpow_pos_of_pos hUp _) (Real.rpow_nonneg hUp.le _) R f hR hf B
    change _≤(C₀*(1+T)^J₀)*U^(ν*S)*(U^F/(B.val.absNorm : ℝ)^6)^(rho ν+loss) at hh
    rw [sixth_window_power (U^F) (B.val.absNorm : ℝ) (rho ν+loss)
      (Real.rpow_pos_of_pos hUp _) hBp,←Real.rpow_mul hUp.le] at hh
    have hp : (B.val.absNorm : ℝ)^(-6*(rho ν+loss))≤(B.val.absNorm : ℝ)^(-6*rho ν) :=
      Real.rpow_le_rpow_of_exponent_le hB1 (by linarith)
    calc
      _ ≤ ((C₀*(1+T)^J₀)*U^(ν*S)*U^(F*(rho ν+loss)))*
          (B.val.absNorm : ℝ)^(-6*(rho ν+loss)) := by simpa only [mul_assoc] using hh
      _ ≤ ((C₀*(1+T)^J₀)*U^(ν*S)*U^(F*(rho ν+loss)))*
          (B.val.absNorm : ℝ)^(-6*rho ν) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((C₀*(1+T)^J₀)*U^(loss*F))*U^(rho ν*F+ν*S)*
          (B.val.absNorm : ℝ)^(-6*rho ν) := by
        congr 1
        rw [show F*(rho ν+loss)=rho ν*F+loss*F by ring]
        simp only [Real.rpow_add hUp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hheight₀ (Real.rpow_nonneg hUp.le _))
          (Real.rpow_nonneg hUp.le _)) (Real.rpow_nonneg hBp.le _)
  have hh := hlift ν S F U Cnow hν0 hν1 hF hU (by dsimp [Cnow]; positivity) R f hs hl
  convert hh using 1
  dsimp [Cnow]
  rw [Real.rpow_add hUp]
  ring

end
end OAI.SevenEighths.Record12518109GainActualRoot
#print axioms OAI.SevenEighths.Record12518109GainActualRoot.actual_ordinary_weighted_fibers
