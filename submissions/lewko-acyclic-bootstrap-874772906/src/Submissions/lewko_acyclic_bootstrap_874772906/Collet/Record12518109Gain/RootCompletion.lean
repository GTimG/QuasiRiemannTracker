import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.Homogeneous
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.LocalMoment.RawSixthDensity

/- Exact weighted decomposition and uniform ideal tail adapted from PR63
Candidate/Cycle63/Marked/DeletionRawLift.lean, Apache-2.0.
The root-dependent homogeneous gain is retained in the new lift below. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Record12518109GainRoot
noncomputable section
open scoped Classical BigOperators
open LocalMoment HeckeFamily HeckeInverseAmplification ConcretePrimeRowBridge ProbeHighRowFamily ProbePhysical
open Record12518109Gain
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
  have hw0 (B : NZIdeal) : 0≤w B := by dsimp [w]; positivity
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

theorem root_dependent_power {ν S F U n : ℝ}
    (hν0 : 31/50 ≤ ν) (hν1 : ν ≤ 3/4) (hU : 1<U) (hn : 1≤n) :
    U^(rho ν*(F-6*Real.logb U n)+ν*S-gain ν S (F-6*Real.logb U n)) ≤
      U^(rho ν*F+ν*S-gain ν S F)*n^(-6*(rho ν-coeffC ν)) := by
  have hn0 : 0<n := zero_lt_one.trans_le hn
  have hl : 0≤Real.logb U n := Real.logb_nonneg hU hn
  have hg := gain_width_loss (S:=S) (q:=F-6*Real.logb U n) (F:=F) hν0 hν1 (by linarith)
  have hp : n^(-6*(rho ν-coeffC ν)) = U^(Real.logb U n*(-6*(rho ν-coeffC ν))) := by
    rw [Real.rpow_mul (x:=U) (by linarith),Real.rpow_logb (by linarith) hU.ne' hn0]
  rw [hp,←Real.rpow_add (by linarith : 0<U)]
  exact Real.rpow_le_rpow_of_exponent_le hU.le (by nlinarith)

theorem root_window {F U n : ℝ} (hU : 1<U) (hn : 1≤n) (hsmall : n≤U^(F/12)) :
    F/2 ≤ F-6*Real.logb U n ∧ F-6*Real.logb U n ≤ F := by
  have hl : 0≤Real.logb U n := Real.logb_nonneg hU hn
  have he := (Real.logb_le_logb hU (by linarith : 0<n)
    (Real.rpow_pos_of_pos (by linarith : 0<U) _)).mpr hsmall
  rw [Real.logb_rpow (by linarith) hU.ne'] at he
  constructor <;> linarith

theorem fixed_inducing_payment {ν S F : ℝ} (hν0 : 31/50≤ν) (hν1 : ν≤3/4)
    (hS : 0≤S) (hhigh : 2*S≤(rho ν-1/6)*F) :
    F/6+S ≤ rho ν*F+ν*S-gain ν S F := by
  have hp := (coefficient_bounds hν0 hν1).2.1
  have hm := mul_le_mul_of_nonneg_right hp hS
  have hg := gain_le_phi ν S F
  nlinarith

theorem root_window_fixed_cutoff {F U n : ℝ} (hU : 1<U) (hn : 1≤n)
    (hF : 1/25≤F) (hsmall : n≤U^(F/12)) :
    1/50≤F-6*Real.logb U n := by
  have hh := (root_window hU hn hsmall).1
  linarith

/-- Full-gain completion of the actual sixth-power fibers. The small-root
premise is the unweakened natural-core estimate at its residual width;
the large-root premise is its ordinary count and pointwise marked envelope.
No root cardinality or common-cutoff minimum is introduced. -/
theorem full_gain_root_completion :
    ∃ D : ℝ, 0<D ∧ ∀ (ν S F U C : ℝ), 31/50≤ν → ν≤3/4 → 0≤F → 1<U → 0≤C →
      ∀ (R : Finset NonzeroFrequency) (f : NonzeroFrequency→ℝ),
      (∀ B : NZIdeal, (B.val.absNorm : ℝ)≤U^(F/12) →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          C*U^(rho ν*(F-6*Real.logb U (B.val.absNorm : ℝ))+ν*S-
            gain ν S (F-6*Real.logb U (B.val.absNorm : ℝ)))) →
      (∀ B : NZIdeal, U^(F/12)<(B.val.absNorm : ℝ) →
        (∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))) ≤
          C*U^(rho ν*F+ν*S)*(B.val.absNorm : ℝ)^(-6*rho ν)) →
      (∑h∈R,f h) ≤ C*D*U^(rho ν*F+ν*S-gain ν S F) := by
  let w : NZIdeal→ℝ := fun B=>(B.val.absNorm : ℝ)^(-(279/175:ℝ))
  have hw : Summable w := by
    convert ideal_sixth_power_summable (93/350) (by norm_num) using 1
    funext B
    dsimp [w]
    norm_num
  have hw0 (B : NZIdeal) : 0≤w B := by dsimp [w]; positivity
  let D1 := (∑'B:NZIdeal,w B)+1
  have hsum : (0:ℝ)≤∑'B:NZIdeal,w B := tsum_nonneg hw0
  have hD1 : 0<D1 := by dsimp [D1]; linarith
  obtain ⟨D2,hD2,htail⟩ := ideal_sixth_tail_uniform (1/100) (by norm_num)
  refine ⟨D1+D2,by positivity,?_⟩
  intro ν S F U C hν0 hν1 hF hU hC R f hsmall hlarge
  let A := rho ν*F+ν*S-gain ν S F
  let roots := (sixthPairs R).image Prod.snd
  let small := roots.filter (fun B => (B.val.absNorm : ℝ)≤U^(F/12))
  let large := roots.filter (fun B => ¬(B.val.absNorm : ℝ)≤U^(F/12))
  let value := fun B : NZIdeal => ∑u∈sixthFreeFiber R B,f (sixthFrequencyEquiv (u,B))
  have hn (B : NZIdeal) : 1≤(B.val.absNorm : ℝ) := by
    have hp : 0<B.val.absNorm := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr B.property)
    exact_mod_cast hp
  have hsmall' : (∑B∈small,value B) ≤ C*D1*U^A := by
    have hterm (B : NZIdeal) (hB : B∈small) : value B ≤ C*U^A*w B := by
      have hb := (Finset.mem_filter.mp hB).2
      have hh := hsmall B hb
      have hrp := root_dependent_power (S:=S) (F:=F) hν0 hν1 hU (hn B)
      have hweight : (B.val.absNorm : ℝ)^(-6*(rho ν-coeffC ν)) ≤ w B :=
        Real.rpow_le_rpow_of_exponent_le (hn B) (by linarith [(root_series_gap hν0 hν1).1])
      calc
        value B ≤ C*U^A*(B.val.absNorm : ℝ)^(-6*(rho ν-coeffC ν)) := by
          exact hh.trans (by simpa only [mul_assoc,A] using mul_le_mul_of_nonneg_left hrp hC)
        _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)
    calc
      _ ≤ ∑B∈small,C*U^A*w B := Finset.sum_le_sum hterm
      _ = C*U^A*(∑B∈small,w B) := by rw [Finset.mul_sum]
      _ ≤ C*U^A*D1 := mul_le_mul_of_nonneg_left
        ((hw.sum_le_tsum _ (fun B _=>hw0 B)).trans (by dsimp [D1]; linarith)) (by positivity)
      _ = _ := by ring
  have hX : 1≤U^(F/12) := Real.one_le_rpow hU.le (by linarith)
  have hrho : 1+1/100≤6*rho ν := by linarith [rho_lower hν1]
  have htail' := htail (rho ν) (U^(F/12)) hrho hX large (fun B hB=>
    (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hB).2)))
  have hlarge' : (∑B∈large,value B) ≤ C*D2*U^A := by
    calc
      _ ≤ ∑B∈large,C*U^(rho ν*F+ν*S)*(B.val.absNorm : ℝ)^(-6*rho ν) := by
        apply Finset.sum_le_sum
        intro B hB
        exact hlarge B (lt_of_not_ge (Finset.mem_filter.mp hB).2)
      _ = C*U^(rho ν*F+ν*S)*(∑B∈large,(B.val.absNorm : ℝ)^(-6*rho ν)) := by rw [Finset.mul_sum]
      _ ≤ C*U^(rho ν*F+ν*S)*(D2*(U^(F/12))^(-(6*rho ν-1-1/100))) :=
        mul_le_mul_of_nonneg_left htail' (by positivity)
      _ = C*D2*U^(rho ν*F+ν*S+(F/12)*(-(6*rho ν-1-1/100))) := by
        rw [←Real.rpow_mul (x:=U) (by linarith)]
        calc
          _ = C*D2*(U^(rho ν*F+ν*S)*U^((F/12)*(-(6*rho ν-1-1/100)))) := by ring
          _ = _ := by rw [←Real.rpow_add (by linarith : 0<U)]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤C*D2)
        apply Real.rpow_le_rpow_of_exponent_le hU.le
        have hg := gain_le_C ν S F
        have hgap := (root_series_gap hν0 hν1).2
        have hm := mul_nonneg (show 0≤(rho ν-1/6)/2-coeffC ν-1/1200 by linarith) hF
        dsimp [A]
        nlinarith
  rw [raw_sixth_weighted_sum]
  change (∑B∈roots,value B) ≤ _
  rw [←Finset.sum_filter_add_sum_filter_not roots (fun B => (B.val.absNorm : ℝ)≤U^(F/12)) value]
  have hh := add_le_add hsmall' hlarge'
  convert hh using 1 <;> dsimp [A] <;> ring

end
end OAI.SevenEighths.Record12518109GainRoot
