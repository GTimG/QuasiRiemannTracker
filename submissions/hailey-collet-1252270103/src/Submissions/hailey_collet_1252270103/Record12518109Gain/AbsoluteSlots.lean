/-
Copyright (c) 2026 Hailey Collet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Absolute annular estimate adapted from Cycle61/Physical/CoarseEnergy.lean.
Keeping the exact square-root normalization sharpens the squared bound to P.
-/
import Submissions.hailey_collet_1252270103.Record12518109Gain.SourceSlotEnvelope
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.Counting

set_option autoImplicit false
namespace OAI.SevenEighths.Record12518109GainWholeGeometry
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentCommonMaskExpansion
open CenteredMomentCounting CenteredMomentPrimeSlot CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ)
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Uniform also for principal characters, units, and arbitrary mask conductors. -/
theorem ray_slot_absolute (W : ℝ→ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(χ : Character)(P σ freq : ℝ),
      1≤P →lo≤σ →σ≤hi →
      ‖rayPrimePolynomial M H χ W b P σ freq‖^2≤C*P := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  let K := 128*B*max 1 b
  refine ⟨max 1 (K^2),le_max_left _ _,?_⟩
  intro χ P σ freq hP hσ hσhi
  have hPp : 0 < P := zero_lt_one.trans_le hP
  let S := (annulusSet b P).filter (fun I => Prime I ∧ I ∈ RayQuotient.identityClass M H)
  let f : Ideal O → ℂ := fun I =>
    if I ∈ S then idealCoeff χ I * annularWeight W P σ freq I else 0
  have hn (I : Ideal O) : ‖idealCoeff χ I * annularWeight W P σ freq I‖ ≤ B := by
    apply (show ‖idealCoeff χ I * annularWeight W P σ freq I‖ ≤
      ‖annularWeight W P σ freq I‖ by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)).trans
    by_cases hz : W ((I.absNorm : ℝ)/P) = 0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσ,hσhi⟩ _ hs
  have hsum := norm_tsum_ideal_ball f (max 1 b*P) B (by positivity) hB.le
    (by
      change f (0 : Ideal O) = 0
      simp only [f,idealCoeff_zero,zero_mul,ite_self])
    (by intro I; dsimp only [f]; split_ifs; exact hn I; simpa using hB.le)
    (by
      intro I hI
      have hmem : I ∈ S := by
        by_contra hnot
        exact hI (by simp only [f,ite_eq_right hnot])
      have hw : W ((I.absNorm : ℝ)/P) ≠ 0 := by
        intro hz
        exact hI (by simp only [f,ite_eq_left hmem,annularWeight,hz,zero_mul,mul_zero])
      exact ((div_le_iff₀ hPp).mp (hWs hw).2).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 b) hPp.le))
  have he : (∑' I : Ideal O, f I) = ∑ I ∈ S, idealCoeff χ I * annularWeight W P σ freq I := by
    rw [tsum_eq_sum (s := S) (fun I hI => by simp only [f,ite_eq_right hI])]
    exact Finset.sum_congr rfl (fun I hI => by simp only [f,ite_eq_left hI])
  rw [he] at hsum
  have hnorm : ‖(P:ℂ)^(-(1/2:ℂ))‖^2=P⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hPp,←Real.rpow_natCast,←Real.rpow_mul hPp.le]
    norm_num [Real.rpow_neg_one]
  have hn0 : 0≤‖∑ I∈S,idealCoeff χ I*annularWeight W P σ freq I‖ := norm_nonneg _
  have hsquare := pow_le_pow_left₀ hn0 (hsum.trans_eq (show _=K*P by dsimp only [K];ring)) 2
  unfold rayPrimePolynomial
  change ‖(P:ℂ)^(-(1/2:ℂ))*(∑ I∈S,idealCoeff χ I*annularWeight W P σ freq I)‖^2≤_
  rw [norm_mul,mul_pow,hnorm]
  calc
    _≤P⁻¹*(K*P)^2 := mul_le_mul_of_nonneg_left hsquare (inv_nonneg.mpr hPp.le)
    _=K^2*P := by field_simp
    _≤_ := mul_le_mul_of_nonneg_right (le_max_right 1 _) hPp.le

variable (hH : RayOrthogonality.globalUnits M≤H)
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]

/-- The original masked natural character stays literal throughout this bound. -/
theorem actual_original_slot_absolute (W : ℝ→ℂ) (lo hi : ℝ)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2) (hW : Continuous W) :
    ∃C : ℝ,1≤C ∧∀(Z : ℝ),1≤Z →∀(χ η₀ : Character)
      (slots : Finset Slot)(w σ v : Slot→ℝ)(t : ℝ)
      (θ : Slot→RayQuotient.Characters M H),
      (∀s∈slots,0≤w s) →(∀s∈slots,lo≤σ s) →(∀s∈slots,σ s≤hi) →
      let Q:=fun s=>naturalSlot χ (primePool M H 2 (Z^(w s)))
        (fun K=>idealCoeff (relativeCharacter M H hH η₀ (θ s)) K*
          annularWeight W (Z^(w s)) (σ s) (t+v s) K) (Z^(w s));
      (∏s∈slots,max 1 (‖Q s‖^2))≤C^slots.card*Z^(∑s∈slots,w s) := by
  obtain ⟨C,hC,hbound⟩:=ray_slot_absolute M H W 1 2 lo hi (by norm_num) hWs hW
  refine ⟨C,hC,?_⟩
  intro Z hZ χ η₀ slots w σ v t θ hw hlo hhi Q
  have hZp : 0<Z:=zero_lt_one.trans_le hZ
  calc
    _≤∏s∈slots,C*Z^(w s) := by
      apply Finset.prod_le_prod₀ (fun _ _=>le_trans zero_le_one (le_max_left _ _))
      intro s hs
      have hP : 1≤Z^(w s):=Real.one_le_rpow hZ (hw s hs)
      apply max_le
      · nlinarith
      · dsimp only [Q]
        rw [source_relative_slot_eq_ray M H hH χ η₀ (θ s) W 2 _ _ _ (by positivity)]
        exact hbound _ _ _ _ hP (hlo s hs) (hhi s hs)
    _=C^slots.card*Z^(∑s∈slots,w s) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hZp]

end
end OAI.SevenEighths.Record12518109GainWholeGeometry
