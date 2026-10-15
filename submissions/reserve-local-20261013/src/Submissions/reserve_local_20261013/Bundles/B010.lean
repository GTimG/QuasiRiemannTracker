/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.reserve_local_20261013.Bundles.B004
import Submissions.local44_20261013.Bundles.B005
import Submissions.reserve_local_20261013.Bundles.B006
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.RowRadicalConductor
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.SixthDecomposition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.MaskDescent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceDetectorCancellation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OriginalReflectionErrorMass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformReflectionApproximation
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UniformRetainedEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorClass

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.RowConductor ; sha256 838c04825723588bc22f6cd01491b01e05b39de30b4ad9e6413928a121c581e7 -/
section




/-! A radical-sized presentation of the actual physical row, with its exact
smoothed sums and the same reflected character coefficients. The radical
periodicity theorem is upstream; this module connects it to the natural
primitive/deletion reflection API without making a primitive-choice assumption.
-/
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.RowConductor
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open ProbeRowRadicalConductor ProbeHighRowFamily CenteredMomentNaturalPrimitive
open CenteredMomentUniformReflectionApproximation
local notation "O" => HeckeFamily.O

theorem idealCoeff_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) (I : Ideal O) :
    idealCoeff χ I = idealCoeff τ I := by
  by_cases hI : I = 0
  · subst I
    rw [map_zero, map_zero]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n ≠ 0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hI
  have hs : Ideal.span {n} = I := ConcretePrimeRowBridge.span_idealGenerator I
  rw [← hs, idealCoeff_span _ hn, idealCoeff_span _ hn, he]

theorem inverse_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) (n : O) :
    elementCoeff χ.inverse n = elementCoeff τ.inverse n := by
  rw [elementCoeff_inverse, elementCoeff_inverse, he]

theorem polynomial_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n)
    (inv : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) :
    HeckeDyadic.polynomial χ inv W D σ ω = HeckeDyadic.polynomial τ inv W D σ ω := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  simp only [HeckeDyadic.summand, HeckeDyadic.coefficient,
    idealCoeff_eq_of_elementCoeff_eq χ τ he I.val]

theorem principal_iff_of_equal_elements (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n) :
    χ.residue = 1 ↔ τ.residue = 1 := by
  apply HeckeFiniteDeletion.principal_iff_of_mask χ τ
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc, idealCoeff_eq_of_elementCoeff_eq χ τ he]
  · rw [ite_eq_right hc]
    simpa only [hc, ite_false] using idealCoeff_source_mask χ I

theorem LFunction_eq_of_elementCoeff_eq (χ τ : Character)
    (he : ∀ n : O, elementCoeff χ n = elementCoeff τ n)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    LFunction χ s = LFunction τ s := by
  unfold LFunction
  rw [continuedLattice_eq_of_elementCoeff_eq χ τ he hs hs1]

/-- This preserves all coefficients, including their zeros at deleted primes. -/
theorem exists_row_small_presentation (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ∃ τ : Character,
      τ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ∀ n : O, elementCoeff (rowCharacter S hS u) n = elementCoeff τ n := by
  obtain ⟨τ, hn, he⟩ := rawRow_small_presentation u
  refine ⟨τ.excludePrimes S hS, ?_, equal_elements_excludePrimes _ τ he S hS⟩
  change (τ.modulus * ∏ P ∈ S, P).absNorm ≤ _
  rw [map_mul]
  simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm] using
    Nat.mul_le_mul_right ((∏ P ∈ S, P).absNorm) hn

/-- A combined primitive-plus-redundant scale already pays for all finite
Euler deletions. Its selected-prime deficit therefore does not require
claiming that the redundant primes belong to a fixed set. -/
theorem reflected_scale_selected_deficit
    (S : Finset (Ideal O)) (u : FreeRow) (τ ψ : Character)
    (hτ : τ.modulus.absNorm ≤ fixedConductorConstant S *
      (Ideal.span {u.val} : Ideal O).radical.absNorm)
    (hcap : ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
      τ.modulus.absNorm)
    {k : ℕ} (P : Fin k → Ideal O) (hP : ∀ i, Prime (P i))
    (hdis : Function.Injective P) (e : Fin k → ℕ) (he : ∀ i, 2 ≤ e i)
    (hdiv : ∀ i, P i ^ e i ∣ Ideal.span {u.val}) :
    (ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
      ∏ i, (P i).absNorm ^ (e i - 1) ≤
        fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm := by
  have hr := radical_norm_selected_deficit (Ideal.span {u.val})
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1) P hP hdis e
    (fun i => by have := he i; omega) hdiv
  calc
    _ ≤ (fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).radical.absNorm) *
        ∏ i, (P i).absNorm ^ (e i - 1) := Nat.mul_le_mul_right _ (hcap.trans hτ)
    _ ≤ _ := by simpa only [mul_assoc] using Nat.mul_le_mul_left (fixedConductorConstant S) hr

theorem reflected_scale_selected_deficit_real
    (S : Finset (Ideal O)) (u : FreeRow) (τ ψ : Character)
    (hτ : τ.modulus.absNorm ≤ fixedConductorConstant S *
      (Ideal.span {u.val} : Ideal O).radical.absNorm)
    (hcap : ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
      τ.modulus.absNorm)
    {k : ℕ} (P : Fin k → Ideal O) (hP : ∀ i, Prime (P i))
    (hdis : Function.Injective P) (e : Fin k → ℕ) (he : ∀ i, 2 ≤ e i)
    (hdiv : ∀ i, P i ^ e i ∣ Ideal.span {u.val}) :
    ((ψ.modulus.absNorm : ℝ) * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
      ∏ i, ((P i).absNorm : ℝ) ^ (e i - 1) ≤
        (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast reflected_scale_selected_deficit S u τ ψ hτ hcap P hP hdis e he hdiv

theorem reflected_scale_pos (τ ψ : Character) :
    0 < (ψ.modulus.absNorm : ℝ) * (redundantIdeal τ.modulus ψ.modulus).absNorm := by
  apply mul_pos
  · exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  · exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (redundantIdeal_ne_zero τ.modulus ψ.modulus))

/-- Exact original physical numerator reflection using a radical-sized
presentation. The output preserves the physical row and its inverse on all
ideals; the RHS is the actual upstream retained/discarded reflection. -/
theorem row_original_split (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow)
    (hn : (rowCharacter S hS u).residue ≠ 1) :
    ∃ (τ ψ : Character) (g : ℂ),
      (∀ n : O, elementCoeff (rowCharacter S hS u) n = elementCoeff τ n) ∧
      (∀ I : Ideal O, idealCoeff (rowCharacter S hS u).inverse I = idealCoeff τ.inverse I) ∧
      τ.residue ≠ 1 ∧ FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      ψ.residue ≠ 1 ∧ ‖g‖ = 1 ∧
      τ.modulus.absNorm ≤ fixedConductorConstant S *
        (Ideal.span {u.val} : Ideal O).radical.absNorm ∧
      ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm ≤
        τ.modulus.absNorm ∧
      (∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) →
        Function.Injective P → ∀ (e : Fin k → ℕ), (∀ i, 2 ≤ e i) →
        (∀ i, P i ^ e i ∣ Ideal.span {u.val}) →
        (ψ.modulus.absNorm * (redundantIdeal τ.modulus ψ.modulus).absNorm) *
          ∏ i, (P i).absNorm ^ (e i - 1) ≤
            fixedConductorConstant S * (Ideal.span {u.val} : Ideal O).absNorm) ∧
      ∀ (G : 𝓢(ℝ, ℂ)) (X R : ℝ), 0 < X →
        HeckeDyadic.polynomial (rowCharacter S hS u) false G X 0 0 =
          g * (retainedSchwartz τ ψ G X R + discardedSchwartz τ ψ G X R) := by
  obtain ⟨τ, hτ, he⟩ := exists_row_small_presentation S hS u
  have hnτ : τ.residue ≠ 1 := fun h => hn ((principal_iff_of_equal_elements _ τ he).mpr h)
  obtain ⟨ψ, g, hp, hnp, hg, hcap, hsplit⟩ := original_split τ hnτ
  refine ⟨τ, ψ, g, he, ?_, hnτ, hp, hnp, hg, hτ, hcap, ?_, ?_⟩
  · exact idealCoeff_eq_of_elementCoeff_eq _ _ (inverse_elementCoeff_eq _ _ he)
  · intro k P hP hdis e he hdiv
    exact reflected_scale_selected_deficit S u τ ψ hτ hcap P hP hdis e he hdiv
  · intro G X R hX
    rw [polynomial_eq_of_elementCoeff_eq _ τ he]
    exact hsplit G X R hX

end Cycle25.Weighted.RowConductor
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.RowConductor -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.ReflectionRetained ; sha256 c4dfd544a778667bc14ae8c0f9d1262e3763a0c136de3577df40e4ea961b6c8f -/
section




namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorReflection
open HeckeFamily HeckeDyadic EisensteinSchwartzPoisson CenteredMomentScaleSupremum
open CenteredMomentRetainedWeightedSource CenteredMomentReflectionWeightedEnergy
open CenteredMomentReflectedTruncation CenteredMomentSectorLocalization
open CenteredMomentUniformReflectionApproximation CenteredMomentUniformRetainedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentNaturalPrimitive

lemma norm_mul_sqrt_fourth (z q : ℂ) :
    ‖z*(Real.sqrt ‖q‖:ℂ)‖^4 = ‖z‖^4*‖q‖^2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  calc
    _ = ((Real.sqrt ‖q‖)^2)^2 := by ring
    _ = _ := by rw [Real.sq_sqrt (norm_nonneg _)]

/-- Exact natural primitive restoration, including its summable redundant-prime
and annular packet, transports the rowwise reflected fourth moment. -/
theorem actual_retained_uniform_fourth (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B J : ℕ) (hB : 2 ≤ B) :
    ∃H : Finset (ℕ×ℕ), ∃C : ℝ, 0 < C ∧ ∀{ι : Type} [Fintype ι],
      ∀(G : ι → 𝓢(ℝ,ℂ)) (χ ψ : ι → Character) (P : ι → ℂ)
        (X R : ι → ℝ) (lo hi D E Rcap : ℝ),
      (∀i, 0 < X i) → lo ≤ hi →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0 < dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2 ∈ retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) ∈ Set.Icc lo hi) →
      0 < D → 0 ≤ E → (∀i, H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G i) ≤ D) →
      1 ≤ Rcap → (∀i, (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ) ≤ Rcap) →
      (∀v w : ℝ, ∀j k : Fin 2, ∀x ∈ Set.Icc lo hi, ∀y ∈ Set.Icc lo hi,
        (∑i, ‖polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P i‖^2)
          ≤ E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2) →
      (∑i, ‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)‖^4*‖P i‖^2)
        ≤ C*Rcap^epsilon*D^4*(1+2*(hi-lo))^2*E := by
  obtain ⟨H,Cp,hCp,hp⟩ := reflected_fourth_rowwise_scales B J
  obtain ⟨Cw,hCw,hw⟩ := actual_masked_reflection_fourth epsilon hepsilon
  refine ⟨H,Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ G χ ψ P X R lo hi D E Rcap hX hlh hgeom hD hE hGD hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let keep (i : ι) (u : α i) := u.2 ∈ retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  let c (i : ι) : ℂ := Real.sqrt ‖P i‖
  let f (i : ι) (u : α i) :=
    retainedColumn (χ i) (ψ i) (G i) (X i) (R i) 0 (hX i) B 0 (c i) u
  have hselected (u : ∀i, α i) :
      (∑i, ‖f i (u i)‖^4) ≤ Cp*D^4*(1+2*(hi-lo))^2*E := by
    let Y (i : ι) := if keep i (u i) then
      dyadicScale (u i).2*dualScale (χ i) (ψ i) (X i) (u i).1.1 (u i).1.2
      else Real.exp lo
    let P' (i : ι) := if keep i (u i) then P i else 0
    have hY (i : ι) : 0 < Y i := by
      dsimp [Y]
      split_ifs
      · exact mul_pos (dyadicScale_pos _) (dualScale_pos _ _ _ (hX i) _ _)
      · exact Real.exp_pos _
    have hlogY (i : ι) : Real.log (Y i) ∈ Set.Icc lo hi := by
      dsimp [Y]
      split_ifs with hk
      · exact hgeom i (u i) _ hk
      · simp only [Real.log_exp]; exact ⟨le_rfl,hlh⟩
    have he (v w : ℝ) (j k : Fin 2) (x : ℝ) (hx : x ∈ Set.Icc lo hi)
        (y : ℝ) (hy : y ∈ Set.Icc lo hi) :
        (∑i, ‖polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) j)
          (Real.exp x) 0 (2*Real.pi*v) *
          polynomial (χ i).inverse false (scaleTest (fun z : ℝ => (annulus z:ℂ)) k)
          (Real.exp y) 0 (2*Real.pi*w) * P' i‖^2)
          ≤ E*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
      apply (Finset.sum_le_sum (fun i _ => ?_)).trans (henergy v w j k x hx y hy)
      dsimp only [P']
      split_ifs
      · exact le_rfl
      · simp only [mul_zero,norm_zero,zero_pow (by omega : 2 ≠ 0)]
        exact sq_nonneg _
    have hh := hp G (fun i => (χ i).inverse) P' (fun i => dyadicScale (u i).2)
      Y lo hi D E hlh (fun i => dyadicScale_pos _) hY hlogY hD hE hGD he
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [f,retainedColumn]
    simp only [normalized_zero]
    by_cases hk : keep i (u i)
    · simp only [keep] at hk
      rw [if_pos hk]
      dsimp [Y,P',keep,c]
      rw [if_pos hk,if_pos hk,norm_mul_sqrt_fourth]
    · have hk' := hk
      simp only [keep] at hk'
      rw [if_neg hk']
      simp only [norm_zero,zero_pow (by omega : 4 ≠ 0)]
      dsimp [P',keep]
      rw [if_neg hk']
      simp
  have hh := hw (fun i => sourcePrimes (χ i) (ψ i))
    (fun i Q hQ => redundantSet_prime _ _ Q hQ) ψ (fun i => (ψ i).inverse)
    (fun _ => B) (fun _ => hB) Rcap _ hRcap hcap (fun _ _ => 1) f
    (by intro i a; simp) hselected
  simp only [one_mul] at hh
  have hid (i : ι) :
      retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*c i =
      ∑'a, signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) B a*f i a := by
    have he := retainedOriginal_eq_weighted (χ i) (ψ i) (G i) (X i) (R i) 0
      (hX i) B 0 (c i) (hh.1 i)
    simpa only [retained_zero,pow_zero,Complex.ofReal_one,one_mul] using he
  calc
    _ = ∑i, ‖retainedSchwartz (χ i) (ψ i) (G i) (X i) (R i)*c i‖^4 := by
      apply Finset.sum_congr rfl
      intro i _
      exact (norm_mul_sqrt_fourth _ (P i)).symm
    _ = ∑i, ‖∑'a, signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) B a*f i a‖^4 := by
      simp_rw [hid]
    _ ≤ Cw*Rcap^epsilon*(Cp*D^4*(1+2*(hi-lo))^2*E) := hh.2
    _ = _ := by ring

end SevenEighths.Cycle25WeightedNumeratorReflection
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.ReflectionRetained -/

/- BEGIN ORIGINAL MODULE LocalMoment.PlainUnmarkedAdapter ; sha256 cff526e5993ba50bfdc3704e943b5932bf6a91e3b2f6d13aa42079289b615b6b -/
section






set_option autoImplicit false

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate SchwartzMap
open Set Filter
namespace SevenEighths.LocalMoment
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainUnmarkedState CenteredMomentEnergyBands
open CenteredMomentEnergyState CenteredMomentDetectorPlainStateDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorPlainProfileControl
open ProbeDetectorPlainUnmarkedField QuadraticInitialBound ProbeHighRowFamily
local notation "O" => HeckeFamily.O

/-- The conductor-bounded natural representative has exactly the coefficient
sequence used by the fixed raw/plain moment dictionary. -/
theorem natural_row_moment_dictionary (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1).character I =
      idealCoeff ((momentData η).character (momentElement u)) I := by
  rw [CenteredMomentNaturalRowSource.NaturalRow.ideal, momentData_coeff]
  have hm : CenteredMomentSecondHeightFamily.fixedBadMask = rowMaskElement := by
    unfold CenteredMomentSecondHeightFamily.fixedBadMask rowMaskElement
    ring
  rw [hm]

/-- A zero-profile auxiliary slot meets the legacy interface supply condition.
It has no analytic contribution: every use below selects the empty product.
No prime-slot lower bound on the input family is assumed. -/
def UnmarkedFiber.toLegacy {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label)
    (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) :
    Fiber M H Label Unit U a ε tstar T allowance i where
  rows := F.rows
  nonempty := F.nonempty
  family := F.family
  witness := F.witness
  label := F.label
  left := F.left
  right := F.right
  fixed_label := F.fixed_label
  fixed_left := F.fixed_left
  fixed_right := F.fixed_right
  row_norm := F.row_norm
  rowData := F.rowData
  reverse := F.reverse
  row_coeff := F.row_coeff
  slots := {()}
  profile := fun _ _ => 0
  upper := fun _ => 0
  widths := fun _ => 7 / 37
  external := fun _ => 0
  bin := fun _ => HeckePrimeAmplitudeBins.amplitude (U^(7/37:ℝ)) ((2*a-1)/2) 1 0
  mesh := 7 / 37
  binWidth := 1
  mesh_nonneg := by norm_num
  binWidth_pos := by norm_num
  widths_pos := by intros; norm_num
  widths_mesh := by intros; exact le_rfl
  supply := by simp
  fixed_bin := by
    intros
    simp [HeckeDetectorPhysicalSelection.physical, HeckePrimeRow.canonicalPrimeAmplitude]

/-- The actual retained plain estimate for an unmarked detector fiber. It
keeps the literal dictionary and eligible-row condition, so it cannot be used
for a different family merely because the scalar exponents agree. -/
theorem unmarked_retained_plain
    {U a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
    (F : UnmarkedFiber U a ε tstar T allowance i Label)
    (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)
    (η : Character) (Q : Ideal O) (δ e : ℝ)
    (hU : 1 < U) (hδ : 0 ≤ δ)
    (hwidth : max 1 (2 * F.m) + δ ≤ 2)
    (hm : F.m ≤ 1)
    (hη : (η.modulus.absNorm : ℝ) ≤ U^δ)
    (hdata : F.rowData = momentData η)
    (hMm : M ≤ Ideal.span {rowMaskElement})
    (hkeep : ∀ u ∈ F.rows, initialKeep η Q u.val)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (A : ℝ)
    (hzero : ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 e U degree S A)
    (j k : ℕ) (σ t : ℝ) :
    (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
      ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
      polynomial (F.family u F.label) false
      ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2) ≤
      A * diagonalControl radialMajorant *
        (detectorProfiles F.reverse j k σ t).control S ^ 2 *
        U^(max 1 (2 * F.m) + δ + e) := by
  let G := F.toLegacy M H
  have hGM : G.m = F.m := rfl
  have hdataG : G.rowData = momentData η := hdata
  have hcompare := retained_positive_energy_le_source (initialKeep η Q)
    radialMajorant radialMajorant_nonneg radialMajorant_one G η ∅ j k σ t
    (zero_lt_one.trans hU) hkeep
  rw [← fiber_plain_unmarked_energy_eq G η hdataG hMm (zero_lt_one.trans hU) j k σ t]
    at hcompare
  let s := state G η Q radialMajorant radialSupportUpper δ hU.le hδ
    radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have he : s.width = max 1 (2 * F.m) + δ := by
    change 1 + CenteredMomentDetectorPlainUnmarkedState.allowance δ G.m = _
    rw [padded_width, hGM]
  have hscale : U^G.m ≤ U^(1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (hGM ▸ hm)
  have hb := hzero s rfl (he ▸ hwidth) (detectorProfiles G.reverse j k σ t)
    0 (U^G.m) (U^G.m) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) hscale hscale
  rw [actual_source_eq G η Q radialMajorant radialSupportUpper δ hU.le hδ
    radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t] at hcompare
  apply hcompare.trans
  have hrad : s.radial.profile = radialMajorant := rfl
  have hrev : G.reverse = F.reverse := rfl
  simpa only [he, hrad, hrev, norm_zero, add_zero, one_pow, mul_one] using hb

/-- The incumbent analytic induction supplies the zero-slot estimate itself.
The base character and fixed conductor are fixed before taking the scale limit.
The zero slot profile used here is only an argument of the incumbent certificate. -/
theorem fixed_zero_input (e : ℝ) (he : 0 < e)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Ideal O) [NeZero Q] (hQtop : Q ≠ ⊤)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) :
    ∃ degree : ℕ, ∃ control : Finset (ℕ × ℕ), ∀ η : Character,
      Q ≤ η.modulus → ∃ A : ℝ, 0 < A ∧ ∀ᶠ U : ℝ in atTop,
        ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 e U degree control A := by
  let κ : ℝ := max (3/4) (2 * HeckeZeroSupremum.beta - 1)
  have hκ : (3/4:ℝ) ≤ κ := le_max_left _ _
  have hκβ : 2 * HeckeZeroSupremum.beta - 1 ≤ κ := le_max_right _ _
  have hcert := CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Unit) Q ⊤ le_top (fun _ : ℝ => (0:ℂ))
    1 2 (1/4) (9/4) radialSupportUpper 0 1 0 0 2 κ e
    (by norm_num) (by simp) (by fun_prop)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    radialSupportUpper_spec.1 (by norm_num) (by norm_num) hκ he hβ hκβ
  obtain ⟨degree, control, h⟩ :=
    CenteredMomentEnergyCappedWidthInduction.certified_terminal (α := Unit)
      Q ⊤ le_top (fun _ : ℝ => (0:ℂ)) 2 (1/4) (9/4) radialSupportUpper
      0 1 0 0 2 κ e (by norm_num) (by norm_num) (by linarith) he hcert
  refine ⟨degree, control, ?_⟩
  intro η hQη
  have hi : internalQ Q η = Q := by
    unfold internalQ
    exact inf_eq_left.mpr hQη
  obtain ⟨A, B, hA, hB, hb⟩ := h η Q le_rfl (by simpa only [hi] using NeZero.ne Q)
    (by simpa only [hi] using hQtop) (by simpa only [hi] using hQ72)
  exact ⟨A, hA, hb.mono (fun U hU => by simpa only [hi] using hU.2.1)⟩

/-- Uniform retained unmarked field for an actual fixed inducing character.
The scale threshold is chosen before every height, row family, and dyadic fiber.
No prime-slot supply or assumed raw/plain moment appears in the inputs. -/
theorem fixed_retained_unmarked_plain (η : Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
    (εm : ℝ) (hεm : 0 < εm) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ {a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
        (F : UnmarkedFiber U a ε tstar T allowance i Label),
      F.m ≤ 3/4 → F.rowData = momentData η →
      (∀ u ∈ F.rows, initialKeep η Q u.val) →
      ∀ height : ℝ, 0 ≤ height → ∀ j k : ℕ, j + k ≤ 2 →
      ∀ σ ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (-height) height,
      (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2) ≤
        C * (1 + height)^J * U^(max 1 (2 * F.m) + εm) := by
  let δ : ℝ := min (εm / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδcap : δ ≤ 1/4 := min_le_right _ _
  have hδbudget : δ + δ ≤ εm := by
    have hd : δ ≤ εm/4 := min_le_left _ _
    linarith
  obtain ⟨degree, control, hz⟩ := fixed_zero_input δ hδ hβ Q hQtop hQ72
  obtain ⟨A, hA, hzero⟩ := hz η hQη
  obtain ⟨J, Cp, hCp, hprofiles⟩ := paired_control control
  let C : ℝ := A * (1 + diagonalControl radialMajorant) * Cp
  have hdiag : 0 ≤ diagonalControl radialMajorant := diagonalControl_nonneg _
  have hC : 0 < C := mul_pos (mul_pos hA (by linarith)) hCp
  have hC' : A * diagonalControl radialMajorant * Cp ≤ C := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : diagonalControl radialMajorant ≤
        1 + diagonalControl radialMajorant) hA.le) hCp.le
  have hmod : ∀ᶠ U : ℝ in atTop, (η.modulus.absNorm:ℝ) ≤ U^δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop _)
  refine ⟨J, C, hC, ?_⟩
  filter_upwards [hzero, hmod, eventually_gt_atTop (1:ℝ)] with U hz hmU hU
  refine ⟨hU, ?_⟩
  intro a ε tstar T allowance i Label F hm hdata hkeep height hh j k hjk σ hσ t ht
  have hwidth : max 1 (2 * F.m) + δ ≤ 2 := by
    have hmax : max 1 (2 * F.m) ≤ 3/2 := max_le (by norm_num) (by linarith)
    linarith
  have hb := unmarked_retained_plain F (Ideal.span {rowMaskElement}) ⊤ η Q δ δ
    hU hδ.le hwidth (by linarith) hmU hdata le_rfl hkeep degree control A hz j k σ t
  have ht' : ‖t‖ ≤ height := by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp : (detectorProfiles F.reverse j k σ t).control control ^ 2 ≤
      Cp * (1 + height)^J := by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl ht') J) hCp.le
  have hpow : U^(max 1 (2 * F.m) + δ + δ) ≤ U^(max 1 (2 * F.m) + εm) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  apply hb.trans
  calc
    _ ≤ (A * diagonalControl radialMajorant * (Cp * (1 + height)^J)) *
        U^(max 1 (2 * F.m) + εm) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hp (mul_nonneg hA.le hdiag)
      · exact hpow
      · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
      · exact mul_nonneg (mul_nonneg hA.le hdiag) (mul_nonneg hCp.le (by positivity))
    _ = (A * diagonalControl radialMajorant * Cp) * (1 + height)^J *
        U^(max 1 (2 * F.m) + εm) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC' (by positivity)) (by positivity)

/-- The free sixth-power-reduced rows removed by `initialKeep` lie in a
fixed finite set. In particular they need not be discarded by imposing a
scale-dependent lower bound on every row. -/
theorem fixed_exceptional_free_finite (η : Character) (Q : Ideal O)
    (hQ0 : Q ≠ 0) (hQtop : Q ≠ ⊤)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus) :
    {u : FreeRow | ¬initialKeep η Q u.val}.Finite := by
  have hfinite := HeckeExceptionalRows.rows_finite
    (UniqueFactorizationMonoid.normalizedFactors Q).toFinset
    (fun P hP => UniqueFactorizationMonoid.prime_of_normalized_factor P
      (Multiset.mem_toFinset.mp hP))
  have hpre : {u : FreeRow | u.val ∈ HeckeExceptionalRows.rows
      (UniqueFactorizationMonoid.normalizedFactors Q).toFinset}.Finite :=
    hfinite.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro u hu
  have hex : CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator 1) 1 u.val := by
    by_contra hn
    exact hu ⟨u.property.1, hn⟩
  exact fixed_inducing_free_support η Q hQ0 hQtop hQ72 hQη
    (CenteredMomentSecondHeightFamily.fixedBadMask * ConcretePrimeRowBridge.idealGenerator 1)
    (mul_ne_zero CenteredMomentSecondHeightFamily.fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hex

/-- A trivial one-row bound uniform in the character, both frequencies,
and the real parameter. This also covers principal and small-conductor rows. -/
theorem detector_plain_absolute :
    ∃ C : ℝ, 0 < C ∧ ∀ χ : Character, ∀ n : ℕ, n ≤ 2 →
      ∀ σ ∈ Icc (0:ℝ) 1, ∀ t D : ℝ, 0 < D →
      ‖polynomial χ false ((logProfile^[n]) positiveAnnular) D σ t‖ ≤
        C * Real.sqrt D := by
  obtain ⟨A, hA, habs⟩ := detectorSchwartz_absolute
  refine ⟨128 * (9/4) * A, by positivity, ?_⟩
  intro χ n hn σ hσ t D hD
  have hs : Function.support (detectorSchwartz false n σ t : ℝ → ℂ) ⊆ Iic (9/4) :=
    fun x hx => (detectorSchwartz_support false n σ t hx).2
  have hp := CenteredMomentOriginalReflectionErrorMass.plain_polynomial_bound
    χ (detectorSchwartz false n σ t) (9/4) A D 0 hA.le hD
    (habs false n hn σ hσ t) hs
  have he : (detectorSchwartz false n σ t : ℝ → ℂ) =
      twistProfile ((logProfile^[n]) positiveAnnular) σ t := by
    funext x
    simpa only [HeckeDetectorCoefficientTransfer.orientedProfile,
      HeckeDetectorCoefficientTransfer.orientedFrequency, Bool.false_eq_true, ite_false]
      using detectorSchwartz_apply false n σ t x
  simpa only [he, polynomial_twistProfile, max_eq_right (by norm_num : (1:ℝ) ≤ 9/4)] using hp

/-- A finite set of exceptional cores costs only its fixed cardinality times
D^2, within the zero-slot growth bound. -/
theorem finite_rows_plain_absolute :
    ∃ B : ℝ, 0 < B ∧ ∀ (rows : Finset FreeRow) (χ : FreeRow → Character),
      ∀ j k : ℕ, j + k ≤ 2 → ∀ σ ∈ Icc (0:ℝ) 1, ∀ t D : ℝ, 0 < D →
      (∑ u ∈ rows, ‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) D σ t *
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) D σ t‖^2) ≤
        (rows.card : ℝ) * B * D^2 := by
  obtain ⟨C, hC, hb⟩ := detector_plain_absolute
  refine ⟨C^4, by positivity, ?_⟩
  intro rows χ j k hjk σ hσ t D hD
  have hp (u : FreeRow) : ‖polynomial (χ u) false ((logProfile^[j]) positiveAnnular) D σ t *
        polynomial (χ u) false ((logProfile^[k]) positiveAnnular) D σ t‖^2 ≤ C^4 * D^2 := by
    have hj := hb (χ u) j (by omega) σ hσ t D hD
    have hk := hb (χ u) k (by omega) σ hσ t D hD
    rw [norm_mul]
    have hprod := mul_le_mul hj hk (norm_nonneg _) (by positivity : 0 ≤ C * Real.sqrt D)
    have hsq := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hprod 2
    convert hsq using 1
    rw [mul_pow, mul_pow, Real.sq_sqrt hD.le]
    ring
  calc
    _ ≤ ∑ u ∈ rows, C^4 * D^2 := Finset.sum_le_sum (fun u _ => hp u)
    _ = _ := by simp; ring

/-- Complete zero-slot plain field, including all small and exceptional free
cores. The theorem has a common scale threshold for all heights and fibers.
Its inducing character is fixed and its row dictionary is literal. -/
theorem fixed_unmarked_plain (η : Character) (Q : Ideal O) [NeZero Q]
    (hQtop : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQη : Q ≤ η.modulus)
    (εm : ℝ) (hεm : 0 < εm) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ {a ε tstar T allowance : ℝ} {i : ℕ} {Label : Type*}
        (F : UnmarkedFiber U a ε tstar T allowance i Label),
      F.m ≤ 3/4 → F.rowData = momentData η →
      ∀ height : ℝ, 0 ≤ height → ∀ j k : ℕ, j + k ≤ 2 →
      ∀ σ ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (-height) height,
      (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
        ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
        polynomial (F.family u F.label) false
        ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2) ≤
        C * (1 + height)^J * U^(max 1 (2 * F.m) + εm) := by
  obtain ⟨J, C, hC, hret⟩ := fixed_retained_unmarked_plain η Q hQtop hQ72 hQη εm hεm hβ
  obtain ⟨B, hB, habs⟩ := finite_rows_plain_absolute
  let E : Finset FreeRow := (fixed_exceptional_free_finite η Q (NeZero.ne Q) hQtop hQ72 hQη).toFinset
  let K : ℝ := (E.card : ℝ) * B
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) hB.le
  refine ⟨J, C + K, by linarith, ?_⟩
  filter_upwards [hret] with U hret
  refine ⟨hret.1, ?_⟩
  intro a ε tstar T allowance i Label F hm hdata height hh j k hjk σ hσ t ht
  let keep : FreeRow → Prop := fun u => initialKeep η Q u.val
  let retained := F.rows.filter keep
  let discarded := F.rows.filter (fun u => ¬keep u)
  let value : FreeRow → ℝ := fun u => ‖polynomial (F.family u F.label) false
    ((logProfile^[j]) positiveAnnular) (U^F.m) σ t *
    polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2
  let P : ℝ := U^(max 1 (2 * F.m) + εm)
  have hP : 0 ≤ P := Real.rpow_nonneg (zero_lt_one.trans hret.1).le _
  have hheight : 1 ≤ (1 + height)^J := one_le_pow₀ (by linarith)
  have hretained : (∑ u ∈ retained, value u) ≤ C * (1 + height)^J * P := by
    by_cases hne : retained.Nonempty
    · let G : UnmarkedFiber U a ε tstar T allowance i Label :=
        { F with
          rows := retained
          nonempty := hne
          fixed_label := by intro u hu; exact F.fixed_label u (Finset.mem_filter.mp hu).1
          fixed_left := by intro u hu; exact F.fixed_left u (Finset.mem_filter.mp hu).1
          fixed_right := by intro u hu; exact F.fixed_right u (Finset.mem_filter.mp hu).1
          row_norm := by intro u hu; exact F.row_norm u (Finset.mem_filter.mp hu).1
          row_coeff := by intro u hu; exact F.row_coeff u (Finset.mem_filter.mp hu).1 }
      exact hret.2 G hm hdata (fun u hu => (Finset.mem_filter.mp hu).2)
        height hh j k hjk σ hσ t ht
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp only [Finset.sum_empty]
      exact mul_nonneg (mul_nonneg hC.le (by positivity)) hP
  have hsub : discarded ⊆ E := by
    intro u hu
    exact (Set.Finite.mem_toFinset _).mpr (Finset.mem_filter.mp hu).2
  have hcard : (discarded.card : ℝ) ≤ (E.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hpower : (U^F.m)^2 ≤ P := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_lt_one.trans hret.1).le]
    apply Real.rpow_le_rpow_of_exponent_le hret.1.le
    have hmax := le_max_right (1:ℝ) (2 * F.m)
    dsimp [P]
    linarith
  have hdiscarded : (∑ u ∈ discarded, value u) ≤ K * (1 + height)^J * P := by
    have hb := habs discarded (fun u => F.family u F.label) j k hjk σ hσ t (U^F.m)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hret.1) _)
    apply hb.trans
    calc
      _ ≤ K * P := mul_le_mul (mul_le_mul_of_nonneg_right hcard hB.le)
        hpower (sq_nonneg _) hK
      _ ≤ K * (1 + height)^J * P := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hK hheight) hP
  have hsplit : (∑ u ∈ F.rows, value u) =
      (∑ u ∈ retained, value u) + ∑ u ∈ discarded, value u :=
    (Finset.sum_filter_add_sum_filter_not F.rows keep value).symm
  change (∑ u ∈ F.rows, value u) ≤ (C + K) * (1 + height)^J * P
  rw [hsplit]
  calc
    _ ≤ C * (1 + height)^J * P + K * (1 + height)^J * P := add_le_add hretained hdiscarded
    _ = _ := by ring

#print axioms natural_row_moment_dictionary
#print axioms fixed_unmarked_plain
#print axioms detector_plain_absolute
#print axioms finite_rows_plain_absolute
#print axioms fixed_retained_unmarked_plain
#print axioms fixed_exceptional_free_finite
#print axioms fixed_zero_input
#print axioms UnmarkedFiber.toLegacy
#print axioms unmarked_retained_plain
end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.PlainUnmarkedAdapter -/

/- BEGIN ORIGINAL MODULE LocalMoment.SixthRowMask ; sha256 f5ab31c8dd5929addcee424b7c19bd2e14e1a1455b88b3c45d48409f2fd53fd9 -/
section





/-! Exact raw-row sixth decomposition, with all Euler punctures retained. -/

namespace OAI
noncomputable section
open scoped Classical

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeRowClosure HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredExceptionalProfile HeckeFiniteDeletion HeckeDetectorZeros
local notation "O" => HeckeFamily.O

lemma rowData_character_zero (data : RowData) (u : NonzeroElement) :
    elementCoeff (data.character u) 0 = 0 := by
  rw [data.character_spec]
  exact rowTwist_zero_of_not_supported (elementHom data.η) data.m data.f u.val 0
    data.lambda_dvd data.two_dvd (by
      intro hs
      exact hs.1 (by simp))

/-- Multiplication of the integer row by an arbitrary ideal generator's
sixth power adds exactly its original coprimality holes. -/
theorem amplified_ideal_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) (I : Ideal O) :
    idealCoeff (data.character (amplifiedElement u B)) I =
      if IsCoprime I B.val then idealCoeff (data.character u) I else 0 := by
  by_cases hs : Supported I
  · rw [idealCoeff_eq_row data.η (data.character (amplifiedElement u B))
      data.m data.f (amplifiedElement u B).val
      (data.character_spec (amplifiedElement u B)) I]
    change idealCoeff data.η I *
      idealRowHom (data.m ^ 6 * data.f ^ 4 *
        (u.val * (idealGenerator B.val) ^ 6)) I = _
    rw [show data.m ^ 6 * data.f ^ 4 * (u.val * (idealGenerator B.val) ^ 6) =
      (data.m ^ 6 * data.f ^ 4 * u.val) * (idealGenerator B.val) ^ 6 by ring,
      idealRowHom_argument_mul, idealRowHom_sixth_mask _ I hs,
      span_idealGenerator]
    by_cases hc : IsCoprime I B.val
    · rw [ite_eq_left hc, mul_one, ite_eq_left hc]
      exact (idealCoeff_eq_row data.η (data.character u) data.m data.f u.val
        (data.character_spec u) I).symm
    · simp only [hc, ite_false, mul_zero]
  · rw [row_coeff_zero_unsupported data.η (data.character (amplifiedElement u B))
      data.m data.f (amplifiedElement u B).val
      (data.character_spec (amplifiedElement u B)) data.lambda_dvd data.two_dvd I hs,
      row_coeff_zero_unsupported data.η (data.character u) data.m data.f u.val
        (data.character_spec u) data.lambda_dvd data.two_dvd I hs]
    split_ifs <;> rfl

theorem amplified_element_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) (n : O) :
    elementCoeff (data.character (amplifiedElement u B)) n =
      if IsCoprime n (idealGenerator B.val) then elementCoeff (data.character u) n else 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [rowData_character_zero]
    split_ifs <;> rfl
  · have h := amplified_ideal_mask data u B (Ideal.span {n})
    rw [idealCoeff_span _ hn, idealCoeff_span _ hn,
      ← span_idealGenerator B.val, Ideal.isCoprime_span_singleton_iff] at h
    exact h

theorem inducedBy_self (χ : Character) : InducedBy χ χ := by
  intro I
  by_cases hc : IsCoprime I χ.modulus
  · rw [ite_eq_left hc]
  · have hz : idealCoeff χ I = 0 := by
      by_contra hn
      exact hc ((CenteredMomentExceptionalPair.idealCoeff_ne_zero_iff χ I).mp hn).2
    rw [ite_eq_right hc, hz]

/-- The exact modulus-mask relation expected by finite Euler deletion. -/
theorem amplified_modulus_mask (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal) :
    InducedBy (data.character (amplifiedElement u B)) (data.character u) :=
  HeckeMaskDescent.inducedBy_mask (data.character u)
    (data.character (amplifiedElement u B)) (data.character u)
    (idealGenerator B.val) (amplified_element_mask data u B)
    (inducedBy_self (data.character u))

theorem amplified_nonprincipal (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character u).residue ≠ 1) :
    (data.character (amplifiedElement u B)).residue ≠ 1 := by
  intro hp
  exact hu ((principal_iff_of_mask _ _ (amplified_modulus_mask data u B)).mp hp)

theorem amplified_positive_zeros (data : RowData) (u : NonzeroElement)
    (B : HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character u).residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction (data.character (amplifiedElement u B)) s = 0 ↔
      LFunction (data.character u) s = 0 :=
  positive_zeros_eq_of_mask _ _ (amplified_nonprincipal data u B hu)
    (amplified_modulus_mask data u B) hs

theorem amplified_zeroMaximum {ι : Type*} [Fintype ι]
    (data : ι → RowData) (u : ι → NonzeroElement)
    (B : ι → HeckeInverseAmplification.NonzeroIdeal)
    (hu : ∀ i, ((data i).character (u i)).residue ≠ 1) (T : ℝ) :
    zeroMaximum (fun i => (data i).character (amplifiedElement (u i) (B i)))
      (fun i => amplified_nonprincipal (data i) (u i) (B i) (hu i)) T =
        zeroMaximum (fun i => (data i).character (u i)) hu T :=
  zeroMaximum_eq_of_mask _ _ _ hu T
    (fun i => amplified_modulus_mask (data i) (u i) (B i))

/-- Bind the general hole identity to the source's actual bijective
decomposition of every nonzero raw integer frequency. -/
theorem sixthFrequency_character_mask (data : RowData)
    (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal) (I : Ideal O) :
    idealCoeff (data.character (ProbePhysical.sixthFrequencyEquiv p)) I =
      if IsCoprime I p.2.val then
        idealCoeff (data.character ⟨p.1.val, p.1.property.1⟩) I else 0 := by
  exact amplified_ideal_mask data ⟨p.1.val, p.1.property.1⟩ p.2 I

theorem sixthFrequency_positive_zeros (data : RowData)
    (p : FreeRow × HeckeInverseAmplification.NonzeroIdeal)
    (hu : (data.character ⟨p.1.val, p.1.property.1⟩).residue ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction (data.character (ProbePhysical.sixthFrequencyEquiv p)) s = 0 ↔
      LFunction (data.character ⟨p.1.val, p.1.property.1⟩) s = 0 :=
  amplified_positive_zeros data ⟨p.1.val, p.1.property.1⟩ p.2 hu hs

theorem sixthFrequency_zeroMaximum {ι : Type*} [Fintype ι]
    (data : ι → RowData)
    (p : ι → FreeRow × HeckeInverseAmplification.NonzeroIdeal)
    (hu : ∀ i, ((data i).character ⟨(p i).1.val, (p i).1.property.1⟩).residue ≠ 1)
    (T : ℝ) :
    zeroMaximum (fun i => (data i).character (ProbePhysical.sixthFrequencyEquiv (p i)))
      (fun i => amplified_nonprincipal (data i)
        ⟨(p i).1.val, (p i).1.property.1⟩ (p i).2 (hu i)) T =
      zeroMaximum (fun i => (data i).character ⟨(p i).1.val, (p i).1.property.1⟩) hu T :=
  amplified_zeroMaximum data (fun i => ⟨(p i).1.val, (p i).1.property.1⟩)
    (fun i => (p i).2) hu T

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.SixthRowMask -/

/- BEGIN ORIGINAL MODULE LocalMoment.UnmarkedBatch ; sha256 1bfbe1461df05e5ee16b4b71db9e9dde57f50499be7f372451c62f57e19bdff1 -/
section


/-! Unmarked detector partition, adapted from OpenAI's DetectorBatch and
DetectorFiberPartition. Unlike the marked batch, this has no positive
prime-slot-supply hypothesis. Its moments remain explicit source inputs. -/

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter

namespace SevenEighths.LocalMoment
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount HeckeDetectorRawFiber

structure UnmarkedBatch (Label : Type*) (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow → Label → Character
  witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U
  data : Label → RowData
  reverse : Label → Bool
  row_coeff : ∀ u ∈ rows, ∀ j, ∀ I : Ideal O, idealCoeff (family u j) I =
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val, u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val, u.property.1⟩) I

variable {Label : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

/-- Extend witnesses only to satisfy the ambient `FreeRow` interface.
Outside the finite source set, reuse one source row; no principal or
out-of-bin ambient row is required to possess a detector witness. -/
def supportedRowRetraction (rows : Finset FreeRow) (u₀ : rows) (u : FreeRow) : rows :=
  if hu : u ∈ rows then ⟨u, hu⟩ else u₀

@[simp] theorem supportedRowRetraction_mem (rows : Finset FreeRow) (u₀ u : rows) :
    supportedRowRetraction rows u₀ u.val = u := by
  simp [supportedRowRetraction, u.property]

def UnmarkedBatch.ofSupportedRows (rows : Finset FreeRow) (u₀ : rows)
    (family : rows → Label → Character)
    (witness : ∀ u, SupportedWitness (family u) U a ε tstar T allowance i)
    (hrow : ∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U)
    (data : Label → RowData) (reverse : Label → Bool)
    (hcoeff : ∀ u : rows, ∀ j, ∀ I : Ideal O, idealCoeff (family u j) I =
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character
        ⟨u.val.val, u.val.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val.val, u.val.property.1⟩) I) :
    UnmarkedBatch Label U a ε tstar T allowance i where
  rows := rows
  family := fun u => family (supportedRowRetraction rows u₀ u)
  witness := fun u => witness (supportedRowRetraction rows u₀ u)
  row_norm := hrow
  data := data
  reverse := reverse
  row_coeff := by
    intro u hu j I
    have h := hcoeff ⟨u, hu⟩ j I
    simpa only [supportedRowRetraction, dite_eq_left hu] using h

def UnmarkedBatch.fiberRows (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  B.rows.filter (fun u => (B.witness u).label = j ∧
    (B.witness u).left = J ∧ (B.witness u).right = K)

def UnmarkedBatch.fiber (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows j J K).Nonempty) : UnmarkedFiber U a ε tstar T allowance i Label where
  rows := B.fiberRows j J K
  nonempty := hne
  family := B.family
  witness := B.witness
  label := j
  left := J
  right := K
  fixed_label := fun _ hu => (Finset.mem_filter.mp hu).2.1
  fixed_left := fun _ hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_right := fun _ hu => (Finset.mem_filter.mp hu).2.2.2
  row_norm := fun u hu => B.row_norm u (Finset.mem_filter.mp hu).1
  rowData := B.data j
  reverse := B.reverse j
  row_coeff := fun u hu => B.row_coeff u (Finset.mem_filter.mp hu).1 j

theorem UnmarkedBatch.card_eq_sum_fibers [Fintype Label]
    (B : UnmarkedBatch Label U a ε tstar T allowance i) :
    B.rows.card = ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows j J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s := B.rows) (t := Finset.univ)
    (f := fun u => ((B.witness u).label, (B.witness u).left, (B.witness u).right))
    (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type, Prod.mk.injEq, UnmarkedBatch.fiberRows] using hh

theorem UnmarkedBatch.card_bound [Fintype Label]
    (B : UnmarkedBatch Label U a ε tstar T allowance i)
    (C exponent : ℝ) (hC : 0 ≤ C) (hU : 0 < U)
    (hfiber : ∀ j J K, ∀ hne : (B.fiberRows j J K).Nonempty,
      ((B.fiber j J K hne).rows.card : ℝ) ≤ C * U ^ exponent) :
    (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 *
      C * U ^ exponent := by
  have he : (B.rows.card : ℝ) = ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C * U ^ exponent := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows j J K).Nonempty
      · exact hfiber j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Sum the actual supported-witness partition at the balanced unmarked
cutoff. This incurs only the displayed label and two dyadic-length counts. -/
theorem batch_count_from_unmarked_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm) :
    ∃ c κ K₀ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 ≤ K₀ ∧
      ∀ᶠ U : ℝ in atTop,
        ∀ (a ε T allowance C height : ℝ) (i : ℕ),
        1 < U → 1 / 2 ≤ a → 2 * a - 1 ≤ 5 / 6 → 0 ≤ ε → ε ≤ 1 / 1000 →
        0 ≤ C → 0 ≤ height → 2 * Real.pi * allowance + (3 * i : ℕ) * T ≤ height →
        ∀ {Label : Type*} [Fintype Label]
          (B : UnmarkedBatch Label U a ε (unmarkedCutoff (2 * a - 1)) T allowance i),
        (∀ j J K, ∀ hne : (B.fiberRows j J K).Nonempty,
          UnmarkedMoments (B.fiber j J K hne) c κ C height εm) →
        (B.rows.card : ℝ) ≤ (Fintype.card Label : ℝ) * (dyadicLength U : ℝ)^2 *
          fiberConstant C height K₀ * U ^ (unmarkedDensity (2 * a - 1) + 156 * ε + εm) := by
  obtain ⟨c, κ, K₀, hc, hc1, hκ, hK, hcount⟩ := count_from_unmarked_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c, κ, K₀, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance C height i hU ha hδ hε hεsmall hC hh hf Label _ B moments
  apply B.card_bound (fiberConstant C height K₀) _
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU)
  intro j J K hne
  exact hcount a ε T allowance C height i hU ha hδ hε hεsmall hC hh hf
    (B.fiber j J K hne) (moments j J K hne)

end SevenEighths.LocalMoment
end
end OAI
end
/- END ORIGINAL MODULE LocalMoment.UnmarkedBatch -/

/- BEGIN ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyClass ; sha256 344795c52e44f4f3dcafe367e387a30d6a78c9dabd5a0c69c16f35b60498d5c0 -/
section



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem actual_nonfloor_class_from_raw_moments (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost) (counts : CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → 51/100< a → a≤1 → 0≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=> ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
      rows'.Nonempty → 0≤ q ∧ q≤(2*a-1)/2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(logCost+heightCost+momentCost+
            d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
            v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) := by
  have hdmax0 : 0< dmax := hdmin.trans_le hdRange
  obtain ⟨K,hK,hcount⟩ :=
    adaptive_source_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C,hC,hphysical⟩ := actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1/100) margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh (by norm_num)
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η,hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0< Z := zero_lt_one.trans hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=> ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0< ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
      (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi hellsum W (fun _=> b) (fun _=> z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0 B
    (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) mesh hmesh (fun j=> ell j/d) Q bin
    (by linarith) (fun j _=> div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum Finset.univ ell d hellsum];positivity) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
    (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu=> hrows u (hsub hu)) (fun u hu=> hnorm u (hsub hu)) hcard i hi
    (fun u hu=> hnext u (hsub hu)) t ht
    (fun u hu=> source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost+heightCost+momentCost+
      d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6=
      (logCost+heightCost+momentCost)+(d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) by ring,
    Real.rpow_add hZp (logCost+heightCost+momentCost)]
  ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end
/- END ORIGINAL MODULE OAI.NumberTheory.DirichletL.Detector.FinalAssemblyClass -/
