/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A fixed-height original pair source pays the witness rectangle. Only
Schwartz seminorm interpolation is used; no moving-profile bound is assumed. -/
import Candidate.C092.transport.WitnessRowSup
import Candidate.C092.transport.StrongPairSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.WitnessRowSup
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set OAI OAI.SevenEighths ConcretePrimeRowBridge CanonicalRowCompletion
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open CenteredMomentSourceMass
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorDictionary
open HeckeDetectorRowwisePolynomial HeckeRowClosure
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.StrongPair
open Qrh.JointDetector WholeWordAmplification
local notation "O" => HeckeFamily.O

lemma iterated_log_support (W : ℝ → ℂ) (n : ℕ) :
    Function.support ((logProfile^[n]) W) ⊆ Function.support W := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (logProfile_support _).trans ih

lemma iterated_log_smooth (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc (1/4:ℝ) (9/4))
    (hW : ContDiff ℝ ∞ W) (n : ℕ) : ContDiff ℝ ∞ ((logProfile^[n]) W) := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact logProfile_smooth _ (1/4) (9/4) (by norm_num)
      ((iterated_log_support W n).trans hs) ih

/-- Three relative log profiles suffice for the actual rectangular derivative
chain. Constants precede real parts, common frequencies and row choices. -/
theorem log_interpolated_control (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Icc (1/4:ℝ) (9/4)) (hW : ContDiff ℝ ∞ W)
    (S : Finset (ℕ×ℕ)) :
    ∃ J : ℕ,∃ C : ℝ,0 < C ∧ ∀ n : ℕ,n ≤ 2 → ∀ σ ∈ Icc (0:ℝ) 1,∀ t : ℝ,
      sourceControl S (interpolatedProfile ((logProfile^[n]) W) (1/4) (9/4) (by norm_num)
        ((iterated_log_support W n).trans hs) (iterated_log_smooth W hs hW n) σ t) ≤ C*(1+|t|)^J := by
  choose degree C hC hb using fun q : Fin 3 => interpolatedProfile_uniform
    ((logProfile^[q.val]) W) (1/4) (9/4) (by norm_num)
    ((iterated_log_support W q.val).trans hs) (iterated_log_smooth W hs hW q.val) S
  let J := (Finset.univ : Finset (Fin 3)).sup degree
  let B := 1+∑ q : Fin 3,C q
  have hB : 0 < B := by
    have hh : 0 ≤ ∑ q : Fin 3,C q := Finset.sum_nonneg (fun q _ => (hC q).le)
    dsimp [B]; linarith
  refine ⟨J,B,hB,?_⟩
  intro n hn σ hσ t
  let q : Fin 3 := ⟨n,by omega⟩
  have hCq : C q ≤ B := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => (hC j).le) (Finset.mem_univ q)
    dsimp [B]; linarith
  have hd : degree q ≤ J := Finset.le_sup (Finset.mem_univ q)
  have h := hb q σ hσ t
  change sourceControl S _ ≤ _ at h
  simpa only [Real.norm_eq_abs] using h.trans
    (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hd) (by positivity) hB.le)

/-- Exact fixed-height source specialization. `hfixed` is precisely the
profile-uniform `finiteEnergyOn` conclusion of `PairAt` at heights `(tL,0)`.
Its row set, ordinary coefficients, long factor and marks stay fixed.
The arbitrary nonnegative weights have their explicit bound A. -/
theorem original_pair_rowwise {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (W : ℝ → ℂ) (hs : Function.support W ⊆ Icc (1/4:ℝ) (9/4)) (hW : ContDiff ℝ ∞ W)
    (controls : Finset (ℕ×ℕ)) :
    ∃ J : ℕ,∃ C : ℝ,0 < C ∧
    ∀ (Tslots : Finset Slot) (rows : Finset FreeRow) (ηL ηS : Character)
      (WL : 𝓢(ℝ,ℂ)) (hWL : Function.support (WL:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4))
      (tL XL XS K : ℝ) (hXS : 0 < XS) (hK : 0 ≤ K)
      (mark : Slot → FreeRow → ℂ),
      (∀ p : Profiles (1/4) (9/4),
        finiteEnergyOn Tslots rows ηL ηS (p.profile 0) (p.profile 1) tL 0 XL XS mark ≤
          K*(p.control controls)^2) →
    ∀ (χ : FreeRow → Character),
      (∀ u ∈ rows,∀ n,elementCoeff (χ u) n = rowTwist (elementHom ηS)
        (fixedBadMask*idealGenerator 1) 1 (1*u.val) n) →
    ∀ (weight : FreeRow → ℝ) (A height : ℝ),0 ≤ A → 0 ≤ height →
      (∀ u ∈ rows,0 ≤ weight u) → (∀ u ∈ rows,weight u ≤ A) →
    ∀ σ freq : FreeRow → ℝ,(∀ u ∈ rows,σ u ∈ Icc (0:ℝ) 1) →
      (∀ u ∈ rows,|freq u| ≤ height) →
      ∑ u ∈ rows,weight u*‖polynomial (χ u) false W XS (σ u) (freq u)*
        (original ηL (fixedBadMask*idealGenerator 1) 1 u.val WL tL XL*
          ∏ i ∈ Tslots,mark i u)‖^2 ≤
        12*A*K*(sourceControl controls WL)^2*C^2*(1+height)^(2*J+1) := by
  obtain ⟨J,C,hC,hctl⟩ := log_interpolated_control W hs hW controls
  refine ⟨J,C,hC,?_⟩
  intro Tslots rows ηL ηS WL hWL tL XL XS K hXS hK mark hfixed χ hχ
    weight A height hA hh hw hwA σ freq hσ hf
  let P : FreeRow → ℂ := fun u => original ηL (fixedBadMask*idealGenerator 1) 1 u.val WL tL XL*
    ∏ i ∈ Tslots,mark i u
  let E := A*K*(sourceControl controls WL)^2*C^2*(1+height)^(2*J)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he (n : ℕ) (hn : n ≤ 2) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1)
      (y : ℝ) (hy : y ∈ Icc (-height) height) :
      ∑ u ∈ rows,weight u*‖polynomial (χ u) false ((logProfile^[n]) W) XS x y*P u‖^2 ≤ E := by
    let V := interpolatedProfile ((logProfile^[n]) W) (1/4) (9/4) (by norm_num)
      ((iterated_log_support W n).trans hs) (iterated_log_smooth W hs hW n) x y
    have hVs : Function.support (V:ℝ→ℂ) ⊆ Icc (1/4:ℝ) (9/4) := by
      intro z hz
      rw [show (V:ℝ→ℂ) = twistProfile ((logProfile^[n]) W) x y from funext (fun z =>
        interpolatedProfile_apply _ _ _ _ _ _ _ _ z)] at hz
      exact ((twistProfile_support _ _ _).trans ((iterated_log_support W n).trans hs)) hz
    let p : Profiles (1/4) (9/4) :=
      ⟨fun j => if j=0 then WL else V,fun j=>by fin_cases j <;> simp only [ite_true,Fin.zero_eta,Fin.mk_one,one_ne_zero,ite_false] <;> assumption⟩
    have hpoint (u : FreeRow) (hu : u ∈ rows) :
        polynomial (χ u) false ((logProfile^[n]) W) XS x y =
          original ηS (fixedBadMask*idealGenerator 1) 1 u.val V 0 XS := by
      rw [plain_polynomial_eq_row ηS (χ u) (fixedBadMask*idealGenerator 1) 1 u.val
        (hχ u hu) _ XS x y hXS]
      rw [show twistProfile ((logProfile^[n]) W) x y = (V:ℝ→ℂ) from
        funext (fun z => (interpolatedProfile_apply _ _ _ _ _ _ _ _ z).symm)]
      rfl
    have hsum : (∑ u ∈ rows,‖polynomial (χ u) false ((logProfile^[n]) W) XS x y*P u‖^2) =
        finiteEnergyOn Tslots rows ηL ηS WL V tL 0 XL XS mark := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hpoint u hu]
      simp only [P,norm_mul,mul_pow,Complex.norm_prod,Finset.prod_pow]
      ring
    have hWL0 := sourceControl_nonneg controls WL
    have hV0 := sourceControl_nonneg controls V
    have hp := hfixed p
    have hv := hctl n hn x hx y
    have hy' : |y| ≤ height := abs_le.mpr hy
    have hv' : sourceControl controls V ≤ C*(1+height)^J :=
      hv.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) J) hC.le)
    have hunweighted : (∑ u ∈ rows,‖polynomial (χ u) false ((logProfile^[n]) W) XS x y*P u‖^2) ≤
        K*(sourceControl controls WL)^2*C^2*(1+height)^(2*J) := by
      rw [hsum]
      apply hp.trans
      simp only [Profiles.control,p,ite_true,one_ne_zero,ite_false]
      calc
        _ ≤ K*(sourceControl controls WL*(C*(1+height)^J))^2 := by gcongr
        _ = _ := by rw [mul_pow,mul_pow,←pow_mul];ring
    calc
      _ ≤ ∑ u ∈ rows,A*‖polynomial (χ u) false ((logProfile^[n]) W) XS x y*P u‖^2 :=
        Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_right (hwA u hu) (sq_nonneg _))
      _ = A*∑ u ∈ rows,‖polynomial (χ u) false ((logProfile^[n]) W) XS x y*P u‖^2 := (Finset.mul_sum _ _ _).symm
      _ ≤ E := by dsimp [E];convert mul_le_mul_of_nonneg_left hunweighted hA using 1 <;> ring
  have hcover : ∀ I : Ideal O,I ≠ 0 → W ((I.absNorm:ℝ)/XS) ≠ 0 → I ∈ idealBall ((9/4:ℝ)*XS) := by
    intro I hI hWI
    exact (mem_idealBall _ _).mpr ⟨hI,(div_le_iff₀ hXS).mp (hs hWI).2⟩
  have h := weighted_height rows χ W XS hXS _ hcover weight hw P height E hh hE σ freq hσ hf he
  convert h using 1 <;> dsimp [E,P]
  rw [pow_add,pow_one,←mul_assoc]
  ring

#print axioms original_pair_rowwise
end
end QRH.Cycle092.WitnessRowSup
