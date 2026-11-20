/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Strongest original source count on one actual supported-zero fiber. Source
suppliers retain the original OpenAI/Collet/Gao and coupled-source attributions. -/
import Candidate.C092.transport.DirectCountMarkedInverse
import Candidate.C092.transport.ActualMixedPriceCount
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.DirectCount
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows
open QRH.Record12518109Count Cycle25ProbeFinalAssembly

/-- Three genuine original cardinality bounds, promoted before selecting their
maximum saving. All three count the identical original source Batch fiber;
none of the cardinality estimates or source moments is a premise. This does
not identify these savings with the extra centered H8 face. -/
theorem q_strongest_source_fiber_count
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ → ℝ, (∀ t, 0 < t → 0 < mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
    (∀ j, D.ell j ≤ mesh D.t/200) →
    ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
    ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a tstar T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a D.ε tstar T allowance i),
    B.rows ⊆ rows → B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.widths=(fun s => D.ell s/d) →
    B.upper=(fun _ => 2) → (∀ s, (B.external s).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height zI zO : ℝ, 0 ≤ height → (∀ s, |(B.external s).im| ≤ height) →
    1/2 ≤ a → 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne
    0 ≤ F.r → F.r ≤ 2 → 0 ≤ zI → zI ≤ 7/37 → F.r+2*zI < 1 → 2*F.r+8*zI < 3 →
    F.m < 1/2 → 0 ≤ F.m → 0 < zO → zO ≤ 7/37 → zO ≤ countFace.slotHi →
    countFace.lam*zO ≤ countFace.B-2*F.m →
    (F.rows.card : ℝ) ≤ (C*(1+height)^J)*
      (Z^d)^(1+(4*D.ε+(2*a-1)*F.mesh+D.t)-
        QRH.Cycle092.ActualMixedPriceCount.deficit
          ((2*a-1)*F.r-(HeckeInverseAmplification.sourceExponent F.r-1))
          ((2*a-1)*F.r+2*F.q*zI) (2*(2*a-1)*F.m+2*F.q*zO)) := by
  obtain ⟨mesh,hm,hOrd⟩ := q_plain_fiber_count hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfine
  obtain ⟨K,hK,Ji,hInv⟩ := source_inverse_fiber_count D S
  obtain ⟨Jm,hMarked⟩ := source_marked_inverse_fiber_count D S
  intro η
  obtain ⟨Jo,Co,hCo,hOrd⟩ := hOrd D S hfine η
  obtain ⟨Ci,hCi,hInv⟩ := hInv η
  obtain ⟨Cm,hCm,hMarked⟩ := hMarked η
  let CS := 1+Co+Ci+Cm
  let JS := Jo+Ji+Jm
  let CC := 192*CS*max 1 K
  have hCS : 0 < CS := by dsimp [CS]; linarith
  have hCC : 0 < CC := by dsimp [CC]; have : 0 < max 1 K := lt_of_lt_of_le zero_lt_one (le_max_left _ _); positivity
  refine ⟨JS+1,CC,hCC,?_⟩
  filter_upwards [hOrd,hInv,hMarked] with Z hOrd hInv hMarked
  refine ⟨hOrd.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label left right hne height zI zO hh him ha hf
  dsimp only
  intro hr hr2 hzI hzImax hI1 hI2 hm hm0 hzO hzOmax hzOface hzObudget
  let F := B.fiber bin label left right hne
  have hU : 1 < Z^d := Real.one_lt_rpow hOrd.1 (by linarith)
  have hb : 1 ≤ 1+height := by linarith
  have promote (L k c : ℝ) (j : ℕ) (hL : 0 ≤ L) (hL' : L ≤ 192)
      (hk : 0 ≤ k) (hk' : k ≤ max 1 K) (hc : 0 ≤ c) (hc' : c ≤ CS) (hj : j ≤ JS) :
      L*(1+height)*((c*(1+height)^j)*k) ≤ CC*(1+height)^(JS+1) := by
    have hp := pow_le_pow_right₀ hb hj
    calc
      _ ≤ 192*(1+height)*((CS*(1+height)^JS)*max 1 K) := by gcongr
      _ = _ := by dsimp [CC]; rw [pow_succ]; ring
  have pI := promote 12 K Ci Ji (by norm_num) (by norm_num) hK (le_max_right _ _)
    hCi.le (by dsimp [CS]; linarith) (by dsimp [JS]; omega)
  have pM := promote 12 1 Cm Jm (by norm_num) (by norm_num) (by norm_num) (le_max_left _ _)
    hCm.le (by dsimp [CS]; linarith) (by dsimp [JS]; omega)
  have pO := promote 192 1 Co Jo (by norm_num) (by norm_num) (by norm_num) (le_max_left _ _)
    hCo.le (by dsimp [CS]; linarith) (by dsimp [JS]; omega)
  have iCount := hInv.2 d hd a D.ε tstar T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height hh ha hf hr hr2
  have mCount := hMarked.2 d hd a D.ε tstar T allowance i B hdata hprofile hupper hwidth hreal
    bin label left right hne height zI hh ha hf hzI hzImax hI1 hI2
  have oCount := hOrd.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    (fun s => congrFun hupper s) hreal bin label left right hne height zO hh him ha hf
    hm hm0 hzO hzOmax hzOface hzObudget
  have hδ : 0 ≤ 2*a-1 := by linarith
  have heps : 0 ≤ D.ε := D.epsilon_pos.le
  have hmesh : 0 ≤ (2*a-1)*F.mesh := mul_nonneg hδ F.mesh_nonneg
  have cI : (F.rows.card : ℝ) ≤ CC*(1+height)^(JS+1)*
      (Z^d)^(1+(4*D.ε+(2*a-1)*F.mesh+D.t)-
        ((2*a-1)*F.r-(HeckeInverseAmplification.sourceExponent F.r-1))) := by
    apply iCount.trans
    apply mul_le_mul pI _ (by positivity) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hU.le
    linarith
  have cM : (F.rows.card : ℝ) ≤ CC*(1+height)^(JS+1)*
      (Z^d)^(1+(4*D.ε+(2*a-1)*F.mesh+D.t)-((2*a-1)*F.r+2*F.q*zI)) := by
    apply mCount.trans
    apply mul_le_mul (by simpa only [mul_one] using pM) _ (by positivity) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hU.le
    linarith
  have cO : (F.rows.card : ℝ) ≤ CC*(1+height)^(JS+1)*
      (Z^d)^(1+(4*D.ε+(2*a-1)*F.mesh+D.t)-(2*(2*a-1)*F.m+2*F.q*zO)) := by
    apply oCount.trans
    apply mul_le_mul (by simpa only [mul_one] using pO) _ (by positivity) (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hU.le
    linarith
  exact ActualMixedPriceCount.strongest_three_count F.rows (Z^d)
    (1+(4*D.ε+(2*a-1)*F.mesh+D.t)) (CC*(1+height)^(JS+1)) _ _ _ cI cM cO
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.q_strongest_source_fiber_count
