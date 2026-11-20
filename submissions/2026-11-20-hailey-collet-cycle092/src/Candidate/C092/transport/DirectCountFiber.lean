/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary witness-fiber counts. Uses the original OpenAI detector
plain_fiber_count and Collet's affine source dictionary with Bebel's coupled
source. No cardinality or ordinary moment is assumed in q_plain_fiber_count. -/
import Candidate.C092.transport.DirectCountSource
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.DirectCount
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorPlainFiberCount HeckeDetectorWitnessRows
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open QRH.Record12518109Source QRH.Record12518109Count
open QRH.Record1252270103Return Cycle25ProbeFinalAssembly

/-- The affine ordinary source alone pays this actual supported-witness count.
The count face has zero lower slot width, so no extra natural moment is needed. -/
theorem affine_only_count {M : Ideal HeckeFamily.O} {H : Subgroup (HeckeFamily.O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (C height εm z : ℝ) (affine : AffineMarkedMoment F countFace C height εm)
    (hU : 1 < U) (ha : 1/2 ≤ a) (hC : 0 ≤ C) (hh : 0 ≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height)
    (hm : F.m < 1/2) (hm0 : 0 ≤ F.m) (hzpos : 0 < z) (hzmax : z ≤ 7/37)
    (hzface : z ≤ countFace.slotHi) (hzbudget : countFace.lam*z ≤ countFace.B-2*F.m) :
    (F.rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  let κ' := (1-2*F.m)/(6*z)
  have hκ'0 : 0 ≤ κ' := div_nonneg (by linarith) (by positivity)
  have he : 6*κ'*z=1-2*F.m := by dsimp [κ']; field_simp
  have hraw : ∀ selected : Finset Slot, selected ⊆ F.slots →
      2*F.m+6*κ'*(∑ s ∈ selected,F.widths s) ≤ 1 →
      ∀ j k : ℕ, j+k ≤ 2 → ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (-height) height,
        (∑ u ∈ F.rows, ‖polynomial (F.family u F.label) false
          ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
          polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
            (U^F.m) s t*F.physicalProduct selected u‖^2) ≤ C*U^(1+εm) := by
    intro selected hsel hc
    have hsum : (∑ s ∈ selected,F.widths s) ≤ z := by
      have he' : 6*κ'=(1-2*F.m)/z := by dsimp [κ']; field_simp
      have h1 : (1-2*F.m)/z*(∑ s ∈ selected,F.widths s) ≤ 1-2*F.m := by
        rw [←he']; linarith
      have hpos : 0 < 1-2*F.m := by linarith
      rw [div_mul_eq_mul_div,div_le_iff₀ hzpos] at h1
      nlinarith
    have hzero : countFace.slotLo ≤ ∑ s ∈ selected,F.widths s := by
      change 0 ≤ _
      exact Finset.sum_nonneg (fun s hs => (F.widths_pos s (hsel hs)).le)
    apply affine (by simpa only [countFace,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face] using hm0)
      (by simpa only [countFace,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face] using hm.le)
      selected hsel hzero (hsum.trans hzface)
    have hl : 0 ≤ countFace.lam := by
      dsimp [countFace,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face]
      have := QRH.Cycle090.allowances_pos.1
      positivity
    have hh := mul_le_mul_of_nonneg_left hsum hl
    linarith
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z κ' εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hzpos.le (hzmax.trans F.supply) F.fixed_bin hκ'0 hC hh hf
    (by change 2*F.m+6*κ'*z ≤ 1; linarith) hraw

/-- Actual Q ordinary cardinality count on each original source Batch fiber.
The source mesh precedes D/F, and the constants precede rows, the attaining-zero
fiber, independent heights and the requested norm-prime width. -/
theorem q_plain_fiber_count (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ → ℝ, (∀ t, 0 < t → 0 < mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
    (∀ j, D.ell j ≤ mesh D.t/200) →
    ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    1 < Z ∧ ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
    ∀ d : ℝ, (1/200 : ℝ) ≤ d → ∀ (a tstar T allowance : ℝ) (i : ℕ)
      (B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
        (Fin D.N) (Z^d) a D.ε tstar T allowance i),
    B.rows ⊆ rows → B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.widths=(fun s => D.ell s/d) →
    (∀ s, B.upper s=2) → (∀ s, (B.external s).re=17/50) →
    ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
    ∀ height z : ℝ, 0 ≤ height → (∀ s, |(B.external s).im| ≤ height) →
    1/2 ≤ a → 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    let F := B.fiber bin label left right hne
    F.m < 1/2 → 0 ≤ F.m → 0 < z → z ≤ 7/37 → z ≤ countFace.slotHi →
    countFace.lam*z ≤ countFace.B-2*F.m →
    (F.rows.card : ℝ) ≤ (192*(1+height)*(C*(1+height)^J))*
      (Z^d)^(1-2*(2*a-1)*F.m-2*F.q*z+4*D.ε+(2*a-1)*F.mesh+D.t) := by
  obtain ⟨mesh,hm,hsrc⟩ := q_count_mesh hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfine η
  obtain ⟨J,C,hC,hU⟩ := hsrc D S hfine η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hU] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label left right hne height z hheight him ha hf
  dsimp only
  intro hm hm0 hz hzmax hzface hzbudget
  have hmoment := hZ.2 rows hrows d hd a tstar T allowance i B hB hdata hprofile hwidth
    hupper hreal bin label left right hne height hheight him
  exact affine_only_count (B.fiber bin label left right hne) (C*(1+height)^J) height D.t z
    hmoment (Real.one_lt_rpow hZ.1 (by linarith)) ha (by positivity) hheight hf
    hm hm0 hz hzmax hzface hzbudget
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.q_plain_fiber_count
