/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original balanced old count, supplied on actual source dictionaries. -/
import Candidate.C092.transport.DirectCountFields
import Candidate.C092.transport.DirectPrices
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.Adaptive
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.PacketJoin
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorFixedAmplitudeCount HeckeDetectorAmplitudeFirst
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Record1252270103Return QRH.Cycle090 QRH.Cycle092.Direct QRH.Cycle092.DirectCount

/-- The analytic inputs are the actual source moments supplied by
q_actual_count_fields. No count or energy estimate is a premise. -/
theorem q_old_batch_count (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ mesh : ℝ → ℝ, (∀ t, 0 < t → 0 < mesh t) ∧
    ∀ (D : Cycle25.Weighted.MomentData) (S : WeightedSourceData D),
    (∀ j, D.ell j ≤ mesh D.t/200) →
    (∀ j, D.ell j ≤ Cycle25.sourceMesh D.t/200) → D.ε ≤ 1/10000000 →
    ∀ κplain : ℝ, 7/10 ≤ κplain → κplain ≤ 3/4 →
    2*HeckeZeroSupremum.beta-1 ≤ κplain →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : Character, ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ rows : Finset FreeRow, (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
    ∀ d : ℝ, (1/200 : ℝ) ≤ d →
    ∀ (a T allowance ν height q : ℝ) (i : ℕ), 51/100 < a → 2*a-1 ≤ 3/4 →
    0 < ν → ν ≤ 1/10000000 → 0 ≤ height →
    2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
    ∀ B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
      (Fin D.N) (Z^d) a D.ε (Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain) T allowance i,
    B.rows.Nonempty → B.rows ⊆ rows →
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
    B.profile=(fun _ x => (S.w x : ℂ)) → B.widths=(fun s => D.ell s/d) →
    B.upper=(fun _ => 2) → (∀ s, (B.external s).re=17/50) →
    (∀ s, |(B.external s).im| ≤ height) →
    (∀ u ∈ B.rows, rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
      (physical S.modulus ⊤ (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
    (B.rows.card : ℝ) ≤
      (Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)) : ℝ)*
      (dyadicLength (Z^d) : ℝ)^2*fiberConstant (C*(1+height)^J) height K*
      (Fintype.card B.Bin : ℝ)*
      (Z^d)^(Cycle25DetectorRowCount.rowCount (2*a-1) (q/(2*a-1)) κplain+159*D.ε+D.t+B.mesh+7*ν) := by
  obtain ⟨mesh,hm,hfields⟩ := q_actual_count_fields hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfineA hfine hεsmall κ hk hk1 hkβ
  obtain ⟨c,κi,K,hc,hc1,hκi,hK,hcount⟩ := Cycle25ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments
    S.modulus ⊤ le_top S.S S.w S.smooth S.compact S.positive_support
    (fun y => (S.bounded y).1) S.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) S.support (fun y => (S.bounded y).2) D.t D.t_pos
  obtain ⟨U0,hU0⟩ := eventually_atTop.mp hcount
  have hscaled : ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, (1/200 : ℝ) ≤ d → U0 ≤ Z^d := by
    filter_upwards [(tendsto_rpow_atTop (by norm_num : 0 < (1/200 : ℝ))).eventually
      (eventually_ge_atTop U0),eventually_ge_atTop (1 : ℝ)] with Z hZ hZone
    intro d hd
    exact hZ.trans (Real.rpow_le_rpow_of_exponent_le hZone hd)
  refine ⟨K,hK,?_⟩
  intro η
  obtain ⟨J,C,hC,hsource⟩ := hfields D S hfineA hfine κ hk hk1 hkβ c κi hc hκi η
  refine ⟨J,C,hC,?_⟩
  filter_upwards [hsource,hscaled] with Z hsource hscaled
  refine ⟨hsource.1,?_⟩
  intro rows hrows d hd a T allowance ν height q i ha hδhi hν hνhi hh hf
    B hne hB hdata hprofile hwidth hupper hreal him hq
  have hU : 1 < Z^d := Real.one_lt_rpow hsource.1 (by linarith)
  have hc' := hU0 (Z^d) (hscaled d hd) a D.ε T allowance κ ν
    (C*(1+height)^J) height q i hU ha hδhi D.epsilon_pos.le (by linarith)
    hk hk1 hν (by positivity) hh hf B hne hq (by
      intro bin label left right hne
      exact (hsource.2 rows hrows d hd a _ T allowance i B hB hdata hprofile hwidth
        hupper hreal bin label left right hne height hh him).1)
  simp only [←Nat.card_eq_fintype_card] at hc' ⊢
  exact hc'

/-- Exact identification with the old certificate's original rational count. -/
lemma old_rowCount_eq (δ p κ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3/4)
    (hp : 0 ≤ p) (hp' : p ≤ 1/2) (hk : 7/10 ≤ κ) (hk' : κ ≤ 3/4) :
    Cycle25DetectorRowCount.rowCount δ p κ = countN .old sourceCost κ δ p/countJ .old sourceCost κ δ p := by
  have hden := Cycle25DetectorRowCount.denominator_lower hp hp' hk hk'
  have hweight := Cycle25DetectorRowCount.coefficient_nonneg hp hp' hk hk'
  have hd : Cycle25DetectorRowCount.denominator p κ ≠ 0 := by linarith
  have hjEq : countJ .old sourceCost κ δ p =
      Cycle25DetectorRowCount.V δ*Cycle25DetectorRowCount.denominator p κ+
      δ*Cycle25DetectorRowCount.primeWeight p κ := by
    unfold countJ Cycle25DetectorRowCount.V Cycle25DetectorRowCount.denominator
      Cycle25DetectorRowCount.primeWeight Cycle25DetectorRowCount.b
    ring
  have hj : 0 < countJ .old sourceCost κ δ p := by
    rw [hjEq]
    have hb := Cycle25DetectorRowCount.b_bounds hp hp' hk hk'
    have hw : 0 ≤ Cycle25DetectorRowCount.primeWeight p κ := by
      unfold Cycle25DetectorRowCount.primeWeight
      exact mul_nonneg (by linarith) (by linarith [hb.2.2.2])
    exact add_pos_of_pos_of_nonneg
      (mul_pos (by unfold Cycle25DetectorRowCount.V;linarith) (by linarith)) (mul_nonneg hδ hw)
  have hsum : Cycle25DetectorRowCount.V δ+δ*Cycle25DetectorRowCount.coefficient p κ =
      countJ .old sourceCost κ δ p/Cycle25DetectorRowCount.denominator p κ := by
    rw [hjEq]
    unfold Cycle25DetectorRowCount.coefficient
    field_simp [hd]
  have hn : countN .old sourceCost κ δ p = (1-δ)*countJ .old sourceCost κ δ p+
      δ*Cycle25DetectorRowCount.primeWeight p κ*Cycle25DetectorRowCount.V δ/2 := by
    simp only [countN,Cycle25DetectorRowCount.primeWeight,Cycle25DetectorRowCount.V,Cycle25DetectorRowCount.b]
  unfold Cycle25DetectorRowCount.rowCount
  rw [hsum,hn]
  unfold Cycle25DetectorRowCount.coefficient
  field_simp [hd,hj.ne']
  <;> ring

end QRH.Cycle092.PacketJoin
#print axioms QRH.Cycle092.PacketJoin.q_old_batch_count
#print axioms QRH.Cycle092.PacketJoin.old_rowCount_eq
