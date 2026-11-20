/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual original M.4 native Batch cardinality, including long inverse and the
ordinary near-half tail, using Collet's original piecewise witness count. -/
import Candidate.C092.transport.DirectCountFields
import Candidate.C092.transport.DirectCountNativeAlgebra
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Count.FixedAmplitude
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical BigOperators
open Filter Set
namespace QRH.Cycle092.DirectCount
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open HeckeDetectorRawFiber HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection
open HeckeDetectorFixedAmplitudeCount HeckeDetectorAmplitudeFirst
open QRH.Record12518109Count Cycle25ProbeFinalAssembly
open QRH.Record1252270103Return QRH.Cycle090 QRH.Cycle092.Direct

/-- Sum a constant exponent over the genuine finite Batch partition. Keeping
this identity abstract avoids unfolding a live cutoff during reassociation. -/
private theorem constant_batch_card {M : Ideal HeckeFamily.O} {H : Subgroup (HeckeFamily.O ⧸ M)ˣ}
    {Label Slot : Type*} [Fintype Label] {U a ε tstar T allowance : ℝ} {i : ℕ}
    (B : HeckeDetectorBatch.Batch M H Label Slot U a ε tstar T allowance i)
    (C E : ℝ) (hC : 0 ≤ C) (hU : 0 < U)
    (hf : ∀ bin label left right, ∀ hne : (B.fiberRows bin label left right).Nonempty,
      ((B.fiber bin label left right hne).rows.card : ℝ) ≤ C*U^E) :
    (B.rows.card : ℝ) ≤ (Nat.card Label : ℝ)*(dyadicLength U : ℝ)^2*C*
      (Nat.card B.Bin : ℝ)*U^E := by
  have hb := B.card_bound C (fun _ => E) hC hU hf
  simpa only [Nat.card_eq_fintype_card,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb

/-- Genuine native R=countN/countJ on the actual original Batch, with the
original crossing cutoff and all finite label/bin/dyadic factors retained.
There is no count or source-moment premise. All tail cases are handled by the
original count_from_piecewise_moments after its moments are supplied here. -/
theorem q_native_batch_count (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
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
    (∀ j : Fin 15, 0 < nativeGuard j sourceCost (2*a-1) (q/(2*a-1))) →
    ∀ B : HeckeDetectorBatch.Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤))
      (Fin D.N) (Z^d) a D.ε (nativeCutoff sourceCost (2*a-1) (q/(2*a-1))) T allowance i,
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
      (Z^d)^(nativeValue sourceCost (2*a-1) (q/(2*a-1))+159*D.ε+D.t+B.mesh+7*ν) := by
  obtain ⟨mesh,hm,hfields⟩ := q_actual_count_fields hβ
  refine ⟨mesh,hm,?_⟩
  intro D S hfineA hfine hεsmall κ hk hk1 hkβ
  obtain ⟨c,κi,K,hc,hc1,hκi,hK,hcount⟩ := count_from_piecewise_moments
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
  intro rows hrows d hd a T allowance ν height q i ha hδhi hν hνhi hh hf hg
    B hne hB hdata hprofile hwidth hupper hreal him hq
  have hδ : 0 < 2*a-1 := by linarith
  have ha' : 1/2 ≤ a := by linarith
  have hU : 1 < Z^d := Real.one_lt_rpow hsource.1 (by linarith)
  have hqb := batch_mean_bounds B hne ha' q hq
  have hp0 : 0 ≤ q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have nd := native_data hδ.le hp0 hg
  have hs := source_contact_guards.1
  have hs' := source_contact_guards.2.1
  have hLam : 1 < countFace.lam := by change 1 < 2+10*sourceCost; linarith
  have hlo : 0 ≤ nativeLo := by
    dsimp [nativeLo,nativeLower]
    nlinarith [sq_nonneg sourceCost]
  have hcap : nativeCap ≤ countFace.slotHi := by dsimp [nativeCap]; linarith
  have hcapsmall : nativeCap ≤ 7/37 := by
    change 3/20-1000*sourceCost/1143-1/10000000 ≤ 7/37
    linarith
  simp only [← Nat.card_eq_fintype_card]
  exact constant_batch_card B (fiberConstant (C*(1+height)^J) height K)
    (nativeValue sourceCost (2*a-1) (q/(2*a-1))+159*D.ε+D.t+B.mesh+7*ν)
    (fiberConstant_bounds (C*(1+height)^J) height K (by positivity) hh hK).1
    (zero_lt_one.trans hU) (by
      intro bin label left right hne
      let F := B.fiber bin label left right hne
      have hFq : F.q=q := fiber_mean_eq B q hq bin label left right hne
      have hfield := hsource.2 rows hrows d hd a _ T allowance i B hB hdata hprofile hwidth
        hupper hreal bin label left right hne height hh him
      have hc' := hU0 (Z^d) (hscaled d hd)
        countFace.B countFace.lam nativeCap countFace.slotHi nativeLo nativeHi
        hLam hlo (by norm_num [nativeHi]) (by norm_num [nativeHi]) hcap hcapsmall
        a D.ε (nativeCutoff sourceCost (2*a-1) (q/(2*a-1))) T allowance κ ν
        (C*(1+height)^J) height i hU ha hδhi D.epsilon_pos.le (by linarith)
        nd.cutoffLo nd.cutoffHi hk hk1 hν (by linarith) (by positivity) hh hf F
        (nativeCross sourceCost (2*a-1) (q/(2*a-1)))
        (nativeValue sourceCost (2*a-1) (q/(2*a-1))) nd.crossLo nd.crossHi
        (by linarith [nd.plainBuffer])
        (by simpa only [hFq] using native_cross_identity sourceCost (2*a-1) (q/(2*a-1)) nd.Dpos nd.Jpos)
        (by simpa only [hFq] using nd.plainCrossing)
        (by simpa only [hFq] using nd.tail κ hk hk1)
        (nd.widths ν hνhi) hfield.1 (by
          simpa only [countFace,Qrh.TwoSlot.AnchorContinuum.PositiveSource.face,broadFace] using hfield.2)
      have hlong := native_long_identity sourceCost (2*a-1) (q/(2*a-1)) nd.Jpos
      rw [hlong,max_self] at hc'
      exact hc')
end QRH.Cycle092.DirectCount
#print axioms QRH.Cycle092.DirectCount.q_native_batch_count
