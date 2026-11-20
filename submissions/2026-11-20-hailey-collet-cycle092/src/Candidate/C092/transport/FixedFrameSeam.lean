/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
On the native fixed frame, integrate each actual physical polynomial bound
over the original finite rows and pass to the original summable series. -/
import Candidate.C092.transport.FixedPhysicalClassLedgerFinite
import Candidate.C092.transport.FixedFourierH15RowSubpower
import Candidate.C092.transport.FirstGroupBudget
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge ConcreteTraceCRT RayFourExpansion
open CenteredMomentHeckeSlots CenteredMomentFiniteProfileExceptional CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization CenteredMomentCommonProfile
open CenteredMomentAddedZeroUniform
open QRH.SilDensitySplit.CubeFree FP MixedPrincipalPair MixedCommonRestriction MixedPrincipalWindow
open CanonicalQuadraticSieve CenteredMomentChildRows Packet
open Packet.Grouped
open QRH.Cycle092.FixedFramePacking QRH.Cycle092.FixedCubeGauss QRH.Cycle092.FixedFourierH15
open QRH.Cycle092.SignedCenter
namespace QRH.Cycle092.FixedFrameSeam
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {L mesh Z:ℝ} {θ:GData L}
local instance c092LocalInst_Candidate_C092_transport_FixedFrameSeam_b929b900ec20d0b8_001 {κ:Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _

/-- Exact pointwise representation recovered from a native class label;
the displayed height conductor is read off that genuine row datum. -/
def RowData (s:Source (Fin θ.N) θ.a θ.b) (ha:0<θ.a) (ω₁ ω₂ η:Character)
    (r:GSrc θ mesh Z) (Q:Id) (v Bcap:ℝ) (x:GLabel θ mesh Z) (hG:Supported x.G) (z:O) : Prop :=
  ∃ (D:FixedCubeDatum) (ψ:Character) (χ:RayCharacter),
    D.Q=Q ∧ D.η=childCharacter ψ χ ∧ D.m=nativeSourceMask s ∧
    (HeckeRowClosure.rowConductorBound D.η D.m 1 (D.A*D.z):ℝ)  ≤  Z^Bcap ∧
    FixedPhysicalClassLedger.rowEnergy s ha ω₁ ω₂ η r Q x v z =
      ‖nativeRowPolynomial s ha D ω₁ ω₂ ψ χ x.G hG x.D v‖^2*
        (ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re

theorem full_fixed_series (θ:GData L) (ω₁ ω₂:Character) (N:ℕ) (hN:θ.N ≤ N)
    (ε Bcap:ℝ) (hε:0<ε) (hB:0 ≤ Bcap) :
    ∃ J:ℕ,∃ S:Finset (ℕ×ℕ),(0,0)∈S ∧ ∀Q:Id,∃ C:ℝ,0<C ∧ ∀ᶠ Z:ℝ in atTop,
    1<Z ∧ ∀ (mesh:ℝ) (r:GSrc θ mesh Z) (s:Source (Fin θ.N) θ.a θ.b)
      (η:Character) (labels:Finset (GLabel θ mesh Z)) (v H Mmin Mmax εg A₀ c u' err:ℝ),
    (Q≠0) → (Q≠⊤) → (Q  ≤  Ideal.span {(72:O)}) →
    Second.AdmissibleGroup (gFrame L θ mesh η Z) Mmin Mmax mesh εg Z r labels H →
    2 ≤ Z → mesh ≤ 1 → 0 ≤  mesh →
    A₀ ≤ 9179599/10000000 → u' ≤ (QRH.SourceCertificate.u:ℝ) →
    r.colLog ≤ A₀-c-u'+err → 1-6*u' ≤ H+err →
    max 0 (115/1000-c) ≤ Real.logb Z (max 1 s.L)+err →
    r.vol=FixedFourierH15.sourceVolume s →
    ∀ fit:∀x∈labels,Fits η r x, ∀ good:∀x∈labels,Supported x.G,
    (∀x∈labels,x.d=s.d) →
    (∀x∈labels,(x.G.absNorm:ℝ) ≤ Z^Bcap ∧ (x.D.absNorm:ℝ) ≤ Z^Bcap) →
    (∀x∈labels,∀ B:commonAlloc s x.G,∀ E:fullPrimaryAlloc s x.G B x.D,
      (s.Fhole.absNorm:ℝ)*(∏i:liveIndices E.val,2*s.P i.val.val)*(s.R.absNorm:ℝ)*
          (x.G.absNorm:ℝ)*(x.D.absNorm:ℝ)  ≤  Z^Bcap) →
    (∀x (hx:x∈labels) z,FixedPhysicalClassLedger.rowEnergy s θ.ha0 ω₁ ω₂ η r Q x v z≠0 →
        RowData s θ.ha0 ω₁ ω₂ η r Q v Bcap x (good x hx) z) →
    let A:=C*fixedMarkCost s*(sourceControl S s.W₁*sourceControl S s.W₂)^2*Z^ε*
      (1+‖s.t₁+v‖+‖s.t₂+v‖)^(2*J)
    ∑ x∈labels,gWeight x*FixedPhysicalClassLedger.gEnergy s θ.ha0 ω₁ ω₂ η r Q x v  ≤ 
      (Fintype.card DictIdx:ℝ)*(768*(6:ℝ)^(UniqueFactorizationMonoid.normalizedFactors Q).toFinset.card)*A*
        Z^(r.colLog+r.twistLog+u'-(3036/100000)+3*mesh+Real.logb Z 2+(17/6)*err+εg/8) := by
  obtain ⟨J,S,hS,hbound⟩:=original_row_H15_subpower (ι:=Fin θ.N) θ.ha0 (zero_le_one.trans θ.hb1) ω₁ ω₂ N
    (by simpa using hN) ε Bcap hε hB
  refine ⟨J,S,hS,?_⟩
  intro Q; obtain ⟨C,hC,hU⟩:=hbound Q
  refine ⟨C,hC,hU.mono ?_⟩
  intro Z hz
  refine ⟨hz.1,?_⟩
  intro mesh r s η labels v H Mmin Mmax εg A₀ c u' err hQ₀ hQt hQ72 hadm hZ hm1 hm hA hu hcol hfill hLf hvol fit good hd hcap hbud hdata
  let E:=FixedPhysicalClassLedger.rowEnergy s θ.ha0 ω₁ ω₂ η r Q
  let A:=C*fixedMarkCost s*(sourceControl S s.W₁*sourceControl S s.W₂)^2*Z^ε*(1+‖s.t₁+v‖+‖s.t₂+v‖)^(2*J)
  have hA0:0 ≤ A:=by
    have hz0:=zero_lt_one.trans hz.1
    have hmk:=fixedMarkCost_nonneg s
    dsimp [A];positivity
  apply FixedPhysicalClassLedger.finite_budget_to_frame s θ.ha0 ω₁ ω₂ η r Q labels fit v
  intro F
  let rows:=fun x:GLabel θ mesh Z=>F.filter (fun z=>E x v z≠0)
  have same (x):∑z∈F,E x v z = ∑z∈rows x,E x v z := by
    rw [Finset.sum_filter]; apply Finset.sum_congr rfl;intro z hz;split_ifs with h
    · rfl
    · exact not_ne_iff.mp h
  change (∑x∈labels,gWeight x*(prefixNorm x*r.norm*∑z∈F,E x v z)) ≤ _
  simp_rw [same]
  have fixed (x) (hx:x∈labels) (z) (hz:z∈rows x) : FixedPhysicalClassLedger.initialFixed (x.char r) Q z := by
    by_contra hn;apply (Finset.mem_filter.mp hz).2
    simp only [E,FixedPhysicalClassLedger.rowEnergy,dif_pos (fit x hx),if_neg hn]
  have radial (x) (hx:x∈labels) (z) (hz:z∈rows x) : (ballProfile (‖eisEmbedding z‖^2/dyadicScale (x.n 1))).re≠0 := by
    intro he; apply (Finset.mem_filter.mp hz).2
    simp only [E,FixedPhysicalClassLedger.rowEnergy,dif_pos (fit x hx),if_pos (fixed x hx z hz),he,mul_zero]
  apply fixed_filled_admissible r η Q hQ₀ hQt hQ72 fixedBadMask fixedBadMask_ne_zero
    (dvd_mul_right _ _) (dvd_mul_left _ _) labels rows (fun x z=>E x v z) H Mmin Mmax εg A A₀ c u' s.L err
    hadm hZ hm1 hA0 hA hu hcol hfill hm hLf
    (fun x hx z hz=>⟨fit x hx,fixed x hx z hz⟩)
    (fun x hx z hz=>fixed_ball_support z (x.n 1) (radial x hx z hz))
  intro x hx z hrow
  obtain ⟨D,ψ,χ,hQ,hη,hmD,hcond,he⟩:=hdata x hx z (Finset.mem_filter.mp hrow).2
  have hh:=hz.2 s D hQ hcond x.G x.D (good x hx) (fit x hx).D_sq (hcap x hx).1 (hcap x hx).2
    (hbud x hx) ψ χ hη hmD v
  have hp:FixedFourierH15.sourcePrefix s x.G x.D=prefixNorm x:=by
    unfold FixedFourierH15.sourcePrefix prefixNorm
    rw [hd x hx];ring
  calc
    _  ≤  ‖nativeRowPolynomial s θ.ha0 D ω₁ ω₂ ψ χ x.G (good x hx) x.D v‖^2 :=
      he.trans_le (mul_le_of_le_one_right (sq_nonneg _) (ballProfile_le_one _))
    _  ≤  _ := hh.trans_eq (by dsimp [A];rw [hp,hvol];ring)

#print axioms full_fixed_series
end QRH.Cycle092.FixedFrameSeam
