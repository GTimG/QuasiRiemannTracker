import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.ActualUnmarkedInputs
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.LocalMoment.PlainUnmarkedAdapter
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.LocalMoment
universe u
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount
open HeckeDetectorDyadicProfiles HeckeDetectorRawFiber
open CenteredMomentDetectorPlainStateDictionary
open ProbeHighRowFamily

/-- A finite inducing dictionary is chosen before the scale and independent height. -/
structure FixedUnmarkedDictionary (Label : Type*) where
  base : Label → Character
  fixedIdeal : Label → Ideal O
  nonzero : ∀ j, fixedIdeal j ≠ 0
  proper : ∀ j, fixedIdeal j ≠ ⊤
  divides72 : ∀ j, fixedIdeal j ≤ Ideal.span {(72 : O)}
  dividesBase : ∀ j, fixedIdeal j ≤ (base j).modulus

def FixedUnmarkedDictionary.data {Label : Type*} (D : FixedUnmarkedDictionary Label) :
    Label → RowData := fun j => momentData (D.base j)

/-- The batch moments are actual analytic inputs, including the finitely many
fixed-inducing free cores. The height degree precedes the dictionary; the constant and the common threshold follow it
and precede every bin and height. -/
theorem fixed_dictionary_actual_batch_moments {Label : Type u} [Fintype Label]
    (c κ εm : ℝ)
    (hc : 0 < c) (hκ : 0 < κ) (hεm : 0 < εm)
    (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∀ D : FixedUnmarkedDictionary Label, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ {a ε tstar T allowance : ℝ} {i : ℕ},
      1 ≤ tstar → tstar ≤ 3/2 → 0 ≤ ε → ε ≤ 1/1000 →
      ∀ (B : UnmarkedBatch Label U a ε tstar T allowance i), B.data = D.data →
      ∀ height : ℝ, 0 ≤ height →
      ∀ j left right, ∀ hne : (B.fiberRows j left right).Nonempty,
        UnmarkedMoments (B.fiber j left right hne) c κ (C * (1 + height)^J) height εm := by
  obtain ⟨Jp, hJp⟩ := fixed_unmarked_plain.{u} εm hεm hβ
  obtain ⟨Ji, hJi⟩ := fixed_family_inverse_raw (Label := Label) c κ hc hκ
  refine ⟨Ji + Jp, fun D => ?_⟩
  have hp (j : Label) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ {a ε tstar T allowance : ℝ} {i : ℕ} {L : Type u}
        (F : UnmarkedFiber U a ε tstar T allowance i L),
      F.m ≤ 3/4 → F.rowData = momentData (D.base j) →
      ∀ height : ℝ, 0 ≤ height → ∀ n k : ℕ, n + k ≤ 2 →
      ∀ σ ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (-height) height,
        (∑ u ∈ F.rows, ‖HeckeDyadic.polynomial (F.family u F.label) false
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) positiveAnnular) (U^F.m) σ t *
          HeckeDyadic.polynomial (F.family u F.label) false
          ((HeckeDetectorRowwisePolynomial.logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2) ≤
          C * (1 + height)^Jp * U^(max 1 (2 * F.m) + εm) :=
    hJp (D.base j) (D.fixedIdeal j) (D.nonzero j) (D.proper j) (D.divides72 j) (D.dividesBase j)
  choose Cp hCp hp using hp
  obtain ⟨Ci, hCi, hi⟩ := hJi D.data
  let C : ℝ := Ci + ∑ j, Cp j
  have hsum : 0 ≤ ∑ j, Cp j := Finset.sum_nonneg (fun j _ => (hCp j).le)
  have hC : 0 < C := by dsimp [C]; linarith
  have hiJ : Ji ≤ Ji + Jp := Nat.le_add_right _ _
  have hpJ : Jp ≤ Ji + Jp := Nat.le_add_left _ _
  have hCip : Ci ≤ C := by dsimp [C]; linarith
  have hCpp (j : Label) : Cp j ≤ C := by
    have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (hCp k).le)
      (Finset.mem_univ j)
    dsimp [C]
    linarith
  have hpall : ∀ᶠ U : ℝ in atTop, ∀ j, _ := eventually_all.2 hp
  refine ⟨C, hC, ?_⟩
  filter_upwards [hpall, eventually_gt_atTop (1 : ℝ)] with U hpall hU
  refine ⟨hU, ?_⟩
  intro a ε tstar T allowance i ht ht' hε hε' B hd height hh j left right hne
  let F : UnmarkedFiber U a ε tstar T allowance i Label := B.fiber j left right hne
  change UnmarkedMoments F c κ (C * (1 + height)^(Ji + Jp)) height εm
  have geom := fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hU
    F.witness F.left F.right F.fixed_left F.fixed_right
  have hm : F.m ≤ 3/4 := by
    change tstar - F.r - ε ≤ F.m ∧ F.r ≤ tstar + ε ∧
      F.m ≤ 1/2 + 75*ε ∧ tstar - 1/2 - 76*ε ≤ F.r ∧ 0 ≤ F.m at geom
    linarith [geom.2.2.1]
  have hdata : F.rowData = momentData (D.base j) := by
    change B.data j = D.data j
    rw [hd]
  have hpow (k : ℕ) (hk : k ≤ Ji + Jp) : (1 + height)^k ≤ (1 + height)^(Ji + Jp) :=
    pow_le_pow_right₀ (by linarith) hk
  have hpi : Ci * (1 + height)^Ji ≤ C * (1 + height)^(Ji + Jp) :=
    mul_le_mul hCip (hpow Ji hiJ) (by positivity) hC.le
  have hpp : Cp j * (1 + height)^Jp ≤ C * (1 + height)^(Ji + Jp) :=
    mul_le_mul (hCpp j) (hpow _ hpJ) (by positivity) hC.le
  refine ⟨?_, ?_⟩
  · intro n hn s hs t ht
    have hdi : F.rowData = D.data j := by change B.data j = D.data j; rw [hd]
    rw [hdi]
    have hb := hi j F.reverse n hn U (zero_lt_one.trans hU) tstar F.r s hs height t hh ht
    constructor <;> intro X E hX hE hcap rows hrows
    · apply (hb.1 X E hX hE hcap rows hrows).trans
      gcongr
    · apply (hb.2 X E hX hE hcap rows hrows).trans
      gcongr
  · intro n k hnk s hs t ht
    have hb := (hpall j).2 F hm hdata height hh n k hnk s hs t ht
    exact hb.trans (mul_le_mul_of_nonneg_right hpp (Real.rpow_nonneg (zero_lt_one.trans hU).le _))

end SevenEighths.LocalMoment
end
end OAI

end Record1252270103Bootstrap.PR67
