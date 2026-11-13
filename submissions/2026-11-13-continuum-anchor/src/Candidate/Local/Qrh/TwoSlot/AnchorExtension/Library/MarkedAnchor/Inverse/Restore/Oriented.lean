/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Glue

/-!
# Inverse.Restore.Oriented — the restored child of one `imageAdm` datum, one orientation

**`oriented_bound`**: for the unpacked `imageAdm'` datum of the class
`canonicalSlotsRay W (33/50) rayM G hH` (pools `L i`, widths `ell i`, coefficients
`β i = rayCoeff … (Z^ell i) (v i)`, row height `|t| ≤ hv`), the positive physical child moment with
oriented coefficients `a' = a` (`neg = false`) or `a' = star a` (`neg = true`, twist `ψ'`) is
bounded by `Datum.child_sum_bound` at the child scale `Z' = Z^{Hc'}`: the child slots are the
canonical slots `canonicalSlotsRay (childBump W | childBumpN W) (33/50) (childRay …)
(childSlotTwist …)` with heights `∓v ∓ 2πt + 2πθ` (`|·| ≤ (1+2π) hv + 2π|θ|`), lists
`(lists i).map val` (`Glue.childLists_eq`), coefficients bounded by `1`
(`Glue.norm_child_coeff_le`), per-prime identity `slot_term_or` (`SlotTerm.slot_term_pos/neg`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)
open OAI.SevenEighths.HeckeInverseAmplification (RowData NonzeroElement)
open OAI.SevenEighths.HeckeDyadic (polynomial)
open OAI.ConcretePrimeRowBridge (primePool)
open OAI.CanonicalQuadraticSieve (poolPrimary)
open OAI.CanonicalCoefficientClass (FactorsModulo fixedBaseConductor)
open DetectorDictionaryInverseRawInitialGates (deletedBase)
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => ActualEisensteinCubic.O

/-- The oriented child bump. -/
def oBump (neg : Bool) (W : ℝ → ℂ) : ℝ → ℂ := if neg then childBumpN W else childBump W

/-- The oriented child slot height. -/
def oHeight (neg : Bool) (v t θ : ℝ) : ℝ :=
  if neg then v + 2 * Real.pi * t + 2 * Real.pi * θ else -v - 2 * Real.pi * t + 2 * Real.pi * θ

theorem abs_oHeight_le (neg : Bool) (v t θ hv : ℝ) (hvv : |v| ≤ hv) (ht : |t| ≤ hv) :
    |oHeight neg v t θ| ≤ (1 + 2 * Real.pi) * hv + 2 * Real.pi * ‖θ‖ := by
  have hpi := Real.pi_pos
  rw [Real.norm_eq_abs]
  have h1 : |2 * Real.pi * t| = 2 * Real.pi * |t| := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have h2 : |2 * Real.pi * θ| = 2 * Real.pi * |θ| := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  cases neg
  · simp only [oHeight, Bool.false_eq_true, ↓reduceIte]
    calc |-v - 2 * Real.pi * t + 2 * Real.pi * θ| ≤ |v| + |2 * Real.pi * t| + |2 * Real.pi * θ| := by
          have := abs_add_le (-v - 2 * Real.pi * t) (2 * Real.pi * θ)
          have := abs_sub (-v) (2 * Real.pi * t)
          rw [abs_neg] at this
          linarith
      _ ≤ _ := by rw [h1, h2]; nlinarith
  · simp only [oHeight, ↓reduceIte]
    calc |v + 2 * Real.pi * t + 2 * Real.pi * θ| ≤ |v| + |2 * Real.pi * t| + |2 * Real.pi * θ| := by
          have := abs_add_le (v + 2 * Real.pi * t) (2 * Real.pi * θ)
          have := abs_add_le v (2 * Real.pi * t)
          linarith
      _ ≤ _ := by rw [h1, h2]; nlinarith

theorem conjHom_factors {M : Ideal O} {ψ : O →* ℂ} (h : FactorsModulo M ψ) :
    FactorsModulo M (conjHom ψ) := by
  intro x y hxy
  simp only [conjHom_apply, h x y hxy]

section
variable (q D : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
  (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)
  (hg : ∀ i : primePool (childF q D), lambda ∉ Ideal.span {poolPrimary (childF q D) i})
  [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]
  (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
  (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (σ : ℝ)
  (data : RowData) (θ : RayQuotient.Characters rayM G.twist)

/-- The per-prime identity in both orientations. -/
theorem slot_term_or (neg : Bool) (y : O) (t τ X v : ℝ) (hX : 0 < X) (L' : Finset (Ideal O))
    (P : primePool (childF q D)) (hPL : P.val ∈ L')
    (hcop : IsCoprime P.val (childRay rayM (deletedBase data) (childCharacter q hq ψ hψ))) :
    CanonicalRowCompletion.idealRowHom y P.val *
      Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff L'
        (rayCoeff (childRay rayM (deletedBase data) (childCharacter q hq ψ hψ))
          (childSlotTwist rayM G hH (deletedBase data) (childCharacter q hq ψ hψ))
          (childSlotTwist_hH rayM G hH _ _) (oBump neg W) σ (childData q hq ψ hψ)
          (childTheta rayM neg G hH θ (deletedBase data) (childCharacter q hq ψ hψ)) X
          (oHeight neg v t τ)) X P.val =
    star (FourierBridge.logPhase τ (Real.log X)) *
      ((if neg then star (star (rayCoeff rayM G hH W σ data θ X v P.val /
          idealCoeff (deletedBase data) P.val) *
          FourierBridge.logPhase (-t) (Real.log ((P.val.absNorm : ℝ) / X)))
        else star (rayCoeff rayM G hH W σ data θ X v P.val /
          idealCoeff (deletedBase data) P.val) *
          FourierBridge.logPhase (-t) (Real.log ((P.val.absNorm : ℝ) / X))) *
        (childWeight (poolPrimary (childF q D)) hg ψ 1 y P *
          FourierBridge.logPhase τ (Real.log (primeN (poolPrimary (childF q D)) P)))) := by
  cases neg
  · simp only [oBump, oHeight, Bool.false_eq_true, ↓reduceIte]
    exact slot_term_pos q D hq ψ hψ hg rayM G hH W σ data θ y t τ X v hX L' P hPL hcop
  · simp only [oBump, oHeight, ↓reduceIte]
    exact slot_term_neg q D hq ψ hψ hg rayM G hH W σ data θ y t τ X v hX L' P hPL hcop

end

set_option maxHeartbeats 2000000 in
/-- **The restored child of one `imageAdm` datum, one orientation.** -/
theorem oriented_bound (neg : Bool) (q D : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
    (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ) (hψn : ∀ x, ‖ψ x‖ ≤ 1)
    (hg : ∀ i : primePool (childF q D), lambda ∉ Ideal.span {poolPrimary (childF q D) i})
    [∀ i : primePool (childF q D), (Ideal.span {poolPrimary (childF q D) i}).IsMaximal]
    (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ)
    {σ : Type} (I : Finset σ) (lists : σ → Finset (primePool (childF q D)))
    (a : σ → primePool (childF q D) → ℂ) (ha1 : ∀ i ∈ I, ∀ P ∈ lists i, ‖a i P‖ ≤ 1)
    (H : σ → ℝ) (Z : ℝ) (hZ : 1 ≤ Z) (data : RowData) (L : σ → Finset (Ideal O))
    (ell : σ → ℝ) (β : σ → Ideal O → ℂ) (tpar : ℝ) (θp : RayQuotient.Characters rayM G.twist)
    (v : σ → ℝ) (hv : ℝ) (hvb : ∀ i, |v i| ≤ hv) (ht : |tpar| ≤ hv)
    (hL : ∀ i, L i = canonicalPool rayM G.pool (Z^(ell i)))
    (hβ : ∀ i, β i = rayCoeff rayM G hH W (33/50) data θp (Z^(ell i)) (v i))
    (hell0 : ∀ i, 0 ≤ ell i) (hβ1 : ∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1)
    (hgateP : ∀ i, (((deletedBase data).modulus.absNorm : ℕ) : ℝ) < Z^(ell i))
    (hlists : ∀ i (P : primePool (childF q D)), P ∈ lists i ↔ P.val ∈ L i)
    (hHdef : ∀ i, H i = 2 * Z^(ell i))
    (ha : ∀ i (P : primePool (childF q D)), a i P =
      star (β i P.val / idealCoeff (deletedBase data) P.val) *
        FourierBridge.logPhase (-tpar)
          (Real.log (InverseInitialCommonProfile.slotRatio Z ell i P.val)))
    (hZD : ∀ i ∈ I, 2 * Z^(ell i) ≤ D)
    (Hc' : ℝ) (hHc' : 0 < Hc') (meshS : ℝ) (hmeshS : ∀ i ∈ I, ell i / Hc' ≤ meshS)
    (K : ℕ) (hIK : I.card ≤ K)
    (Φ Φsep : ℝ → ℂ) (bΦ : ℝ) (hbΦ : 0 ≤ bΦ) (hΦv : ∀ x, bΦ < x → Φ x = 0) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ r x hh : ℝ, 1 ≤ 2^(2*K+1) * r → r ≤ 1 → 0 < x →
      Φ (r * x) * FourierBridge.logPhase hh (Real.log (r * x)) =
        ∫ t : ℝ, FourierBridge.logPhase (t + hh) (Real.log r) * childLogTest Φsep (t + hh) x * b t)
    (bsup : ℝ) (hbsup : 0 < bsup) (hΦsep : ∀ x, bsup < x → Φsep x = 0)
    {ρ : AnchorRect} {Φ₀ : ℝ → ℂ} {ε' : ℝ} {d₂ d₀ : ℕ} {C₂ C₀ : ℝ}
    (hs₂ : InverseRectAt (canonicalSlotsRay (oBump neg W) (33/50)
        (childRay rayM (deletedBase data) (childCharacter q hq ψ hψ))
        (childSlotTwist rayM G hH (deletedBase data) (childCharacter q hq ψ hψ))
        (childSlotTwist_hH rayM G hH _ _)) ρ (fun x => Φsep x * ((x : ℂ) ^ (-(1/2 : ℂ)))) K
      meshS 1 1 ε' (Z^Hc') (childData q hq ψ hψ) d₂ C₂)
    (hs₀ : InverseRectAt (canonicalSlotsRay (oBump neg W) (33/50)
        (childRay rayM (deletedBase data) (childCharacter q hq ψ hψ))
        (childSlotTwist rayM G hH (deletedBase data) (childCharacter q hq ψ hψ))
        (childSlotTwist_hH rayM G hH _ _)) ρ Φ₀ K meshS 1 1 ε' (Z^Hc')
      (childData q hq ψ hψ) d₀ C₀)
    (hZ' : 1 < Z^Hc') (hC₂ : 0 ≤ C₂) (hC₀ : 0 ≤ C₀)
    (hΦ₀1 : Φ₀ 1 = 1) (hΦ₀2 : ∀ x, 2 ≤ x → Φ₀ x = 0)
    (Cb : ℝ) (hCb0 : 0 ≤ Cb)
    (hCb : ∀ (θ : ℝ) (χ : Character) (Y : ℝ), 0 < Y → Y ≤ 1 →
      ‖polynomial χ true (childLogTest (fun x => Φsep x * ((x : ℂ) ^ (-(1/2 : ℂ)))) θ) Y 0 0‖
        ≤ Cb)
    (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hgate : (((deletedBase (childData q hq ψ hψ)).modulus.absNorm : ℕ) : ℝ) < c₀)
    (hS : ∑ i ∈ I, ell i / Hc' ≤ ρ.Smax)
    (hPmax : 0 ≤ ρ.Pmax ∨ bsup * (Z^Hc')^ρ.Pmax < 1)
    (s Xc : ℝ) (hXc : 0 < Xc)
    (hXcmax : Xc * 2^I.card ≤ 2^(K+1) * (∏ i ∈ I, H i) * (Z^Hc')^ρ.Pmax)
    (hD : bsup * Xc ≤ D) (t : Finset (primePool (childF q D))) (m : O) :
    mobiusChildSumInj (poolPrimary (childF q D)) hg (Finset.univ \ t) ψ m I lists
        (fun i P => if neg then star (a i P) else a i P) (childLogTest Φ s) Xc false Z Hc' ≤
      lamA 256 I.card * (12^((t ∪ Finset.univ.filter
          (fun i => m ∈ Ideal.span {poolPrimary (childF q D) i})).card + I.card) *
        (lamA ((t ∪ Finset.univ.filter
          (fun i => m ∈ Ideal.span {poolPrimary (childF q D) i})).card + I.card : ℕ) I.card *
          mainConst b (d₂+d₀) K c₀ Cb (C₂ + C₀) (Z^Hc') ε' ((1 + 2 * Real.pi) * hv) s)) := by
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hv0 : 0 ≤ hv := (abs_nonneg _).trans ht
  have hpi := Real.pi_pos
  set δ := deletedBase data with hδdef
  set η' := childCharacter q hq ψ hψ with hη'def
  have hZell : ∀ i, (Z^Hc')^(ell i / Hc') = Z^(ell i) := by
    intro i
    rw [← Real.rpow_mul hZ0.le, mul_div_cancel₀ _ hHc'.ne']
  have hXpos : ∀ i, 0 < Z^(ell i) := fun i => Real.rpow_pos_of_pos hZ0 _
  have hfacts : ∀ i ∈ I, ∀ P ∈ lists i, P.val ∈ canonicalPool rayM G.pool (Z^(ell i)) ∧
      Z^(ell i) ≤ (P.val.absNorm : ℝ) ∧ (P.val.absNorm : ℝ) ≤ 2 * Z^(ell i) ∧ Prime P.val ∧
      IsCoprime P.val (childRay rayM δ η') := by
    intro i hi P hP
    have hPL : P.val ∈ canonicalPool rayM G.pool (Z^(ell i)) := hL i ▸ (hlists i P).mp hP
    obtain ⟨hN1, hN2, hpr⟩ := canonicalPool_norm rayM G.pool _ (hXpos i) P.val hPL
    refine ⟨hPL, hN1, hN2, hpr, ?_⟩
    exact (coprime_childRay_iff q D rayM G hq δ η' rfl δ.modulus_ne_bot (Z^(ell i)) P.val hPL
      (lt_of_lt_of_le (hgateP i) hN1) (hN2.trans (hZD i hi))).mp P.property
  refine child_sum_bound q D hq ψ hψ hψn hg I lists
    (fun i P => if neg then star (a i P) else a i P)
    (fun i hi P hP => by
      cases neg
      · simpa using ha1 i hi P hP
      · simpa using ha1 i hi P hP)
    H (fun i hi => by
      rw [hHdef i]; have := Real.one_le_rpow hZ (hell0 i); linarith)
    (fun i hi P hP => by
      obtain ⟨_, hN1, hN2, _, _⟩ := hfacts i hi P hP
      rw [hHdef i]; constructor <;> linarith)
    K hIK Φ Φsep bΦ hbΦ hΦv b hsep bsup hbsup hΦsep hs₂ hs₀ hZ' hC₂ hC₀ hΦ₀1 hΦ₀2 Cb hCb0 hCb
    c₀ hc₀ hgate (fun i => ell i / Hc')
    (fun θ i => rayCoeff (childRay rayM δ η') (childSlotTwist rayM G hH δ η')
      (childSlotTwist_hH rayM G hH _ _) (oBump neg W) (33/50) (childData q hq ψ hψ)
      (childTheta rayM neg G hH θp δ η') ((Z^Hc')^(ell i / Hc')) (oHeight neg (v i) tpar θ))
    (fun θ i => star (FourierBridge.logPhase θ (Real.log ((Z^Hc')^(ell i / Hc')))))
    (fun θ i => by rw [norm_star, FourierBridge.logPhase_norm])
    ?_ (fun θ => (1 + 2 * Real.pi) * hv + 2 * Real.pi * ‖θ‖)
    (fun θ => by positivity) ((1 + 2 * Real.pi) * hv) (by positivity) (fun θ => le_rfl)
    ?_ (fun i _ => div_nonneg (hell0 i) hHc'.le) hmeshS
    (fun i hi P hP => (hfacts i hi P hP).2.2.2.1)
    (fun i hi P hP => by
      obtain ⟨_, hN1, hN2, _, _⟩ := hfacts i hi P hP
      rw [hZell i, Set.mem_Icc, le_div_iff₀ (hXpos i), div_le_iff₀ (hXpos i), one_mul]
      exact ⟨hN1, by linarith⟩)
    ?_ hS hPmax Z Hc' (by rw [Real.rpow_one]) s Xc hXc hXcmax hD t m
  · intro θ y i hi P hP
    obtain ⟨_, _, _, _, hcop⟩ := hfacts i hi P hP
    simp only [hZell i]
    have h := slot_term_or q D hq ψ hψ hg rayM G hH W (33/50) data θp neg y tpar θ (Z^(ell i))
      (v i) (hXpos i) ((lists i).map (Function.Embedding.subtype _)) P
      (Finset.mem_map_of_mem _ hP) hcop
    rw [ha i P, hβ i]
    unfold InverseInitialCommonProfile.slotRatio
    exact h
  · intro θ J _ f hf
    refine ⟨childTheta rayM neg G hH θp δ η', fun j => oHeight neg (v (f j)) tpar θ,
      fun j => abs_oHeight_le neg (v (f j)) tpar θ hv (hvb _) ht, fun j => ⟨?_, rfl⟩⟩
    show (lists (f j)).map (Function.Embedding.subtype _) =
      canonicalPool (childRay rayM δ η') (childSlotTwist rayM G hH δ η').pool
        ((Z^Hc')^(ell (f j) / Hc'))
    rw [hZell]
    exact childLists_eq q D rayM G hH hq δ η' rfl δ.modulus_ne_bot (Z^(ell (f j))) (lists (f j))
      (L (f j)) (hL _) (hlists _) (hgateP _) (hZD _ (hf j))
  · intro θ i hi P hP
    obtain ⟨hPL, hN1, _, hpr, hcop⟩ := hfacts i hi P hP
    haveI : P.val.IsMaximal := (Ideal.isPrime_of_prime hpr).isMaximal hpr.ne_zero
    have hP0 : P.val ≠ ⊥ := fun h0 => hpr.ne_zero (h0.trans Ideal.zero_eq_bot.symm)
    simp only [hZell i]
    have hb := hβ1 i P.val (hL i ▸ hPL)
    rw [hβ i] at hb
    exact norm_child_coeff_le rayM G hH W (33/50) data θp q hq ψ hψ neg (v i) tpar θ (Z^(ell i))
      (hXpos i) P.val hP0 hN1 hcop hb hψn

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.slot_term_or
#print axioms Qrh.MarkedAnchor.Inverse.Restore.oriented_bound
