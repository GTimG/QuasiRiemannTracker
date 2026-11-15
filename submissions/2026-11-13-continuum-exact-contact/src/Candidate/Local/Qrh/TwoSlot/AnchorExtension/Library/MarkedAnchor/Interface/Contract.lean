/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PrimeSlot
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters

/-!
# Interface.Contract

Anchor contracts: at an anchor `(R, z_R)` BOTH the actual inverse `M_v`
with prime slots and the product of two actual ordinary polynomials satisfy row-sized moments on
the rectangle `P ≤ R*H`, `S ≤ ((1-R)/2 + z_R)*H` (widths relative to the row radius `H`), with
arbitrarily small endpoint decrements and arbitrary downward shortening.

* `AnchorRect` — the rectangle `(Pmax, Smax)`; `Admissible r S M` is `0 ≤ r ≤ Pmax*M`,
  `0 ≤ S ≤ Smax*M` (downward closed).
* `InverseRectAt` / `InverseRectSource` / `UniformInverseRectSource` — the inverse contract.
  The moment is literally the one of HC
  `direct_reference_energy` / `actual_inverse_marked_energy` (Record12518109Gain/Upstream/
  DeletionInverse.lean): actual inverse `polynomial (data.character u) true (childLogTest Φ θ)
  (Z^r) 0 0` times `∏ directSlot u (L i) (β i) (Z^(ell i))`, summed over ALL nonzero rows of the
  ball `‖u‖^2 ≤ Z^M` (no keep predicate: fixed-inducing inverse rows are inside), uniform over
  compactly supported smooth `Φ` (fixed before the degree), polynomial in the height `θ`.
  The native gates `r+2S<1, 2r+8S<3` are replaced by the rectangle; a slot-class filter `cls`
  (from a family `fam`) restricts the admitted slot vectors (`anySlots`: the native class with
  arbitrary bounded coefficients; `canonicalSlots`: whole canonical slots).
  Quantifier order: `∀ε>0 ∃mesh>0, ∀K (slot-type bound) ∀cls∈fam ∀Φ, ∀data, ∃degree C Z₀,
  ∀Z≥Z₀` (the height degree may depend on the row data; the native
  order `∃degree ∀data ∃C U₀ ∀U` implies it; the mesh is in front as in `UniformUnitFaceSource`).
  Slot classes take a height bound `hv` (`SlotClass … Z hv`); the canonical classes
  require `|v i| ≤ hv` for the slot heights, and `InverseRectAt` quantifies `∀ hv ≥ 0` with the
  slot vector and pays `((1+‖θ‖+hv)^degree)^2` (polynomial in all permitted heights).
* `OrdinaryRectSource ρ` — `UniformUnitFaceSource` of the face `globalFace Pmax 0 Smax`
  (so `P1+P2 ≤ Pmax`, `S ≤ Smax`); a restriction of `GlobalSource B L c` on its native part.
* `AnchorAt R z`, `ImprovedMoments lo hi g0 g1` and the structural lemmas.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Interface.Contract
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
local notation "O" => HeckeFamily.O
local instance (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-! ## The rectangle -/

/-- Anchor rectangle: free width `≤ Pmax`, total slot width `≤ Smax`, both relative to the
row radius. -/
structure AnchorRect where
  Pmax : ℝ
  Smax : ℝ

/-- Admission of free width `r` and total slot width `S` on a row ball of radius exponent `M`. -/
def AnchorRect.Admissible (ρ : AnchorRect) (r S M : ℝ) : Prop :=
  0 ≤ r ∧ r ≤ ρ.Pmax*M ∧ 0 ≤ S ∧ S ≤ ρ.Smax*M

/-- `strong` covers `weak`. -/
def AnchorRect.Restricts (strong weak : AnchorRect) : Prop :=
  weak.Pmax ≤ strong.Pmax ∧ weak.Smax ≤ strong.Smax

/-- The native inverse region `Pmax + 2 Smax < 1`, `2 Pmax + 8 Smax < 3`. -/
def AnchorRect.NativeInverse (ρ : AnchorRect) : Prop :=
  ρ.Pmax+2*ρ.Smax < 1 ∧ 2*ρ.Pmax+8*ρ.Smax < 3

theorem AnchorRect.admissible_of_restricts {strong weak : AnchorRect}
    (h : strong.Restricts weak) {r S M : ℝ} (hM : 0 ≤ M)
    (ha : weak.Admissible r S M) : strong.Admissible r S M := by
  obtain ⟨hr0,hr,hS0,hS⟩ := ha
  exact ⟨hr0,hr.trans (mul_le_mul_of_nonneg_right h.1 hM),hS0,
    hS.trans (mul_le_mul_of_nonneg_right h.2 hM)⟩

theorem AnchorRect.restricts_refl (ρ : AnchorRect) : ρ.Restricts ρ := ⟨le_rfl,le_rfl⟩

theorem AnchorRect.Restricts.trans {a b c : AnchorRect} (hab : a.Restricts b)
    (hbc : b.Restricts c) : a.Restricts c := ⟨hbc.1.trans hab.1,hbc.2.trans hab.2⟩

/-- Arbitrary downward shortening. -/
theorem AnchorRect.admissible_downward {ρ : AnchorRect} {r S r' S' M : ℝ}
    (ha : ρ.Admissible r S M) (hr0 : 0 ≤ r') (hr : r' ≤ r) (hS0 : 0 ≤ S') (hS : S' ≤ S) :
    ρ.Admissible r' S' M :=
  ⟨hr0,hr.trans ha.2.1,hS0,hS.trans ha.2.2.2⟩

/-- Inside the native region every admitted pair (unit ball) satisfies the strict native gates
of `Moments.inverse_marked` / `actual_inverse_marked_energy`. -/
theorem AnchorRect.native_gates {ρ : AnchorRect} (hρ : ρ.NativeInverse) {r S : ℝ}
    (ha : ρ.Admissible r S 1) : r+2*S < 1 ∧ 2*r+8*S < 3 := by
  obtain ⟨_,hr,_,hS⟩ := ha
  rw [mul_one] at hr hS
  obtain ⟨h1,h2⟩ := hρ
  constructor <;> linarith

/-! ## Slots -/

/-- The normalized whole-slot mark; literally HC `directPrimeSlot`. -/
def directSlot (u : O) (L : Finset (Ideal O)) (β : Ideal O → ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P : ℂ)⁻¹ * ∑ I ∈ L, β I * CanonicalRowCompletion.idealRowHom u I

/-- A filter on admitted slot vectors `(L, ell, β)` at scale `Z` for row data `data`, with slot
height bound `hv` (the last argument bounds the imaginary heights of the slot coefficients;
classes that do not see heights ignore it). -/
abbrev SlotClass : Type 1 :=
  (ι : Type) → RowData → (ι → Finset (Ideal O)) → (ι → ℝ) → (ι → Ideal O → ℂ) → ℝ → ℝ → Prop

/-- The native class: every bounded coefficient vector on disjoint prime annuli. -/
def anySlots : SlotClass := fun _ _ _ _ _ _ _ => True

/-- The canonical slot list at scale `D`: identity-ray primes with `Np/D ∈ [1,2]`
(a whole slot, never a subset of its primes). -/
def canonicalPool (rayM : Ideal O) (H : Subgroup (O ⧸ rayM)ˣ) (D : ℝ) : Finset (Ideal O) :=
  (CenteredMomentPrimeSlot.primePool rayM H 2 D).filter
    (fun P => ((P.absNorm : ℝ)/D) ∈ Icc (1 : ℝ) 2)

/-- Ray data of a slot class: the subgroup `pool` defines the slot pool
(`identityClass rayM pool`), the smaller subgroup `twist` defines the relative ray characters
`θ ∈ Characters twist`, so the common relative finite character can be nontrivial on the pool. -/
structure SlotTwist (rayM : Ideal O) where
  pool : Subgroup (O ⧸ rayM)ˣ
  twist : Subgroup (O ⧸ rayM)ˣ
  twist_le : twist ≤ pool

/-- The diagonal case `pool = twist = H`. -/
def SlotTwist.diag {rayM : Ideal O} (H : Subgroup (O ⧸ rayM)ˣ) : SlotTwist rayM :=
  ⟨H, H, le_rfl⟩

/-- Canonical slots with common bump `W`, real part `σ`, independent imaginary
heights `v i`, pool `identityClass rayM G.pool`, coefficient = (relative ray character of
`θ i ∈ Characters G.twist` w.r.t. the row base `data.η`) times the row base character; the row
symbol enters through `idealRowHom` in `directSlot`. `globalUnits ≤ G.twist ≤ G.pool`.
The slot heights are bounded by the class height, `|v i| ≤ hv`. -/
def canonicalSlots (W : ℝ → ℂ) (σ : ℝ) : SlotClass := fun ι data L ell β Z hv =>
  ∃ (rayM : Ideal O) (_ : NeZero rayM) (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)
    (θ : ι → RayQuotient.Characters rayM G.twist) (v : ι → ℝ),
    (∀ i, |v i| ≤ hv) ∧ ∀ i, L i = canonicalPool rayM G.pool (Z^(ell i)) ∧
      β i = fun I => idealCoeff
          (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM G.twist hH data.η (θ i)) I *
        idealCoeff data.η I * HeckePrimeAnnular.annularWeight W (Z^(ell i)) σ (v i) I

/-- The diagonal class (one subgroup for pool and twists; the twist is then trivial on the
pool): the special case `G = SlotTwist.diag H` of `canonicalSlots`. -/
def canonicalSlotsOld (W : ℝ → ℂ) (σ : ℝ) : SlotClass := fun ι data L ell β Z hv =>
  ∃ (rayM : Ideal O) (_ : NeZero rayM) (H : Subgroup (O ⧸ rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (θ : ι → RayQuotient.Characters rayM H) (v : ι → ℝ),
    (∀ i, |v i| ≤ hv) ∧ ∀ i, L i = canonicalPool rayM H (Z^(ell i)) ∧
      β i = fun I => idealCoeff
          (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM H hH data.η (θ i)) I *
        idealCoeff data.η I * HeckePrimeAnnular.annularWeight W (Z^(ell i)) σ (v i) I

theorem canonicalSlots_old_le_new (W : ℝ → ℂ) (σ : ℝ) (ι : Type) (data : RowData)
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (Z hv : ℝ)
    (h : canonicalSlotsOld W σ ι data L ell β Z hv) : canonicalSlots W σ ι data L ell β Z hv := by
  obtain ⟨rayM, hne, H, hH, θ, v, hL⟩ := h
  exact ⟨rayM, hne, SlotTwist.diag H, hH, θ, v, hL⟩

/-! ### Ray data fixed in the class (before the scale)

`canonicalSlots` keeps `rayM, G, hH` existential per slot vector, i.e. chosen after the scale
`Z`; with `rayM = ∏_{P∈S} P` it contains arbitrary prime-subset slots. The canonical FAMILY
therefore fixes `(rayM, G, hH)` in the class; only `θ` and `v` stay free. -/

/-- The coefficient of a canonical slot, verbatim from `canonicalSlots`. -/
def rayCoeff (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (σ : ℝ) (data : RowData)
    (θ : RayQuotient.Characters rayM G.twist) (D v : ℝ) : Ideal O → ℂ := fun I =>
  idealCoeff (CenteredMomentNaturalFixedRaySource.relativeCharacter rayM G.twist hH data.η θ) I *
    idealCoeff data.η I * HeckePrimeAnnular.annularWeight W D σ v I

/-- Canonical slots with the ray data `(rayM, G, hH)` fixed in the class and ONE common relative
twist `θ` for all slots (a common relative character). The slot heights are bounded by the
height argument, `|v i| ≤ hv` (paid in `InverseRectAt` like the row height: polynomial
dependence on all permitted heights). -/
def canonicalSlotsRay (W : ℝ → ℂ) (σ : ℝ) (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) : SlotClass := fun ι data L ell β Z hv =>
  ∃ (θ : RayQuotient.Characters rayM G.twist) (v : ι → ℝ),
    (∀ i, |v i| ≤ hv) ∧ ∀ i, L i = canonicalPool rayM G.pool (Z^(ell i)) ∧
      β i = rayCoeff rayM G hH W σ data θ (Z^(ell i)) (v i)

/-- A fixed-ray canonical slot vector is canonical (unrestricted predicate). -/
theorem canonicalSlotsRay_le (W : ℝ → ℂ) (σ : ℝ) (rayM : Ideal O) [hne : NeZero rayM]
    (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (ι : Type)
    (data : RowData) (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (Z hv : ℝ)
    (h : canonicalSlotsRay W σ rayM G hH ι data L ell β Z hv) :
    canonicalSlots W σ ι data L ell β Z hv := by
  obtain ⟨θ, v, hvb, h⟩ := h
  exact ⟨rayM, hne, G, hH, fun _ => θ, v, hvb, h⟩

/-- Whole-slot sub-collections stay in a fixed-ray class (`SubClosed`, unfolded). -/
theorem canonicalSlotsRay_restrict (W : ℝ → ℂ) (σ : ℝ) (rayM : Ideal O) [NeZero rayM]
    (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (ι : Type)
    (data : RowData) (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (Z hv : ℝ)
    (F : Finset ι) (hc : canonicalSlotsRay W σ rayM G hH ι data L ell β Z hv) :
    canonicalSlotsRay W σ rayM G hH F data (fun i => L i.val) (fun i => ell i.val)
      (fun i => β i.val) Z hv := by
  obtain ⟨θ, v, hvb, h⟩ := hc
  exact ⟨θ, fun i => v i.val, fun i => hvb i.val, fun i => h i.val⟩

/-- A fixed-ray class depends on widths and scale only through `Z^(ell i)`
(`ScaleInvariant`, unfolded). -/
theorem canonicalSlotsRay_rescale (W : ℝ → ℂ) (σ : ℝ) (rayM : Ideal O) [NeZero rayM]
    (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (ι : Type)
    (data : RowData) (L : ι → Finset (Ideal O)) (ell ell' : ι → ℝ) (β : ι → Ideal O → ℂ)
    (Z Z' hv : ℝ) (hs : ∀ i, Z^(ell i) = Z'^(ell' i))
    (hc : canonicalSlotsRay W σ rayM G hH ι data L ell β Z hv) :
    canonicalSlotsRay W σ rayM G hH ι data L ell' β Z' hv := by
  obtain ⟨θ, v, hvb, h⟩ := hc
  refine ⟨θ, v, hvb, fun i => ?_⟩
  rw [← hs i]
  exact h i

/-- A larger height bound admits more slot vectors. -/
theorem canonicalSlotsRay_mono_height (W : ℝ → ℂ) (σ : ℝ) (rayM : Ideal O) [NeZero rayM]
    (G : SlotTwist rayM) (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (ι : Type)
    (data : RowData) (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ)
    (Z hv hv' : ℝ) (hle : hv ≤ hv')
    (hc : canonicalSlotsRay W σ rayM G hH ι data L ell β Z hv) :
    canonicalSlotsRay W σ rayM G hH ι data L ell β Z hv' := by
  obtain ⟨θ, v, hvb, h⟩ := hc
  exact ⟨θ, v, fun i => (hvb i).trans hle, h⟩

/-- The canonical family: fixed-ray canonical slots for a smooth bump
supported in `[1,2]`, real part `33/50` (the convention of `UnitFaceSource`); the ray modulus,
pool and twist subgroups are part of the class, hence chosen before the scale. -/
def canonicalFamily : SlotClass → Prop := fun cls =>
  ∃ W : ℝ → ℂ, ContDiff ℝ ∞ W ∧ Function.support W ⊆ Icc (1 : ℝ) 2 ∧
    ∃ (rayM : Ideal O) (_ : NeZero rayM) (G : SlotTwist rayM)
      (hH : RayOrthogonality.globalUnits rayM ≤ G.twist),
      cls = canonicalSlotsRay W (33/50) rayM G hH

/-- The unrestricted canonical family (ray data after the scale). Strictly stronger as a source
hypothesis; sources for it transfer to `canonicalFamily` by `of_free`. -/
def canonicalFamilyFree : SlotClass → Prop := fun cls =>
  ∃ W : ℝ → ℂ, ContDiff ℝ ∞ W ∧ Function.support W ⊆ Icc (1 : ℝ) 2 ∧
    cls = canonicalSlots W (33/50)

/-- The unrestricted canonical family with diagonal `SlotTwist`. -/
def canonicalFamilyOld : SlotClass → Prop := fun cls =>
  ∃ W : ℝ → ℂ, ContDiff ℝ ∞ W ∧ Function.support W ⊆ Icc (1 : ℝ) 2 ∧
    cls = canonicalSlotsOld W (33/50)

/-- Every slot class (strongest family; the native theorem supplies it). -/
def allFamily : SlotClass → Prop := fun _ => True

/-! ## The inverse contract -/

/-- The literal actual inverse marked row sum. -/
def inverseMarkedSum (data : RowData) (Φ : ℝ → ℂ) {ι : Type} [Fintype ι]
    (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ)
    (rows : Finset HeckeInverseAmplification.NonzeroElement) (Z r θ : ℝ) : ℝ :=
  ∑ u ∈ rows, ‖polynomial (data.character u) true (InverseMoment.childLogTest Φ θ) (Z^r) 0 0 *
    (∏ i, directSlot u.val (L i) (β i) (Z^(ell i)))‖^2

/-- The inverse contract at one scale `Z`: every slot vector of the class with at most `K`
slots, widths `≤ mesh` (chosen after `Z`), pools possibly overlapping (no
`PairwiseDisjoint L`; the full product `∏ directSlot` is bounded), radius `M ∈ [Mmin,Mmax]`,
rectangle admission, all nonzero rows of the ball `‖u‖^2 ≤ Z^M`, every height `θ`.
Every slot height bound `hv ≥ 0` (chosen after `Z`, with the slot vector) is paid like
the row height, by the factor `((1+‖θ‖+hv)^degree)^2`. -/
def InverseRectAt (cls : SlotClass) (ρ : AnchorRect) (Φ : ℝ → ℂ) (K : ℕ)
    (mesh Mmin Mmax ε Z : ℝ) (data : RowData) (degree : ℕ) (C : ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
  ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (hv : ℝ), 0 ≤ hv →
    cls ι data L ell β Z hv →
    (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) → (∀ i, ∀ P ∈ L i, Prime P) →
    (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
    (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
    (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ r : ℝ, ρ.Admissible r (∑ i, ell i) M →
  ∀ rows : Finset HeckeInverseAmplification.NonzeroElement,
    (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z^M) → ∀ θ : ℝ,
    inverseMarkedSum data Φ L ell β rows Z r θ ≤ C*Z^(M+ε)*((1+‖θ‖+hv)^degree)^2

/-- The height factor is monotone in the slot height. -/
theorem heightFactor_mono (θ : ℝ) {hv hv' : ℝ} (h0 : 0 ≤ hv) (hle : hv ≤ hv') (d : ℕ) :
    ((1+‖θ‖+hv)^d)^2 ≤ ((1+‖θ‖+hv')^d)^2 := by
  have h1 : 0 ≤ 1+‖θ‖+hv := by positivity
  gcongr

/-- The row-height factor is dominated by the full height factor. -/
theorem heightFactor_row_le (θ : ℝ) {hv : ℝ} (h0 : 0 ≤ hv) (d : ℕ) :
    ((1+‖θ‖)^d)^2 ≤ ((1+‖θ‖+hv)^d)^2 := by
  simpa using heightFactor_mono θ le_rfl h0 d

/-- The full height factor splits into a slot-height factor and a row-height factor
(`1+a+b ≤ (1+a)(1+b)` for `a, b ≥ 0`). -/
theorem heightFactor_split (θ : ℝ) {hv : ℝ} (h0 : 0 ≤ hv) (d : ℕ) :
    ((1+‖θ‖+hv)^d)^2 ≤ (1+hv)^(2*d)*(1+‖θ‖)^(2*d) := by
  have hn := norm_nonneg θ
  have h1 : 1+‖θ‖+hv ≤ (1+hv)*(1+‖θ‖) := by nlinarith
  have h2 : 0 ≤ 1+‖θ‖+hv := by positivity
  calc ((1+‖θ‖+hv)^d)^2 ≤ (((1+hv)*(1+‖θ‖))^d)^2 := by gcongr
    _ = (1+hv)^(2*d)*(1+‖θ‖)^(2*d) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm d 2]

theorem inverseRectAt_restrict {cls : SlotClass} {strong weak : AnchorRect}
    (h : strong.Restricts weak) (Φ : ℝ → ℂ) (K : ℕ) (mesh Mmin Mmax ε Z : ℝ)
    (data : RowData) (degree : ℕ) (C : ℝ) (hMmin : 0 ≤ Mmin)
    (hs : InverseRectAt cls strong Φ K mesh Mmin Mmax ε Z data degree C) :
    InverseRectAt cls weak Φ K mesh Mmin Mmax ε Z data degree C := by
  intro ι _ _ hK L ell β hv hv0 hc h1 h2 h3 h5 h6 h7 M hMlo hMhi r hadm
  exact hs hK L ell β hv hv0 hc h1 h2 h3 h5 h6 h7 M hMlo hMhi r
    (AnchorRect.admissible_of_restricts h (hMmin.trans hMlo) hadm)

theorem inverseRectAt_mono_mesh {cls : SlotClass} {ρ : AnchorRect} (Φ : ℝ → ℂ) (K : ℕ)
    (mesh mesh' Mmin Mmax ε Z : ℝ) (data : RowData) (degree : ℕ) (C : ℝ)
    (hle : mesh' ≤ mesh)
    (hs : InverseRectAt cls ρ Φ K mesh Mmin Mmax ε Z data degree C) :
    InverseRectAt cls ρ Φ K mesh' Mmin Mmax ε Z data degree C := by
  intro ι _ _ hK L ell β hv hv0 hc h1 h2
  exact hs hK L ell β hv hv0 hc h1 (fun i => (h2 i).trans hle)

/-- A contract for a larger slot class implies the one for a smaller class. -/
theorem inverseRectAt_mono_class {cls cls' : SlotClass}
    (hk : ∀ (ι : Type) (data : RowData) (L : ι → Finset (Ideal O)) (ell : ι → ℝ)
      (β : ι → Ideal O → ℂ) (Z hv : ℝ), cls' ι data L ell β Z hv → cls ι data L ell β Z hv)
    {ρ : AnchorRect} (Φ : ℝ → ℂ) (K : ℕ) (mesh Mmin Mmax ε Z : ℝ)
    (data : RowData) (degree : ℕ) (C : ℝ)
    (hs : InverseRectAt cls ρ Φ K mesh Mmin Mmax ε Z data degree C) :
    InverseRectAt cls' ρ Φ K mesh Mmin Mmax ε Z data degree C := by
  intro ι _ _ hK L ell β hv hv0 hc
  exact hs hK L ell β hv hv0 (hk ι data L ell β Z hv hc)

/-- A contract for `canonicalSlots` gives the one for the diagonal class `canonicalSlotsOld`. -/
theorem inverseRectAt_old_of_new (W : ℝ → ℂ) (σ : ℝ) {ρ : AnchorRect} (Φ : ℝ → ℂ) (K : ℕ)
    (mesh Mmin Mmax ε Z : ℝ) (data : RowData) (degree : ℕ) (C : ℝ)
    (hs : InverseRectAt (canonicalSlots W σ) ρ Φ K mesh Mmin Mmax ε Z data degree C) :
    InverseRectAt (canonicalSlotsOld W σ) ρ Φ K mesh Mmin Mmax ε Z data degree C :=
  inverseRectAt_mono_class (canonicalSlots_old_le_new W σ) Φ K mesh Mmin Mmax ε Z data degree C hs

/-- One mesh precedes the slot-type bound `K`, the slot class, the profile and all row data;
the height degree and the constants depend on the row data;
constants precede the scale threshold. Radius pinned to
`M = 1` (rescaled), as in `UnitFaceSource`. -/
def InverseRectSource (fam : SlotClass → Prop) (ρ : AnchorRect) (mesh ε : ℝ) : Prop :=
  ∀ K : ℕ, ∀ cls : SlotClass, fam cls →
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support Φ ⊆ Icc ao bo →
    ContDiff ℝ ∞ Φ →
  ∀ data : RowData, ∃ (degree : ℕ) (C Z₀ : ℝ), 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → InverseRectAt cls ρ Φ K mesh 1 1 ε Z data degree C

/-- `∀ ε>0 ∃ mesh>0`, exactly as `UniformUnitFaceSource`. -/
def UniformInverseRectSource (fam : SlotClass → Prop) (ρ : AnchorRect) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧ InverseRectSource fam ρ mesh ε

theorem InverseRectSource.restrict {fam : SlotClass → Prop} {strong weak : AnchorRect}
    {mesh ε : ℝ} (h : strong.Restricts weak) (hs : InverseRectSource fam strong mesh ε) :
    InverseRectSource fam weak mesh ε := by
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree,C,Z₀,hC,hZ₀,hb⟩ := hs K cls hcls Φ ao bo hao hab hΦs hΦ data
  exact ⟨degree,C,Z₀,hC,hZ₀,
    fun Z hZ => inverseRectAt_restrict h Φ K mesh 1 1 ε Z data degree C
      zero_le_one (hb Z hZ)⟩

theorem InverseRectSource.mono_mesh {fam : SlotClass → Prop} {ρ : AnchorRect}
    {mesh mesh' ε : ℝ} (hle : mesh' ≤ mesh) (hs : InverseRectSource fam ρ mesh ε) :
    InverseRectSource fam ρ mesh' ε := by
  intro K cls hcls Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree,C,Z₀,hC,hZ₀,hb⟩ := hs K cls hcls Φ ao bo hao hab hΦs hΦ data
  exact ⟨degree,C,Z₀,hC,hZ₀,
    fun Z hZ => inverseRectAt_mono_mesh Φ K mesh mesh' 1 1 ε Z data degree C
      hle (hb Z hZ)⟩

theorem InverseRectSource.mono_family {fam fam' : SlotClass → Prop}
    (hf : ∀ cls, fam' cls → fam cls) {ρ : AnchorRect} {mesh ε : ℝ}
    (hs : InverseRectSource fam ρ mesh ε) : InverseRectSource fam' ρ mesh ε :=
  fun K cls hcls => hs K cls (hf cls hcls)

theorem UniformInverseRectSource.restrict {fam : SlotClass → Prop} {strong weak : AnchorRect}
    (h : strong.Restricts weak) (hs : UniformInverseRectSource fam strong) :
    UniformInverseRectSource fam weak := by
  intro ε hε
  obtain ⟨mesh,hmesh,hsrc⟩ := hs ε hε
  exact ⟨mesh,hmesh,hsrc.restrict h⟩

theorem UniformInverseRectSource.mono_family {fam fam' : SlotClass → Prop}
    (hf : ∀ cls, fam' cls → fam cls) {ρ : AnchorRect}
    (hs : UniformInverseRectSource fam ρ) : UniformInverseRectSource fam' ρ := by
  intro ε hε
  obtain ⟨mesh,hmesh,hsrc⟩ := hs ε hε
  exact ⟨mesh,hmesh,hsrc.mono_family hf⟩

/-- The unrestricted canonical source implies the diagonal one. -/
theorem UniformInverseRectSource.old_of_new {ρ : AnchorRect}
    (hs : UniformInverseRectSource canonicalFamilyFree ρ) :
    UniformInverseRectSource canonicalFamilyOld ρ := by
  intro ε hε
  obtain ⟨mesh,hmesh,hsrc⟩ := hs ε hε
  refine ⟨mesh,hmesh,?_⟩
  rintro K cls ⟨W,hW,hWs,rfl⟩ Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree,C,Z₀,hC,hZ₀,hb⟩ :=
    hsrc K (canonicalSlots W (33/50)) ⟨W,hW,hWs,rfl⟩ Φ ao bo hao hab hΦs hΦ data
  exact ⟨degree,C,Z₀,hC,hZ₀,fun Z hZ =>
    inverseRectAt_old_of_new W (33/50) Φ K mesh 1 1 ε Z data degree C (hb Z hZ)⟩

/-- A source for the free family is one for the (fixed-ray) canonical family. -/
theorem InverseRectSource.of_free {ρ : AnchorRect} {mesh ε : ℝ}
    (hs : InverseRectSource canonicalFamilyFree ρ mesh ε) :
    InverseRectSource canonicalFamily ρ mesh ε := by
  rintro K cls ⟨W, hW, hWs, rayM, hne, G, hH, rfl⟩ Φ ao bo hao hab hΦs hΦ data
  obtain ⟨degree,C,Z₀,hC,hZ₀,hb⟩ :=
    hs K (canonicalSlots W (33/50)) ⟨W, hW, hWs, rfl⟩ Φ ao bo hao hab hΦs hΦ data
  exact ⟨degree,C,Z₀,hC,hZ₀,fun Z hZ =>
    inverseRectAt_mono_class (canonicalSlotsRay_le W (33/50) rayM G hH) Φ K mesh 1 1 ε Z data
      degree C (hb Z hZ)⟩

theorem UniformInverseRectSource.of_free {ρ : AnchorRect}
    (hs : UniformInverseRectSource canonicalFamilyFree ρ) :
    UniformInverseRectSource canonicalFamily ρ := by
  intro ε hε
  obtain ⟨mesh, hmesh, hsrc⟩ := hs ε hε
  exact ⟨mesh, hmesh, hsrc.of_free⟩

/-! ## The ordinary contract -/

/-- The two-ordinary rectangle as a source face: `m₁+m₂ ≤ Pmax`, `S ≤ Smax`, no marked
budget (`lam = 0`). It is HC's `globalFace Pmax 0 Smax`. -/
def AnchorRect.ordinaryFace (ρ : AnchorRect) : SourceFace :=
  QRH.Record1252270103Source.globalFace ρ.Pmax 0 ρ.Smax

/-- The ordinary anchor contract on the same rectangle. -/
def OrdinaryRectSource (ρ : AnchorRect) : Prop :=
  UniformUnitFaceSource ρ.ordinaryFace

theorem AnchorRect.ordinaryFace_restricts {strong weak : AnchorRect}
    (h : strong.Restricts weak) : strong.ordinaryFace.Restricts weak.ordinaryFace := by
  obtain ⟨hP,hS⟩ := h
  constructor <;> simp only [AnchorRect.ordinaryFace,QRH.Record1252270103Source.globalFace]
    <;> linarith

/-- Restriction of a unit-face source (upstream only has `mono_mesh`). -/
theorem unitFaceSource_restrict {strong weak : SourceFace} (h : strong.Restricts weak)
    {mesh ε : ℝ} (hs : UnitFaceSource strong mesh ε) : UnitFaceSource weak mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hev⟩ :=
    hs α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,controls,C,hC,hev.mono (fun Z hZ => initialAffineAt_restrict rayM H hH h W
    2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C zero_le_one hZ)⟩

theorem uniformUnitFaceSource_restrict {strong weak : SourceFace} (h : strong.Restricts weak)
    (hs : UniformUnitFaceSource strong) : UniformUnitFaceSource weak := by
  intro ε hε
  obtain ⟨mesh,hmesh,hsrc⟩ := hs ε hε
  exact ⟨mesh,hmesh,unitFaceSource_restrict h hsrc⟩

/-- Transport of `InitialAffineAt` along an implication of face admissions (needed because
`globalFace B L c` and `ordinaryFace` have different `lam`, so `Restricts` does not apply). -/
theorem initialAffineAt_of_admissible {α : Type} [Fintype α] [DecidableEq α]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O ⧸ rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) {strong weak : SourceFace}
    (W : ℝ → ℂ) (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (himp : ∀ m₁ m₂ s M : ℝ, Mmin ≤ M → 0 ≤ s →
      weak.Admissible m₁ m₂ s M → strong.Admissible m₁ m₂ s M)
    (hs : InitialAffineAt (α:=α) rayM H hH strong W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C) :
    InitialAffineAt (α:=α) rayM H hH weak W
      bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hadm
  exact hs T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂
    (himp _ _ _ M hMlo (Finset.sum_nonneg (fun i _ => hw i)) hadm)

theorem unitFaceSource_of_admissible {strong weak : SourceFace}
    (himp : ∀ m₁ m₂ s M : ℝ, 1 ≤ M → 0 ≤ s →
      weak.Admissible m₁ m₂ s M → strong.Admissible m₁ m₂ s M)
    {mesh ε : ℝ} (hs : UnitFaceSource strong mesh ε) : UnitFaceSource weak mesh ε := by
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,hev⟩ :=
    hs α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨degree,controls,C,hC,hev.mono (fun Z hZ => initialAffineAt_of_admissible rayM H hH W
    2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C himp hZ)⟩

/-- Admission transfer from the ordinary rectangle into a parent global face. -/
theorem ordinaryFace_admissible_global {ρ : AnchorRect} {B L c : ℝ}
    (hL : 0 ≤ L) (hB : ρ.Pmax+L*ρ.Smax ≤ B) (hc : ρ.Smax ≤ c)
    {m₁ m₂ s M : ℝ} (hM : 0 ≤ M) (hs : 0 ≤ s)
    (ha : ρ.ordinaryFace.Admissible m₁ m₂ s M) :
    (QRH.Record1252270103Source.globalFace B L c).Admissible m₁ m₂ s M := by
  obtain ⟨h1,_,h3,_,_,h6,h7⟩ := ha
  simp only [AnchorRect.ordinaryFace,QRH.Record1252270103Source.globalFace,zero_mul,
    add_zero] at h1 h3 h6 h7
  have hcM := mul_le_mul_of_nonneg_right hc hM
  have hBM := mul_le_mul_of_nonneg_right hB hM
  have hLs := mul_le_mul_of_nonneg_left h6 hL
  have hLs0 : 0 ≤ L*s := mul_nonneg hL hs
  refine (QRH.Record1252270103Source.globalFace_admissible_iff h1 h3 hs hL).mpr ⟨?_,?_⟩
  · linarith
  · nlinarith

/-- The native ordinary part: a global source `G(B,L,c)` covering the rectangle
(`Pmax + L*Smax ≤ B`, `Smax ≤ c`) supplies the ordinary anchor contract. -/
theorem ordinaryRectSource_of_global {ρ : AnchorRect} {B L c : ℝ}
    (hsrc : QRH.Record1252270103Source.GlobalSource B L c)
    (hL : 0 ≤ L) (hB : ρ.Pmax+L*ρ.Smax ≤ B) (hc : ρ.Smax ≤ c) : OrdinaryRectSource ρ := by
  intro ε hε
  obtain ⟨mesh,hmesh,hs⟩ := hsrc ε hε
  refine ⟨mesh,hmesh,unitFaceSource_of_admissible ?_ hs⟩
  intro m₁ m₂ s M hM hs0 ha
  exact ordinaryFace_admissible_global hL hB hc (zero_le_one.trans hM) hs0 ha

theorem OrdinaryRectSource.restrict {strong weak : AnchorRect} (h : strong.Restricts weak)
    (hs : OrdinaryRectSource strong) : OrdinaryRectSource weak :=
  uniformUnitFaceSource_restrict (AnchorRect.ordinaryFace_restricts h) hs

/-! ## Anchors and the improved family -/

/-- The anchor rectangle with endpoint decrement `δ`. -/
def anchorRect (R z δ : ℝ) : AnchorRect := ⟨R-δ, (1-R)/2+z-δ⟩

/-- Anchor `(R, z_R)`: for every decrement `δ > 0` BOTH contracts hold on the rectangle; the
inverse one for the canonical slot family. -/
def AnchorAt (R z : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    UniformInverseRectSource canonicalFamily (anchorRect R z δ) ∧
      OrdinaryRectSource (anchorRect R z δ)

/-- Left end `1467/2000` and base `311/400` of the improved free-width range. -/
def leftEnd : ℝ := 1467/2000
def topEnd : ℝ := 311/400

/-- The count's improved line: a minorant of the own line of chain stage 97 on
`[leftEnd, topEnd]`. The count consumes `ImprovedMoments leftEnd topEnd lineG0 lineG1`. -/
def lineG0 : ℝ := 55755437 / 1000000000
def lineG1 : ℝ := 14591009 / 200000000

/-- Improved fiber moments: at every free width `r ∈ [lo,hi]` the anchor `(r, g0 - g1*r)`,
i.e. free width `≤ r` and mark width `≤ (1-r)/2 + g0 - g1*r` (decremented). -/
def ImprovedMoments (lo hi g0 g1 : ℝ) : Prop :=
  ∀ r : ℝ, lo ≤ r → r ≤ hi → AnchorAt r (g0-g1*r)

theorem anchorRect_restricts {R z R' z' δ δ' : ℝ} (hP : R'-δ' ≤ R-δ)
    (hS : (1-R')/2+z'-δ' ≤ (1-R)/2+z-δ) :
    (anchorRect R z δ).Restricts (anchorRect R' z' δ') :=
  ⟨hP,hS⟩

theorem AnchorAt.rect {R z : ℝ} (h : AnchorAt R z) {δ : ℝ} (hδ : 0 < δ)
    {ρ : AnchorRect} (hρ : (anchorRect R z δ).Restricts ρ) :
    UniformInverseRectSource canonicalFamily ρ ∧ OrdinaryRectSource ρ :=
  ⟨(h δ hδ).1.restrict hρ,(h δ hδ).2.restrict hρ⟩

/-- Shortening an anchor: smaller free width and a lower mark line. -/
theorem AnchorAt.mono {R z r z' : ℝ} (h : AnchorAt R z) (hr : r ≤ R)
    (hS : (1-r)/2+z' ≤ (1-R)/2+z) : AnchorAt r z' := by
  intro δ hδ
  exact h.rect hδ (anchorRect_restricts (by linarith) (by linarith))

/-- Only small decrements need proof: a larger decrement shrinks the rectangle. -/
theorem AnchorAt.of_small {R z δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (h : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      UniformInverseRectSource canonicalFamily (anchorRect R z δ) ∧
        OrdinaryRectSource (anchorRect R z δ)) :
    AnchorAt R z := by
  intro δ hδ
  by_cases hle : δ ≤ δ₀
  · exact h δ hδ hle
  · have hlt : δ₀ < δ := lt_of_not_ge hle
    have hr : (anchorRect R z δ₀).Restricts (anchorRect R z δ) :=
      anchorRect_restricts (by linarith) (by linarith)
    exact ⟨(h δ₀ hδ₀ le_rfl).1.restrict hr,(h δ₀ hδ₀ le_rfl).2.restrict hr⟩

/-- A family of anchors whose rectangles dominate the improved line gives the improved
moments (each stage supplies the anchor `(r, Y(r)-δ)` for every `r` of the stage). -/
theorem improved_of_anchors {lo hi g0 g1 : ℝ}
    (h : ∀ r : ℝ, lo ≤ r → r ≤ hi →
      ∃ R z : ℝ, AnchorAt R z ∧ r ≤ R ∧ (1-r)/2+(g0-g1*r) ≤ (1-R)/2+z) :
    ImprovedMoments lo hi g0 g1 := by
  intro r hlo hhi
  obtain ⟨R,z,hA,hr,hS⟩ := h r hlo hhi
  exact hA.mono hr hS

/-- Monotonicity in the range and the gain line. -/
theorem ImprovedMoments.mono {lo hi g0 g1 lo' hi' g0' g1' : ℝ}
    (h : ImprovedMoments lo hi g0 g1) (hlo : lo ≤ lo') (hhi : hi' ≤ hi)
    (hline : ∀ r : ℝ, lo' ≤ r → r ≤ hi' → g0'-g1'*r ≤ g0-g1*r) :
    ImprovedMoments lo' hi' g0' g1' := by
  intro r hr1 hr2
  exact (h r (hlo.trans hr1) (hr2.trans hhi)).mono le_rfl (by linarith [hline r hr1 hr2])

/-- The improved rectangle at `r` with decrement `δ`, as consumed by the count. -/
theorem ImprovedMoments.rect {lo hi g0 g1 : ℝ} (h : ImprovedMoments lo hi g0 g1)
    {r δ : ℝ} (hlo : lo ≤ r) (hhi : r ≤ hi) (hδ : 0 < δ) :
    UniformInverseRectSource canonicalFamily (anchorRect r (g0-g1*r) δ) ∧
      OrdinaryRectSource (anchorRect r (g0-g1*r) δ) :=
  h r hlo hhi δ hδ

end
end Qrh.MarkedAnchor.Interface.Contract

#print axioms Qrh.MarkedAnchor.Interface.Contract.inverseRectAt_restrict
#print axioms Qrh.MarkedAnchor.Interface.Contract.ordinaryRectSource_of_global
#print axioms Qrh.MarkedAnchor.Interface.Contract.AnchorAt.of_small
#print axioms Qrh.MarkedAnchor.Interface.Contract.improved_of_anchors
#print axioms Qrh.MarkedAnchor.Interface.Contract.ImprovedMoments.mono
