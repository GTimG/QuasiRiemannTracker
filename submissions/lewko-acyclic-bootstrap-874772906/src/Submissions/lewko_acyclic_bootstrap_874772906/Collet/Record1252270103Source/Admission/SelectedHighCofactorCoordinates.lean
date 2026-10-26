/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual selected cofactor geometry and second-allocation scalar in the
literal lost-width coordinates used by the HIGH physical caller. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedHighCofactorGeometry
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.HighScalar.SingletonLoss
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
open CenteredMomentFirstAmplificationChoice CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open Cycle61Moment Cycle61InitialMass Record12518109Natural.MarkedPlain
open OAI.SevenEighths.Record1252270103Source Record1252270103Second
open SelectedHighSlots SelectedHighCoordinates HighScalar
local notation "O" => HeckeFamily.O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- This is the literal caller coordinate, with its required first-row orientation. -/
def cofactorCoordinates (reflected second : Bool) (l : FirstSourceLabel)
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A amp ξ reserve err errv forced live small annular : ℝ) : Fin 4→ℝ :=
  lostWidthCoordinates (childHighCoordinates
    (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U Z M A amp ξ reserve err) errv)
    (forced+live-small-annular)

theorem cofactor_coordinates_zero (reflected second : Bool) (l : FirstSourceLabel)
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A amp ξ reserve err errv forced live small annular : ℝ) :
    cofactorCoordinates reflected second l C₂ D₂ U Z M A amp ξ reserve err errv
      forced live small annular 0 =
      childHighCoordinates (actualHighCoordinates reflected (!reflected) second l C₂ D₂ U
        Z M A amp ξ reserve err) errv 0 := rfl

theorem cofactor_coordinates_three (reflected second : Bool) (l : FirstSourceLabel)
    (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (Z M A amp ξ reserve err errv forced live small annular : ℝ) :
    cofactorCoordinates reflected second l C₂ D₂ U Z M A amp ξ reserve err errv
      forced live small annular 3 = A-
      Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)-forced-live+small+annular := by
  dsimp [cofactorCoordinates,lostWidthCoordinates,childHighCoordinates,actualHighCoordinates]
  ring

section Geometry
variable {ι : Type} [Fintype ι]
variable (s : Input ι) (reflected second : Bool) (l : FirstSourceLabel) (R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (τ₁ : Character) (t₁ : ℝ) (C₂ D₂ : Ideal O)
    (B₂ : actualAllocations (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁).pools
      (if second then D₂ else C₂)) (τ₂ : Character) (t₂ : ℝ) (Cf : Ideal O)
    (Bf : actualAllocations (child (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁)
      (if second then D₂ else C₂) (R*(if reflected then l.1.2 else l.1.1)) B₂ τ₂ t₂).pools Cf)
    (τf : Character) (tf : ℝ)

/-- Actual third-child geometry in the exact x used by the cofactor caller.
The original volume is used exactly, so no target-coordinate capacity is assumed. -/
theorem actual_coordinate_geometry (U : Finset (CommonIndex C₂ D₂))
    (N : ℕ) (upper Z M amp ξ reserve err errv wmin b δ allowance : ℝ)
    (hN : Fintype.card ι≤N) (hupper : 1≤upper) (hsupper : s.upper≤upper)
    (hslower : 1≤s.lower) (hZ : 1<Z) (hmin : 0≤wmin)
    (w : ι→ℝ) (hscale : ∀i,s.P i=Z^(w i)) (hw : ∀i,0≤w i)
    (htotal : b-δ≤∑i,w i) (hwidth : (∑i,w i)≤b)
    (hloss : δ+(N:ℝ)*wmin≤2*allowance)
    (T : Finset ι) (hT : T⊆finalImage B₁.val B₂.val Bf.val)
    (hf₁ : frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0)
    (hf₂ : let s₁:=child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁
      frozenCoefficient B₂.val (if second then D₂ else C₂)
        (R*(if reflected then l.1.2 else l.1.1)) s₁.ν s₁.W s₁.P≠0)
    (hff : let s₂:=(child (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁)
        (if second then D₂ else C₂) (R*(if reflected then l.1.2 else l.1.1)) B₂ τ₂ t₂);
      frozenCoefficient Bf.val Cf ((R*(if reflected then l.1.2 else l.1.1))*(if second then D₂ else C₂))
        s₂.ν s₂.W s₂.P≠0) :
    let schild:=child (child (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁)
      (if second then D₂ else C₂) (R*(if reflected then l.1.2 else l.1.1)) B₂ τ₂ t₂)
      Cf ((R*(if reflected then l.1.2 else l.1.1))*(if second then D₂ else C₂)) Bf τf tf
    let full:=finalImage B₁.val B₂.val Bf.val
    let live:=∑i∈largeSlots full w wmin,w i
    let small:=∑i∈largeSlots T w wmin,w i
    let forced:=Real.logb Z (Cf.absNorm:ℝ)
    let annular:=3*(N:ℝ)*Real.logb Z upper
    let x:=cofactorCoordinates reflected second l C₂ D₂ U Z M (Real.logb Z (volume s))
      amp ξ reserve err errv forced live small annular
    x 3=Real.logb Z (volume s)-Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)-
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)-forced-live+small+annular ∧
    0≤forced ∧ 0≤small ∧ small≤live ∧ live≤b ∧
    b-2*allowance≤live+Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)+
      Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)+forced ∧
    (∑i∈T,w i)+(live-small)≤∑i∈full,w i ∧
    schild.X₁*schild.X₂≤Z^(x 3-∑i∈T,w i) ∧
    schild.X₁≤s.X₁ ∧ schild.X₂≤s.X₂ ∧ schild.Y₁≤s.Y₁ ∧ schild.Y₂≤s.Y₂ ∧
    (∏i,schild.P i)=∏i∈full,s.P i := by
  intro schild full live small forced annular x
  have hx:=cofactor_coordinates_three reflected second l C₂ D₂ U Z M (Real.logb Z (volume s))
    amp ξ reserve err errv forced live small annular
  refine ⟨hx,?_⟩
  have hV : volume s≤Z^(Real.logb Z (volume s)) :=
    (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (volume_pos s)).symm.le
  have hg:=SelectedHighCofactorGeometry.actual_canonical_cofactor_geometry s
    (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁ (if second then D₂ else C₂) B₂ τ₂ t₂
    Cf Bf τf tf hf₁ hf₂ hff N upper Z (Real.logb Z (volume s)) wmin b δ allowance
    hN hupper hsupper hslower hZ hV hmin w hscale hw htotal hwidth hloss T hT
  dsimp only at hg
  dsimp only [x]
  rw [hx]
  exact hg
end Geometry

/-- The original positive second-allocation coefficient, including the parent
MAIN radius, physical normalizer, frozen square, and volume/profile factors. -/
def secondAllocationCoefficient {ι : Type} [Fintype ι] (s : Input ι)
    (reflected second : Bool) (l : FirstSourceLabel) (R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (τ₁ : Character) (t₁ : ℝ) (C₂ D₂ : Ideal O) (U : Finset (CommonIndex C₂ D₂))
    (B₂ : actualAllocations (child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁).pools
      (if second then D₂ else C₂)) (τ₂ : Character) (t₂ Z M amp ξ reserve : ℝ) : ℝ :=
  let C₁:=if reflected then l.1.2 else l.1.1
  let s₁:=child s C₁ R B₁ τ₁ t₁
  let Cchosen:=if second then D₂ else C₂
  let s₂:=child s₁ Cchosen (R*C₁) B₂ τ₂ t₂
  Z^(-amp)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*amp) reserve l/volume s₁)*
    normalizer C₂ D₂ U*‖frozenCoefficient B₂.val Cchosen (R*C₁) s₁.ν s₁.W s₁.P‖^2*
      (volume s₂/volume s₁)*forcedProfileCost s₂

/-- A quantitative finite coefficient statement; zero profile costs are
handled by max(1,PC)^2, and the exact original weight can always be recovered. -/
def NormalizedSecondAllocationBound {ι : Type} [Fintype ι] (s : Input ι)
    (reflected second : Bool) (l : FirstSourceLabel) (R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (τ₁ : Character) (t₁ Z M amp ξ reserve err errv : ℝ) : Prop :=
  let s₁:=child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁
  ∀(C₂ D₂ : Ideal O),Supported C₂→∀(U : Finset (CommonIndex C₂ D₂))
    (B₂ : actualAllocations s₁.pools (if second then D₂ else C₂)) (τ₂ : Character) (t₂ : ℝ),
  ∀forced live small annular : ℝ,
  let raw:=secondAllocationCoefficient s reflected second l R B₁ τ₁ t₁ C₂ D₂ U B₂ τ₂ t₂ Z M amp ξ reserve
  let denom:=(max 1 (forcedProfileCost s₁))^2
  let x:=cofactorCoordinates reflected second l C₂ D₂ U Z M (Real.logb Z (volume s))
    amp ξ reserve err errv forced live small annular
  0≤raw/denom ∧ raw/denom≤Z^(x 0) ∧ raw=denom*(raw/denom)

/-- Normalize the checked literal second-allocation bound; the stronger
uniform theorem below discharges this finite bound from actual modified columns. -/
theorem normalize_second_allocation {ι : Type} [Fintype ι] (s : Input ι)
    (reflected second : Bool) (l : FirstSourceLabel) (R : Ideal O)
    (B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (τ₁ : Character) (t₁ Z M amp ξ reserve err errv : ℝ) (hZ : 1<Z)
    (hbound : SecondAllocationBound s reflected (!reflected) second l R B₁ τ₁ t₁ Z M amp ξ reserve err errv) :
    NormalizedSecondAllocationBound s reflected second l R B₁ τ₁ t₁ Z M amp ξ reserve err errv := by
  let s₁:=child s (if reflected then l.1.2 else l.1.1) R B₁ τ₁ t₁
  intro C₂ D₂ hC₂ U B₂ τ₂ t₂ forced live small annular raw denom x
  have hb:=hbound C₂ D₂ hC₂ U B₂ τ₂ t₂
  change raw≤(forcedProfileCost s₁)^2*Z^(x 0) at hb
  have hmax : 0<max 1 (forcedProfileCost s₁) := zero_lt_one.trans_le (le_max_left _ _)
  have hd : 0<denom := sq_pos_of_pos hmax
  have hp : (forcedProfileCost s₁)^2≤denom :=
    pow_le_pow_left₀ (forcedProfileCost_nonneg s₁) (le_max_right _ _) _
  have hn : 0≤raw := by
    dsimp only [raw,secondAllocationCoefficient]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
        (div_nonneg (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*amp) reserve
          (zero_lt_one.trans hZ) l).le (volume_pos _).le))
      (normalizer_pos C₂ D₂ hC₂ U).le) (sq_nonneg _))
      (div_nonneg (volume_pos _).le (volume_pos _).le)) (forcedProfileCost_nonneg _)
  refine ⟨div_nonneg hn hd.le,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    exact hb.trans (by simpa [mul_comm] using
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (zero_lt_one.trans hZ).le (x 0)))
  · field_simp

/-- The threshold precedes all actual original Inputs, modified columns and
both selected allocations. No coefficient-bound or analytic premise remains. -/
theorem eventual_modified_normalized_cofactor (N : ℕ) (lo errv : ℝ) (hlo : 0<lo) (he : 0<errv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type} [Fintype ι] (s : Input ι),
    Fintype.card ι≤N→lo≤s.lower→∀(modifier : CenteredMomentAddedZeroUniform.Tuple ι→ℂ)
      (R seed : Ideal O) (K ξ : ℝ) (hK : 0<K) (bin : ℤ×(Fin 5→ℤ))
      (j : FirstColumnIndex (High.CoupledFirst.geometryFirstSource s modifier R seed K Z ξ hK bin))
      (reflected second : Bool),
    let l:=FirstFamily.firstLabel s modifier R seed K Z ξ hK bin j
    ∀(B₁ : actualAllocations s.pools (if reflected then l.1.2 else l.1.1)) (τ₁ : Character) (t₁ : ℝ),
    frozenCoefficient B₁.val (if reflected then l.1.2 else l.1.1) R s.ν s.W s.P≠0→
    ∀M amp reserve err : ℝ,
    NormalizedSecondAllocationBound s reflected second l R B₁ τ₁ t₁ Z M amp ξ reserve err errv := by
  filter_upwards [eventual_modified_high_coefficient N lo errv hlo he] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι inst s hN hloS modifier R seed K ξ hK bin j reflected second l B₁ τ₁ t₁ hB₁ M amp reserve err
  exact normalize_second_allocation s reflected second l R B₁ τ₁ t₁ Z M amp ξ reserve err errv hz.1
    (hz.2 s hN hloS modifier R seed K ξ hK bin j reflected (!reflected) second B₁ τ₁ t₁ hB₁
      M amp reserve err)

end
end QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates.cofactor_coordinates_zero
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates.cofactor_coordinates_three
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates.actual_coordinate_geometry
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates.normalize_second_allocation
#print axioms QRH.Record1252270103Source.Admission.SelectedHighCofactorCoordinates.eventual_modified_normalized_cofactor
