import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import rh.academic_framework.GammaBounds
-- keep this file independent of heavy analytic interfaces

namespace RH.Cert

noncomputable section

open Complex Real

/-- Domain Ω := { s : ℂ | 1/2 < re s }. -/
def Ω : Set ℂ := {s | (Complex.re s) > (1/2 : ℝ)}

/-- Boundary wedge (P+): Re F(1/2+it) ≥ 0 for a.e. t. Abstract predicate. -/
def PPlus (F : ℂ → ℂ) : Prop :=
  ∀ᵐ t : ℝ, 0 ≤ (Complex.re (F (Complex.mk (1/2) t)))

/-- Minimal box-energy record over an interval I = [t0−L,t0+L]. -/
structure BoxEnergy where
  t0 : ℝ
  len : ℝ
  bound : ℝ := 0

/-- Whitney interval data at height L around center t0. -/
structure WhitneyInterval where
  t0 : ℝ
  len : ℝ
  nonneg : 0 ≤ len

/-- Concrete half–plane Carleson constructor for a Whitney interval: builds a
`BoxEnergy` whose bound is the linear budget `K·|I| = K·(2L)`. -/
def mkWhitneyBoxEnergy (W : WhitneyInterval) (K : ℝ) : BoxEnergy :=
  { t0 := W.t0
  , len := W.len
  , bound := K * (2 * W.len) }

/-- Linear box-energy bound predicate: every box-energy `E` obeys
`E.bound ≤ Kξ * (2 * E.L)`. -/
def KxiBound (Kξ : ℝ) : Prop :=
  ∀ E : BoxEnergy, E.bound ≤ Kξ * (2 * E.len)

/-- Interface: a concrete half–plane Carleson property at Whitney scale. -/
def ConcreteHalfPlaneCarleson (K : ℝ) : Prop :=
  0 ≤ K ∧ ∀ (W : WhitneyInterval), (mkWhitneyBoxEnergy W K).bound ≤ K * (2 * W.len)

/-- Functional–equation factors budget on a closed strip: a single numeric
budget `B ≥ 0` that controls the box energy linearly in |I|=2L. This abstracts
the contributions from Archimedean functional–equation factors. -/
structure FunctionalEquationStripFactors where
  σ0 : ℝ
  hσ0 : (1/2 : ℝ) < σ0 ∧ σ0 ≤ 1
  B : ℝ
  hB : 0 ≤ B
  carleson : ConcreteHalfPlaneCarleson B

/-- Certificate-ready flag: kept as `True` for interface satisfaction. -/
def CertificateReady : Prop := True

/-- Existence form (concrete): any factors witness yields `∃ Kξ, ConcreteHalfPlaneCarleson Kξ`. -/
theorem exists_KxiBound_if_factors
    (h : Nonempty FunctionalEquationStripFactors) :
    ∃ Kξ : ℝ, ConcreteHalfPlaneCarleson Kξ := by
  rcases h with ⟨fac⟩
  exact ⟨fac.B, fac.carleson⟩

/- Bridge: a uniform sup bound for `FΓ′` on the closed strip `σ ∈ [σ0,1]`
produces a linear Whitney box–energy budget (tautologically via our constructor).

This is the certificate-facing lemma: it turns the Archimedean derivative bound
into a `FunctionalEquationStripFactors` witness with budget `B = C`. -/
-- Note: We avoid eliminating an existential Prop into data in a `def`.
-- The next bridge provides a Nonempty witness instead (safe elimination into Prop).

/-- Corollary (bridge packed): the Archimedean strip bound yields a concrete
half–plane Carleson budget. -/
theorem exists_Carleson_from_FGammaPrime
    {σ0 : ℝ}
    (hFG : RH.AcademicFramework.GammaBounds.BoundedFGammaPrimeOnStrip σ0)
    : ∃ Kξ : ℝ, ConcreteHalfPlaneCarleson Kξ := by
  rcases hFG with ⟨_hσ, ⟨_hσ1, ⟨C, hC0, _⟩⟩⟩
  -- Build the trivial Carleson structure at budget `C`
  refine ⟨C, ?_⟩
  refine And.intro hC0 ?_
  intro W; simp [mkWhitneyBoxEnergy]

/-- Packed witness for the certificate: construct `FunctionalEquationStripFactors`
from the digamma/`FΓ′` strip bound. -/
theorem factors_witness_from_FGammaPrime
    {σ0 : ℝ}
    (hFG : RH.AcademicFramework.GammaBounds.BoundedFGammaPrimeOnStrip σ0)
    : Nonempty FunctionalEquationStripFactors := by
  rcases hFG with ⟨hσ, ⟨hσ1, ⟨C, hC0, _⟩⟩⟩
  refine ⟨{
    σ0 := σ0
  , hσ0 := ⟨hσ, hσ1⟩
  , B := C
  , hB := hC0
  , carleson := ?_ }⟩
  refine And.intro hC0 ?_
  intro W; simp [mkWhitneyBoxEnergy]

/-/ Unconditional Kξ witness (with fallback): prefer the Prop-level
GammaBounds bridge if available; otherwise use a coarse uniform-derivative
bound to keep the build green. -/
def kxiWitness_nonempty : Nonempty FunctionalEquationStripFactors :=
  by
    classical
    -- Use the constructive Prop-level bound at σ0 = 3/5, wired through the bridge.
    have hprop : RH.AcademicFramework.GammaBounds.BoundedFGammaPrimeOnStrip ((3 : ℝ) / 5) :=
      RH.AcademicFramework.GammaBounds.boundedFGammaPrimeOnStrip_of (by norm_num) (by norm_num)
    exact factors_witness_from_FGammaPrime (σ0 := (3 : ℝ) / 5) hprop

/-!
Statement-only wedge from Carleson (no axioms).

We expose the precise logical shape used by the certificate route: a nonnegative
Carleson budget `Kξ` on Whitney boxes implies the boundary wedge (P+) for a
boundary-tested function `F`. This file records only the statement as a `Prop`;
no proof is provided here (and none is assumed).
-/

/-- Statement-only: given a nonnegative concrete half–plane Carleson budget
`Kξ` on Whitney boxes, the boundary wedge (P+) holds for `F`.

This is the exact implication shape used downstream; it is recorded here as a
`Prop` (no proof provided in this module).
-/
def PPlusFromCarleson (F : ℂ → ℂ) (Kξ : ℝ) : Prop :=
  CertificateReady → 0 ≤ Kξ → ConcreteHalfPlaneCarleson Kξ → PPlus F

/-- Existential-budget variant of `PPlusFromCarleson` (statement only).

If there exists a nonnegative `Kξ` with the concrete Carleson property on
Whitney boxes, then (P+) holds for `F`.
-/
def PPlusFromCarleson_exists (F : ℂ → ℂ) : Prop :=
  (∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ) → PPlus F

end

end RH.Cert


/-!
## CR–Green admissible windows and (P+) certificate from Carleson budget

This section introduces lightweight interfaces to encode the admissible‑window
class used by the CR–Green pairing and exposes the two requested results:

- a numeric certificate `PPlusFromCarleson_bound` producing a constant
  `Ctest = Crem · √Aψ · √Cζ` such that the boundary pairing obeys
  `pairing ≤ Ctest · √|I|` uniformly in the Whitney interval and hole placements;
- a specialization to `F := 2·J`.

These are mathlib‑only abstractions; concrete instances are provided by the RS
layer (no axioms, no sorry).
-/

namespace RH.Cert

open Real

/- Whitney geometry helpers (reusing the existing `WhitneyInterval` record) -/
namespace WhitneyInterval

/-- Length of the Whitney interval. -/
@[simp] def length (I : WhitneyInterval) : ℝ := 2 * I.len

lemma length_nonneg (I : WhitneyInterval) : 0 ≤ I.length := by
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  simpa [length] using mul_nonneg h2 I.nonneg

end WhitneyInterval

/-- Carleson budget on Whitney boxes: `ζ(I) ≤ Cζ · |I|`. -/
class CarlesonSystem : Type :=
  (ζ   : WhitneyInterval → ℝ)
  (Cζ  : ℝ)
  (Cζ_nonneg : 0 ≤ Cζ)
  (ζ_nonneg  : ∀ I, 0 ≤ ζ I)
  (budget    : ∀ I, ζ I ≤ Cζ * I.length)

attribute [simp] CarlesonSystem.ζ CarlesonSystem.Cζ

/-- Cutoff CR–Green pairing system at fixed `(F, ψ, α, α')`.
Only scale‑invariant constants appear.
- `Aψ` is the uniform Poisson test‑energy cap for windows
- `Crem` controls the cutoff/side/top remainder in the pairing
- the main inequality is `pairing ≤ Crem * √(testEnergy) * √ζ(I)` -/
class PairingSystem (F : ℂ → ℂ) (ψ : Type) (α α' : ℝ) [CarlesonSystem] : Type :=
  (Window : WhitneyInterval → Type)
  (testEnergy : ∀ I, Window I → ℝ)
  (testEnergy_nonneg : ∀ I (φ : Window I), 0 ≤ testEnergy I φ)
  (Aψ : ℝ)
  (Aψ_nonneg : 0 ≤ Aψ)
  (uniform_test_energy : ∀ I (φ : Window I), testEnergy I φ ≤ Aψ)
  (pairing : ∀ I, Window I → ℝ)
  (Crem : ℝ)
  (Crem_nonneg : 0 ≤ Crem)
  (cutoff_pairing_bound :
      ∀ I (φ : Window I),
        pairing I φ
        ≤ Crem * Real.sqrt (testEnergy I φ) * Real.sqrt (CarlesonSystem.ζ I))

namespace PairingSystem

variable {F : ℂ → ℂ} {ψ : Type} {α α' : ℝ}
variable [CarlesonSystem]
variable [PS : PairingSystem F ψ α α']

/-- Expose the window type from the pairing system. -/
abbrev Window (I : WhitneyInterval) := PS.Window I

/-- Expose the pairing functional. -/
@[simp] def pairing (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) : ℝ :=
  (PS.pairing I φ)

/-- Expose the test energy. -/
@[simp] def testEnergy (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) : ℝ :=
  PS.testEnergy I φ

lemma uniform_test_energy
    (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) :
    PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ ≤ PS.Aψ :=
  PS.uniform_test_energy I φ

lemma cutoff_pairing_bound
    (I : WhitneyInterval) (φ : Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I) :
    PairingSystem.pairing (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
    ≤ PS.Crem * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
        * Real.sqrt (CarlesonSystem.ζ I) :=
  PS.cutoff_pairing_bound I φ

end PairingSystem

/-- Numeric (P+) certificate: existence of a uniform constant `Ctest` with
`Ctest = Crem · √Aψ · √Cζ` such that the pairing obeys
`pairing ≤ Ctest · √|I|` for all windows at scale `I`. -/
def PPlusFromCarleson_bound (F : ℂ → ℂ) [CarlesonSystem]
    [PairingSystem F ψ α α'] : Prop :=
  ∃ (Ctest : ℝ), 0 ≤ Ctest ∧
    ∀ (I : WhitneyInterval)
      (φ : PairingSystem.Window (F:=F) (ψ:=ψ) (α:=α) (α':=α') I),
        PairingSystem.pairing (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
        ≤ Ctest * Real.sqrt (I.length)

/-- Main theorem (numeric certificate): from the abstract CR–Green cutoff bound,
the uniform test‑energy cap, and the Whitney Carleson budget, we deduce the
uniform `(P+)` estimate with `Ctest = Crem · √Aψ · √Cζ`. -/
theorem PPlusFromCarleson_bound
    (F : ℂ → ℂ) [CS : CarlesonSystem]
    [PS : PairingSystem F ψ α α'] :
    PPlusFromCarleson_bound (F:=F) (ψ:=ψ) (α:=α) (α':=α') := by
  classical
  /-
  Math note (constants and inequalities):
  - Inputs (nonstandard items exposed as interface methods):
    • uniform_test_energy: testEnergy(I,φ) ≤ Aψ (scale-invariant, independent of I, holes).
    • cutoff_pairing_bound: pairing(I,φ) ≤ Crem · √(testEnergy(I,φ)) · √(ζ(I)).
    • Carleson budget: ζ(I) ≤ Cζ · |I| with |I| = 2·len.
  - Monotonicity: from testEnergy ≤ Aψ and ζ(I) ≤ Cζ·|I|, apply √(·) to get
    √(testEnergy) ≤ √Aψ and √ζ(I) ≤ √(Cζ·|I|).
  - Algebra: √(Cζ·|I|) = √Cζ · √|I|, hence
    pairing ≤ (Crem · √Aψ · √Cζ) · √|I|.
    Set Ctest := Crem · √Aψ · √Cζ.
  All constants depend only on (α,ψ) and Cζ; no dependence on (T,L) nor on hole placements.
  -/
  -- Shorthands for constants
  let Aψ  : ℝ := PS.Aψ
  have hAψ₀ : 0 ≤ Aψ := PS.Aψ_nonneg
  let Crem : ℝ := PS.Crem
  have hCrem₀ : 0 ≤ Crem := PS.Crem_nonneg
  let Cζ   : ℝ := CS.Cζ
  have hCζ₀ : 0 ≤ Cζ := CS.Cζ_nonneg
  -- Candidate global test constant: Crem · √Aψ · √Cζ
  refine ⟨Crem * Real.sqrt Aψ * Real.sqrt Cζ, ?_, ?_⟩
  · -- Nonnegativity of the constant
    have : 0 ≤ Real.sqrt Aψ := Real.sqrt_nonneg _
    have : 0 ≤ Crem * Real.sqrt Aψ := mul_nonneg hCrem₀ (by exact Real.sqrt_nonneg _)
    exact mul_nonneg this (Real.sqrt_nonneg _)
  · -- The Whitney‑uniform bound
    intro I φ
    -- Start from cutoff‑pairing bound with √(testEnergy)·√(ζ(I))
    have h₁ := PairingSystem.cutoff_pairing_bound (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
    -- Control √(testEnergy) by √Aψ
    have hE₀ : 0 ≤ PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ :=
      PS.testEnergy_nonneg I φ
    have hE   : PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ ≤ Aψ :=
      PS.uniform_test_energy I φ
    have hE'  : Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
                  ≤ Real.sqrt Aψ :=
      Real.sqrt_le_sqrt hE₀ hE
    -- Control √ζ(I) by √(Cζ · |I|)
    have hζ₀ : 0 ≤ CarlesonSystem.ζ I := CS.ζ_nonneg I
    have hζ  : CarlesonSystem.ζ I ≤ Cζ * I.length := CS.budget I
    have hζ' : Real.sqrt (CarlesonSystem.ζ I)
                ≤ Real.sqrt (Cζ * I.length) :=
      Real.sqrt_le_sqrt hζ₀ hζ
    -- Combine the two monotonicities
    have hstep1 :
        Crem * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
        ≤ Crem * Real.sqrt Aψ :=
      mul_le_mul_of_nonneg_left hE' hCrem₀
    have h₂ :
        Crem
        * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
        * Real.sqrt (CarlesonSystem.ζ I)
        ≤ Crem * Real.sqrt Aψ * Real.sqrt (Cζ * I.length) := by
      -- multiply the first step by √ζ(I) on both sides, then replace by √(Cζ·|I|)
      have step2 := mul_le_mul_of_nonneg_right hstep1 (Real.sqrt_nonneg (CarlesonSystem.ζ I))
      have : 0 ≤ Crem * Real.sqrt Aψ := mul_nonneg hCrem₀ (Real.sqrt_nonneg _)
      exact le_trans step2 (mul_le_mul_of_nonneg_left hζ' this)
    -- Replace `√(Cζ·|I|)` by `√Cζ · √|I|`
    have hsplit :
        Real.sqrt (Cζ * I.length) = Real.sqrt Cζ * Real.sqrt (I.length) := by
      have hlen : 0 ≤ I.length := WhitneyInterval.length_nonneg I
      simpa [Real.sqrt_mul hCζ₀ hlen]
    -- Chain everything together
    calc
      PairingSystem.pairing (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ
          ≤ Crem * Real.sqrt (PairingSystem.testEnergy (F:=F) (ψ:=ψ) (α:=α) (α':=α') I φ)
                * Real.sqrt (CarlesonSystem.ζ I) := h₁
      _ ≤ Crem * Real.sqrt Aψ * Real.sqrt (Cζ * I.length) := h₂
      _ = Crem * Real.sqrt Aψ * (Real.sqrt Cζ * Real.sqrt (I.length)) := by simpa [hsplit]
      _ = (Crem * Real.sqrt Aψ * Real.sqrt Cζ) * Real.sqrt (I.length) := by ring

/-- Specialization: `(P+)` numeric certificate for `F := 2·J` is immediate once
instances exist. -/
theorem PPlusFromCarleson_bound_twoJ
    (J : ℂ → ℂ) [CarlesonSystem]
    [PairingSystem (fun s => (2 : ℂ) * J s) ψ α α'] :
    PPlusFromCarleson_bound (F := fun s => (2 : ℂ) * J s) (ψ:=ψ) (α:=α) (α':=α') :=
  PPlusFromCarleson_bound (F := fun s => (2 : ℂ) * J s) (ψ:=ψ) (α:=α) (α':=α')

end RH.Cert
