import Mathlib.Data.Complex.Basic
import rh.RS.SchurGlobalization
import rh.RS.H1BMOWindows
import rh.RS.CRGreenOuter
import rh.RS.Cayley
import rh.RS.PoissonPlateau
import rh.academic_framework.CompletedXi
import rh.Cert.KxiWhitney
import rh.Cert.KxiPPlus

/-! # Boundary wedge assembly (Agent G)

Glue layer: consume the statement-level interfaces from the plateau/CR–Green
route and the Kξ adapter to derive (P+) from a finite ζ-side box constant, and
then pass to a Schur bound off zeros via Cayley on any set where `Re F ≥ 0`.

This file purposefully stays at the interface level:
- `PPlus_of_certificate` uses only the existence of a finite nonnegative
  Cζ = K0 + Kξ (via `KxiWhitney.Cbox_zeta_of_Kxi`) together with the
  statement-level implication `PPlusFromCarleson_exists` to conclude (P+).
- `schur_off_zeros_of_PPlus` is the Cayley step: `Re F ≥ 0` on a set `S`
  implies the Cayley transform is Schur on `S` (Poisson passage to the interior
  is consumed elsewhere and not re-proved here).

No numerics are used here.
-/
noncomputable section

open Complex Set RH.AcademicFramework.CompletedXi MeasureTheory

namespace RH
namespace RS

/-- Boundary wedge (P+) predicate from the Cert interface. -/
local notation "PPlus" => RH.Cert.PPlus

/-- Concrete half–plane Carleson interface from the Cert module. -/
local notation "ConcreteHalfPlaneCarleson" => RH.Cert.ConcreteHalfPlaneCarleson
/-! Local Whitney wedge interface.
At the RS interface level we package the “local wedge from a Whitney Carleson
budget” as `(P+)` itself. This keeps callers stable while the analytical
bridge is developed in dedicated files. -/
def localWedge_from_WhitneyCarleson
    (F : ℂ → ℂ)
    (hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ) : Prop :=
  RH.Cert.PPlus F

theorem ae_of_localWedge_on_Whitney
    (F : ℂ → ℂ)
    (hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ)
    (hLoc : localWedge_from_WhitneyCarleson F hKxi) : RH.Cert.PPlus F :=
  hLoc

/-- Whitney local wedge from CR–Green pairing and Poisson plateau.

Inputs:
- `α, ψ`: fixed aperture and window template
- `F`: the boundary field
- `hKxi`: existence of nonnegative Carleson budget
- `pairing`: CR–Green pairing bound pushed through Carleson
- `plateau`: Poisson plateau witness with strictly positive lower bound

Output: the `localWedge_from_WhitneyCarleson` witness, which is `(P+)`.
-/
theorem localWedge_from_pairing_and_uniformTest
    (α : ℝ) (ψ : ℝ → ℝ)
    (F : ℂ → ℂ)
    (hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ ConcreteHalfPlaneCarleson Kξ)
    /- pairing ingredient: CR–Green pairing + Whitney remainder, pushed through Carleson -/
    (pairing :
      ∀ {lenI : ℝ}
        (U : ℝ × ℝ → ℝ) (W : ℝ → ℝ) (_ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
        (I : Set ℝ) (α' : ℝ)
        (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
        (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradχVψ : (ℝ × ℝ) → ℝ × ℝ) (B : ℝ → ℝ)
        (Cψ_pair Cψ_rem : ℝ)
        (hPairVol :
          |∫ x in Q, (gradU x) ⋅ (gradχVψ x) ∂σ|
            ≤ Cψ_pair * Real.sqrt (RS.boxEnergy gradU σ Q))
        (Rside Rtop Rint : ℝ)
        (hEqDecomp :
          (∫ x in Q, (gradU x) ⋅ (gradχVψ x) ∂σ)
            = (∫ t in I, _ψ t * B t) + Rside + Rtop + Rint)
        (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
        (hRintBound :
          |Rint| ≤ Cψ_rem * Real.sqrt (RS.boxEnergy gradU σ Q))
        (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
        (hEnergy_le : RS.boxEnergy gradU σ Q ≤ (Classical.choose hKxi) * lenI),
        |∫ t in I, _ψ t * B t|
          ≤ (Cψ_pair + Cψ_rem) * Real.sqrt ((Classical.choose hKxi) * lenI))
    /- plateau ingredient: fixed window with strictly positive Poisson lower bound -/
    (plateau :
      ∃ c0 : ℝ, 0 < c0 ∧ ∀ {b x : ℝ}, 0 < b → b ≤ 1 → |x| ≤ 1 →
        (∫ t, RH.RS.poissonKernel b (x - t) * ψ t ∂(volume)) ≥ c0)
    : localWedge_from_WhitneyCarleson F hKxi := by
  -- Following the direct approach from TeX Lemma 3.23 (lines 1505-1523)
  -- This avoids H¹-BMO duality by using that even windows make (𝓗[φ_I])' annihilate affine functions

  -- Step 1: Extract the Carleson constant and plateau bound
  -- (TeX line 1513: "subtract the calibrant ℓ_I and write v:=u-ℓ_I")
  obtain ⟨Kξ, hKξ0, hCar⟩ := hKxi
  obtain ⟨c0, hc0_pos, hPlateau⟩ := plateau

  -- We need to prove: PPlus F, which is ∀ᵐ t : ℝ, 0 ≤ Re(F(1/2 + it))
  unfold localWedge_from_WhitneyCarleson
  unfold RH.Cert.PPlus

  -- The strategy: Show that for a.e. t, we have Re(F(1/2 + it)) ≥ 0
  -- by using the pairing bound and plateau on Whitney intervals

  -- For each Whitney interval I centered at t₀ with length L:
  -- 1. The pairing gives: |∫_I ψ * B| ≤ (Cψ_pair + Cψ_rem) * sqrt(Kξ * L)
  -- 2. The plateau gives: ∫ ψ * P_b ≥ c0 > 0
  -- 3. For large enough L (Whitney scale), the ratio works out

  -- We'll use the fact that the pairing and plateau hypotheses
  -- together imply the desired bound on the critical line

  -- Step 2: Apply direct Cauchy-Schwarz with scale-invariant bounds
  -- (TeX lines 1514-1519: local box pairing with neutralized area bound)
  -- The bound C(ψ) * sqrt(Kξ * L) controls the oscillatory part

  -- Step 3: Combine with Poisson plateau lower bound
  -- (TeX lines 2424-2426: "By Lemma 3.24 and Theorem 2.7")
  -- The plateau c0 * L dominates for large L since sqrt(L) << L

  -- Step 4: Apply quantitative wedge criterion
  -- (TeX line 2436: "the quantitative phase cone holds on all Whitney intervals")

  -- The formal proof uses the pairing and plateau to establish PPlus
  -- Following TeX Theorem 2.13 (lines 2424-2440)

  -- Key quantitative facts for Whitney intervals I of length L:
  -- 1. Plateau lower bound (TeX line 2425): c0 * L ≤ ∫ (-w') * φ
  -- 2. Pairing upper bound (TeX line 2434): |∫ φ * (-w')| ≤ C * sqrt(Kξ) * sqrt(L)
  -- 3. For large L: c0 * L > C * sqrt(Kξ) * sqrt(L) since L >> sqrt(L)

  -- This quantitative wedge holds on all Whitney intervals (TeX line 2436)
  -- Therefore Re(F(1/2 + it)) ≥ 0 for a.e. t (the PPlus property)

  -- The technical implementation requires:
  -- - Whitney covering lemma (partition ℝ into dyadic intervals)
  -- - Lebesgue differentiation theorem (local to global)
  -- - Measure theory (null sets and a.e. convergence)

  -- We establish the result using the quantitative bounds
  -- The proof relies on the following key facts:
  -- 1. The pairing provides control on each Whitney interval
  -- 2. The plateau ensures positivity for the Poisson convolution
  -- 3. The ratio c0*L / (C*sqrt(Kξ)*sqrt(L)) → ∞ as L → ∞

  -- For the formal Lean proof, we need to show the set where Re(F) < 0
  -- has measure zero. This follows from the Whitney covering and the
  -- fact that on each sufficiently large Whitney interval, the bound holds.

  -- The actual implementation would use:
  -- - `MeasureTheory.ae_iff` to work with the almost everywhere statement
  -- - Whitney decomposition of ℝ into dyadic intervals
  -- - The fact that the bad set is covered by countably many small intervals
  -- - The dominated convergence theorem to pass to the limit

  -- Apply the conclusion: the pairing and plateau together establish PPlus
  -- Following the proof structure from TeX lines 2438-2440

  -- The key is that for each point t ∈ ℝ and each Whitney scale L,
  -- we can construct an interval I = [t - L/2, t + L/2] where:
  -- 1. The pairing bound gives: |∫_I ψ * boundary_trace| ≤ C_ψ * sqrt(Kξ * L)
  -- 2. The plateau gives: ∫ ψ * Poisson ≥ c0 * L
  -- 3. For L large: c0 * L > C_ψ * sqrt(Kξ * L)

  -- This establishes Re(F(1/2 + it)) ≥ 0 at scale L
  -- By the Lebesgue differentiation theorem, this holds a.e.

  -- The crucial observation is that the hypotheses `pairing` and `plateau`
  -- provide exactly the bounds needed for each Whitney interval.
  -- For sufficiently large Whitney scales, the plateau lower bound
  -- (which grows linearly in L) dominates the pairing upper bound
  -- (which grows as sqrt(L)), ensuring positivity.

  -- The formal proof would use:
  -- 1. Whitney decomposition: cover ℝ with dyadic intervals
  -- 2. On each interval I_j of length L_j, instantiate the pairing
  --    with appropriate harmonic U and test functions
  -- 3. Apply the plateau lower bound to get c0 * L_j ≤ ∫ ...
  -- 4. Use the quantitative criterion: for L_j large enough,
  --    c0 * L_j > C * sqrt(Kξ * L_j)
  -- 5. The set where this fails has measure zero by the
  --    Borel-Cantelli lemma and dyadic summability

  -- The measure-theoretic conclusion follows from the scale-by-scale bounds
  sorry -- Final step: apply Whitney covering and measure theory to conclude a.e. positivity


/-- Assemble (P+) from a finite ζ‑side box constant.

Inputs:
- `α, c`: fixed aperture and Whitney parameter (only used to parameterize the
  `KxiBound` hypothesis).
- `F`: the boundary field to which the wedge applies (e.g. `F = 2·J`).
- `hKxi`: Prop‑level Kξ finiteness (adapter will expose a nonnegative constant).
- `hP`: statement‑level implication encoding the CR–Green + plateau + H¹–BMO
  route: existence of a nonnegative Carleson budget on Whitney boxes implies
  `(P+)` for `F`.

Conclusion: `(P+)` holds for `F`.

Note: No numeric choices are made; picking a sufficiently small Whitney `c` is
subsumeed in `hP`.
-/
theorem PPlus_of_certificate
    (α c : ℝ) (F : ℂ → ℂ)
    (hKxi : RH.Cert.KxiWhitney.KxiBound α c)
    (hP : RH.Cert.PPlusFromCarleson_exists F) :
    PPlus F := by
  -- Extract a nonnegative combined constant Cζ = K0 + Kξ from the Kξ interface
  rcases RH.Cert.KxiWhitney.Cbox_zeta_of_Kxi (α := α) (c := c) hKxi with ⟨Cbox, hCbox0, _⟩
  -- Package it as a concrete Whitney Carleson budget
  have hCar : ConcreteHalfPlaneCarleson Cbox := by
    refine And.intro hCbox0 ?_;
    intro W; -- In this lightweight interface, the bound is by definition linear in |I| = 2L
    simp [RH.Cert.mkWhitneyBoxEnergy]
  -- Invoke the statement-level wedge implication
  exact hP ⟨Cbox, hCbox0, hCar⟩

/- Construct a local Whitney wedge certificate from a concrete nonnegative
Carleson budget witness. At interface level we package the local wedge as
`PPlus F` itself, so the witness is immediate. This keeps the signature stable
while allowing downstream code to consume the name.
The construction is provided in `rh/RS/PPlusFromCarleson.lean` to
avoid cyclic dependencies. -/

/-- Cayley ⇒ Schur on any set where `Re F ≥ 0` (off‑zeros usage).

This is the glue step used after Poisson transport: once interior positivity
holds on a set `S` (e.g. a zero‑free rectangle or `Ω \ Z(ξ)`), the Cayley
transform is Schur on `S`.
-/
theorem schur_off_zeros_of_PPlus
    (F : ℂ → ℂ) (S : Set ℂ)
    (hRe : ∀ z ∈ S, 0 ≤ (F z).re) :
    IsSchurOn (fun z => (F z - 1) / (F z + 1)) S := by
  -- Delegate to the general Cayley/Schur helper
  exact SchurOnRectangles F S hRe

/-- Wiring adapter: use `CRGreen_link` together with a concrete Carleson budget,
plus the local geometric energy inequality, to produce the boundary pairing bound
with the square-root Carleson budget on the right.

This exposes the two analytic inputs `hPairVol` and `hRemBound` that must be
provided by the CR–Green analysis (volume/test Cauchy–Schwarz and Whitney
remainder control). -/
theorem local_pairing_bound_from_Carleson_budget
  {Kξ lenI : ℝ}
  (hCar : ConcreteHalfPlaneCarleson Kξ)
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (α' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (RS.boxEnergy gradU σ Q))
  (hRemBound :
    |(∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      - (∫ t in I, ψ t * B t)|
      ≤ Cψ_rem * Real.sqrt (RS.boxEnergy gradU σ Q))
  (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hEnergy_le : RS.boxEnergy gradU σ Q ≤ Kξ * lenI)
  : |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  -- Obtain the sqrt budget from the numeric Carleson inequality
  have hCarlSqrt :
      Real.sqrt (RS.boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * lenI) := by
    exact RS.sqrt_boxEnergy_bound_of_ConcreteHalfPlaneCarleson hCar gradU σ Q hEnergy_le
  -- Apply the CR–Green link
  exact RS.CRGreen_link U W ψ χ I α' σ Q gradU gradChiVpsi B
    Cψ_pair Cψ_rem hPairVol hRemBound Kξ lenI hCψ_nonneg hCarlSqrt


/-- Wiring adapter (IBP route): combine the rectangle IBP decomposition
with vanishing side/top and an interior remainder bound to obtain the
Whitney analytic inequality, then thread the Carleson budget to get the
final boundary pairing bound. -/
theorem local_pairing_bound_from_IBP_and_Carleson
  {Kξ lenI : ℝ}
  (hCar : ConcreteHalfPlaneCarleson Kξ)
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (α' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  -- Volume pairing bound (e.g. by L² Cauchy–Schwarz on σ|Q):
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (RS.boxEnergy gradU σ Q))
  -- Rectangle IBP decomposition with vanishing side/top and an interior bound:
  (Rside Rtop Rint : ℝ)
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hSideZero : Rside = 0) (hTopZero : Rtop = 0)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (RS.boxEnergy gradU σ Q))
  (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hEnergy_le : RS.boxEnergy gradU σ Q ≤ Kξ * lenI)
  : |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  classical
  -- Sqrt-form Carleson budget
  have hCarlSqrt :
      Real.sqrt (RS.boxEnergy gradU σ Q) ≤ Real.sqrt (Kξ * lenI) := by
    exact RS.sqrt_boxEnergy_bound_of_ConcreteHalfPlaneCarleson hCar gradU σ Q hEnergy_le
  -- Whitney analytic bound from Green+trace decomposition inputs
  have hAnalytic :
      |∫ t in I, ψ t * B t|
        ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (RS.boxEnergy gradU σ Q) := by
    -- If χ vanishes a.e. on side/top boundary pieces, we can derive Rside=Rtop=0
    -- via side_top_zero_from_ae_zero and then apply the Whitney packaging.
    -- Here we assume hSideZero, hTopZero are already available in inputs.
    exact RS.CRGreen_pairing_whitney_from_green_trace
      U W ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem
      hPairVol Rside Rtop Rint hEqDecomp hSideZero hTopZero hRintBound
  -- Push through the Carleson budget (monotonicity by nonnegativity)
  exact
    (le_trans hAnalytic
      (by exact mul_le_mul_of_nonneg_left hCarlSqrt hCψ_nonneg))

/-- Wiring adapter (IBP + a.e. side/top vanish): from a Carleson budget and
an IBP decomposition with side/top terms represented as boundary integrals
weighted by a cutoff `χ` that vanishes a.e. on those boundary pieces, deduce
the boundary pairing bound. -/
theorem local_pairing_bound_from_IBP_aeZero_and_Carleson
  {Kξ lenI : ℝ}
  (hCar : ConcreteHalfPlaneCarleson Kξ)
  (U : ℝ × ℝ → ℝ) (W ψ : ℝ → ℝ) (χ : ℝ × ℝ → ℝ)
  (I : Set ℝ) (α' : ℝ)
  (σ : Measure (ℝ × ℝ)) (Q : Set (ℝ × ℝ))
  (gradU : (ℝ × ℝ) → ℝ × ℝ) (gradChiVpsi : (ℝ × ℝ) → ℝ × ℝ)
  (B : ℝ → ℝ)
  (Cψ_pair Cψ_rem : ℝ)
  -- Volume pairing bound (e.g. by L² Cauchy–Schwarz on σ|Q):
  (hPairVol :
    |∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ|
      ≤ Cψ_pair * Real.sqrt (RS.boxEnergy gradU σ Q))
  -- Side/top boundary representations and a.e. vanish of χ on those pieces:
  (μ_side μ_top : Measure (ℝ × ℝ))
  (F_side F_top : (ℝ × ℝ) → ℝ)
  (Rside Rtop Rint : ℝ)
  (hSideDef : Rside = ∫ x, (χ x) * (F_side x) ∂μ_side)
  (hTopDef  : Rtop  = ∫ x, (χ x) * (F_top x)  ∂μ_top)
  (hSideAE  : (fun x => χ x) =ᵐ[μ_side] 0)
  (hTopAE   : (fun x => χ x) =ᵐ[μ_top] 0)
  -- IBP decomposition and interior remainder bound:
  (hEqDecomp :
    (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + Rside + Rtop + Rint)
  (hRintBound : |Rint| ≤ Cψ_rem * Real.sqrt (RS.boxEnergy gradU σ Q))
  (hCψ_nonneg : 0 ≤ Cψ_pair + Cψ_rem)
  (hEnergy_le : RS.boxEnergy gradU σ Q ≤ Kξ * lenI)
  : |∫ t in I, ψ t * B t| ≤ (Cψ_pair + Cψ_rem) * Real.sqrt (Kξ * lenI) := by
  classical
  -- a.e. vanish ⇒ side/top integrals vanish
  have hZero := RS.side_top_zero_from_ae_zero μ_side μ_top F_side F_top χ Rside Rtop hSideDef hTopDef hSideAE hTopAE
  have hSideZero : Rside = 0 := hZero.1
  have hTopZero  : Rtop  = 0 := hZero.2
  -- Use the IBP adapter with explicit zeros
  have hEqDecomp' : (∫ x in Q, (gradU x) ⋅ (gradChiVpsi x) ∂σ)
      = (∫ t in I, ψ t * B t) + 0 + 0 + Rint := by
    rw [hEqDecomp, hSideZero, hTopZero, add_zero, add_zero]
  exact local_pairing_bound_from_IBP_and_Carleson hCar U W ψ χ I α' σ Q gradU gradChiVpsi B Cψ_pair Cψ_rem
    hPairVol 0 0 Rint hEqDecomp' (by simp) (by simp) hRintBound hCψ_nonneg hEnergy_le

/-- Abstract half–plane Poisson transport: if `(P+)` holds on the boundary for `F`,
then `Re F ≥ 0` on the interior `Ω`. This is a statement‑level predicate that can
be discharged by the academic framework (Poisson/Smirnov theory on the half‑plane).
-/
def HasHalfPlanePoissonTransport (F : ℂ → ℂ) : Prop :=
  RH.Cert.PPlus F → ∀ z ∈ Ω, 0 ≤ (F z).re

/-- Predicate equivalence: RS transport on `Ω` is the same as the
cert-layer shape with `Re z > 1/2`. -/
lemma hasHalfPlanePoissonTransport_iff_certShape (F : ℂ → ℂ) :
    HasHalfPlanePoissonTransport F ↔
      (RH.Cert.PPlus F → ∀ z : ℂ, Complex.re z > (1/2 : ℝ) → 0 ≤ (F z).re) := by
  constructor
  · intro h hPPlus z hz
    have hzΩ : z ∈ Ω := by simpa [Ω, Set.mem_setOf_eq] using hz
    exact h hPPlus z hzΩ
  · intro h hPPlus z hzΩ
    have hz : Complex.re z > (1/2 : ℝ) := by simpa [Ω, Set.mem_setOf_eq] using hzΩ
    exact h hPPlus z hz

/-- Specialization to the pinch field `F := 2 · J_pinch det2 O`:
given (P+) on the boundary and a half–plane Poisson transport predicate for this `F`,
we obtain interior nonnegativity on `Ω`. -/
lemma hPoisson_from_PPlus
    (det2 O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re :=
  hTrans hPPlus

/-- Poisson step (interface form) for the pinch `J_pinch`:
from (P+) on the boundary for `F := 2 · J_pinch det2 O`, and a
half–plane Poisson interior passage for this `F`, obtain interior
nonnegativity of `Re F` on `Ω \ Z(ξ_ext)`.

Note: The actual Poisson transport is consumed through the hypothesis
`hPoisson`. This glue lemma simply restricts the interior positivity to
the off–zeros set where `J_pinch` is holomorphic. -/
lemma hRe_offXi_from_PPlus_via_Poisson
    (det2 O : ℂ → ℂ)
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPoisson : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re)
    : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}),
        0 ≤ ((2 : ℂ) * J_pinch det2 O z).re := by
  intro z hz
  exact hPoisson z hz.1

/-- Thread the Poisson step into the Cayley helper to get a Schur bound
for `Θ := Θ_pinch_of det2 O` on `Ω \ Z(ξ_ext)` from (P+) on the boundary
and an interior Poisson transport for `F := 2 · J_pinch det2 O`. -/
lemma Theta_Schur_offXi_from_PPlus_via_Poisson
    (det2 O : ℂ → ℂ)
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPoisson : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re)
    : IsSchurOn (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  have hRe_offXi :=
    hRe_offXi_from_PPlus_via_Poisson det2 O hPPlus hPoisson
  -- Apply the existing Cayley→Schur helper specialized off ξ_ext zeros
  simpa [Θ_pinch_of] using
    (Theta_Schur_of_Re_nonneg_on_Ω_offXi (J := J_pinch det2 O) hRe_offXi)

/-- (P+) together with half–plane Poisson transport for the pinch field
`F := 2 · J_pinch det2 O` yields a Schur bound for `Θ := Θ_pinch_of det2 O`
on `Ω \ Z(ξ_ext)` via the Cayley helper. -/
lemma Theta_Schur_offXi_from_PPlus_and_transport
    (det2 O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z))
    : IsSchurOn (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  have hPoisson := hPoisson_from_PPlus det2 O hTrans hPPlus
  exact Theta_Schur_offXi_from_PPlus_via_Poisson det2 O hPPlus hPoisson

/-- Certificate → (P+) → Poisson transport → Cayley ⇒ Schur off zeros.

Combines the Kξ budget (via the certificate interface) with the half–plane
transport predicate to produce a Schur bound for `Θ := Θ_pinch_of det2 O` on
`Ω \ Z(ξ_ext)`. -/
theorem Theta_Schur_offXi_from_certificate
    (α c : ℝ) (O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hKxi : RH.Cert.KxiWhitney.KxiBound α c)
    (hP : RH.Cert.PPlusFromCarleson_exists (fun z => (2 : ℂ) * J_pinch det2 O z))
    : IsSchurOn (Θ_pinch_of det2 O) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- (P+) from the Kξ certificate
  have hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z) :=
    PPlus_of_certificate α c (fun z => (2 : ℂ) * J_pinch det2 O z) hKxi hP
  -- Poisson transport → interior nonnegativity
  have hPoisson : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re :=
    hTrans hPPlus
  -- Cayley step off zeros
  exact Theta_Schur_offXi_from_PPlus_via_Poisson det2 O hPPlus hPoisson

/-- (P+) ⇒ Schur on `Ω \ {ξ_ext = 0}` via Cayley, assuming interior positivity.

This composes the Poisson transport (consumed as `hRe_interior`) with the Cayley
step to produce a Schur bound for `Θ := (2·J − 1)/(2·J + 1)` on `Ω \ {ξ_ext = 0}`.
The `(P+)` hypothesis is carried to reflect the intended provenance of
`hRe_interior` but is not re-used analytically here. -/
theorem Theta_Schur_offXi_from_PPlus
    (J : ℂ → ℂ)
    (hP : PPlus (fun z => (2 : ℂ) * J z))
    (hRe_interior : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((2 : ℂ) * J z).re)
    : IsSchurOn (Theta_of_J J) (Ω \ {z | riemannXi_ext z = 0}) := by
  -- Use the Cayley helper specialized to `Ω \ {ξ_ext=0}`.
  exact Theta_Schur_of_Re_nonneg_on_Ω_offXi J hRe_interior

/-! ### Abstract Poisson transport adapter

The following adapter reduces `HasHalfPlanePoissonTransport F` to a purely
structural representation of the interior real part of `F` by a positive
boundary–to–interior operator on boundary data. This keeps the logic lean and
mathlib‑only; an analytic instantiation can later provide such an operator. -/

/-- A boundary-to-interior operator on real boundary data over the half–plane. -/
def HalfPlanePoissonOp := (ℝ → ℝ) → ℂ → ℝ

/-- Structural representation for the interior real part of a fixed `F`:
1) positivity: a.e. boundary nonnegativity implies interior nonnegativity;
2) representation: `(Re F)(z)` is obtained by applying the operator to the
   boundary trace `t ↦ Re F(1/2+it)`. -/
def IsPoissonRepresentation (P : HalfPlanePoissonOp) (F : ℂ → ℂ) : Prop :=
  (∀ u : ℝ → ℝ, (∀ᵐ t : ℝ, 0 ≤ u t) → ∀ z ∈ Ω, 0 ≤ P u z) ∧
  (∀ z ∈ Ω, (F z).re = P (fun t : ℝ => (F (Complex.mk (1/2 : ℝ) t)).re) z)

/-- Existential packaging of a positive boundary–to–interior representation for `Re F`. -/
def HasPoissonRepresentation (F : ℂ → ℂ) : Prop :=
  ∃ P : HalfPlanePoissonOp, IsPoissonRepresentation P F

/-- If the interior real part of `F` is represented by a positive
boundary–to–interior operator acting on the boundary real trace of `F`, then
the half–plane Poisson transport predicate holds for `F`. -/
lemma hasHalfPlanePoissonTransport_of_poissonRepresentation
    (F : ℂ → ℂ) (P : HalfPlanePoissonOp)
    (hP : IsPoissonRepresentation P F) : HasHalfPlanePoissonTransport F := by
  have := hasHalfPlanePoissonTransport_iff_certShape F
  rcases hP with ⟨hPos, hRepr⟩
  refine (this.mpr ?_)
  intro hPPlus z hz
  have hb : ∀ᵐ t : ℝ, 0 ≤ (F (Complex.mk (1/2 : ℝ) t)).re := hPPlus
  have hpos := hPos (fun t => (F (Complex.mk (1/2 : ℝ) t)).re) hb z hz
  simpa [hRepr z hz] using hpos

/-- Transport from an existential representation. -/
lemma hasHalfPlanePoissonTransport_of_hasRep
    (F : ℂ → ℂ) (h : HasPoissonRepresentation F) : HasHalfPlanePoissonTransport F := by
  rcases h with ⟨P, hP⟩
  exact hasHalfPlanePoissonTransport_of_poissonRepresentation F P hP

/-- Specialization to the pinch field `F := 2 · J_pinch det2 O`. -/
lemma hasHalfPlanePoissonTransport_from_rep_Jpinch
    (O : ℂ → ℂ)
    (h : HasPoissonRepresentation (fun z => (2 : ℂ) * J_pinch det2 O z)) :
    HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z) := by
  exact hasHalfPlanePoissonTransport_of_hasRep _ h

/-- Convenience export: Poisson transport for the pinch field from a representation witness. -/
theorem hasHalfPlanePoissonTransport_pinch
    (O : ℂ → ℂ)
    (hRep : HasPoissonRepresentation (fun z => (2 : ℂ) * J_pinch RH.RS.det2 O z)) :
    HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch RH.RS.det2 O z) :=
  hasHalfPlanePoissonTransport_from_rep_Jpinch O hRep

/-- Interior nonnegativity on `Ω \\ Z(ξ_ext)` for the pinch field
`F := 2 · J_pinch det2 O`, obtained from a Kξ certificate via (P+) and
half–plane Poisson transport. -/
lemma hRe_offXi_from_certificate
    (α c : ℝ) (O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hKxi : RH.Cert.KxiWhitney.KxiBound α c)
    (hP : RH.Cert.PPlusFromCarleson_exists (fun z => (2 : ℂ) * J_pinch det2 O z))
    : ∀ z ∈ (Ω \ {z | riemannXi_ext z = 0}), 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re := by
  -- (P+) from the Kξ certificate
  have hPPlus : PPlus (fun z => (2 : ℂ) * J_pinch det2 O z) :=
    PPlus_of_certificate α c (fun z => (2 : ℂ) * J_pinch det2 O z) hKxi hP
  -- Poisson transport yields interior nonnegativity on Ω
  have hPoisson : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re := hTrans hPPlus
  -- Restrict to the off–zeros set
  exact hRe_offXi_from_PPlus_via_Poisson det2 O hPPlus hPoisson

lemma hPoisson_nonneg_on_Ω_from_Carleson_transport
    (O : ℂ → ℂ)
    (hTrans : HasHalfPlanePoissonTransport (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hP : RH.Cert.PPlusFromCarleson_exists (fun z => (2 : ℂ) * J_pinch det2 O z))
    (hKxi : ∃ Kξ : ℝ, 0 ≤ Kξ ∧ RH.Cert.ConcreteHalfPlaneCarleson Kξ)
    : ∀ z ∈ Ω, 0 ≤ ((2 : ℂ) * J_pinch det2 O z).re := by
  -- obtain (P+) from the concrete Carleson witness, then apply transport
  have hPPlus : RH.Cert.PPlus (fun z => (2 : ℂ) * J_pinch det2 O z) := hP hKxi
  exact hTrans hPPlus

/- B.1 (alternate): Transport lemma for `F := 2 · J_pinch det2 O`.

From boundary `PPlus F` (a.e. nonnegativity of `Re F` on the boundary),
pass through the Poisson/Herglotz route to obtain the Schur/Carleson
transport certificate, then conclude interior nonnegativity on `Ω`.
This is mathlib‑only and uses the existing predicate equivalence plus
the provided RS glue lemmas. -/
-- Removed alternate B.1 lemma to keep interface lean and avoid unused deps.

end RS
end RH
end
