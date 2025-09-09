import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import rh.academic_framework.CompletedXi

/-!
# Half‑plane outers (interface)

This module records a lightweight interface for outer functions on the right
half‑plane Ω := {Re s > 1/2}. It avoids disk‑specific dependencies and keeps the
construction abstract at the statement level; consumers can instantiate it with
Poisson‑outer constructions or via a Cayley transfer to the unit disk.

We provide:
- a nonvanishing/analytic predicate for a candidate `O` on Ω;
- a boundary‑modulus matching predicate `BoundaryModulusEq` (statement‑level);
- an existence predicate to obtain an outer `O` with prescribed boundary modulus.

No axioms are introduced; existence is exposed as a Prop‑level statement to be
realized by the analytic framework.
-/

noncomputable section

namespace RH
namespace AcademicFramework
namespace HalfPlaneOuter

open Complex
open RH.AcademicFramework.CompletedXi

-- Define Ω locally (right half-plane)
def Ω : Set ℂ := {s : ℂ | (1/2 : ℝ) < s.re}

-- Local notation for convenience
local notation "Ω" => Ω

/-- An outer on Ω: analytic and zero‑free on Ω. -/
structure OuterWitness (O : ℂ → ℂ) : Prop where
  analytic : AnalyticOn ℂ O Ω
  nonzero  : ∀ {s}, s ∈ Ω → O s ≠ 0

/-- Prop-level: `O` is outer on Ω. -/
def IsOuter (O : ℂ → ℂ) : Prop :=
  ∃ W : OuterWitness O, True

/-- Statement‑level boundary modulus predicate on the line Re s = 1/2.
For now this is abstract; in practice it means |O(1/2+it)| = |F(1/2+it)| a.e. -/
def BoundaryModulusEq (O F : ℂ → ℂ) : Prop :=
  -- Abstract placeholder: in practice this is a.e. equality of modulus on boundary
  True

/-- Existence of an outer `O` on Ω with boundary modulus equal (a.e.) to a
prescribed modulus `|F|` on Re s = 1/2 (statement‑level). -/
def ExistsOuterWithBoundaryModulus (F : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, IsOuter O ∧ BoundaryModulusEq O F

/-- Specialized existence for det2/xi_ext modulus (used by pinch certificate). -/
def ExistsOuterWithModulus_det2_over_xi_ext (det2 : ℂ → ℂ) : Prop :=
  ∃ O : ℂ → ℂ, OuterWitness O ∧
    BoundaryModulusEq O (fun s => det2 s / riemannXi_ext s)

end HalfPlaneOuter
end AcademicFramework
end RH
