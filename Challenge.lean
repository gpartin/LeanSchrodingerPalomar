module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

public section

/-!
# Exact Schrödinger kinetic split and quartic remainder bound

This is an independent statement surface extracted from the conditional
nonrelativistic handoff in `LeanSchrodingerDerivation`. Given positive mass,
it states an exact decomposition of the positive relativistic kinetic energy
into the Schrödinger kinetic term plus an explicit correction, and bounds the
correction by a quartic expression.

The result does not derive the free-Dirac mass shell, an arbitrary-wavefunction
position-space PDE, the Born rule, or a complete quantum theory.
-/

namespace LeanSchrodingerPalomar

noncomputable section

def relativisticEnergy (mass momentum : ℝ) : ℝ :=
  Real.sqrt (mass ^ 2 + momentum ^ 2)

def restPhaseRemovedEnergy (mass momentum : ℝ) : ℝ :=
  relativisticEnergy mass momentum - mass

def schrodingerEnergy (mass momentum : ℝ) : ℝ :=
  momentum ^ 2 / (2 * mass)

def schrodingerRemainder (mass momentum : ℝ) : ℝ :=
  -(momentum ^ 4) /
    (2 * mass * (relativisticEnergy mass momentum + mass) ^ 2)

theorem exactSchrodingerKineticSplit
    (mass momentum : ℝ) (hMass : 0 < mass) :
    restPhaseRemovedEnergy mass momentum =
      schrodingerEnergy mass momentum + schrodingerRemainder mass momentum := by
  sorry

theorem schrodingerRemainderBound
    (mass momentum : ℝ) (hMass : 0 < mass) :
    |schrodingerRemainder mass momentum| ≤ momentum ^ 4 / (8 * mass ^ 3) := by
  sorry

end
end LeanSchrodingerPalomar
