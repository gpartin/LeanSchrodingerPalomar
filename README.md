# LeanSchrodingerPalomar

Palomar submission wrapper for two narrow theorems extracted from
[LeanSchrodingerDerivation](https://github.com/gpartin/LeanSchrodingerDerivation).

For positive mass, the development proves an exact split of the positive
relativistic kinetic energy into the Schrödinger kinetic term and an explicit
remainder, then bounds the remainder by `p^4 / (8 m^3)`.

It does not derive the free-Dirac mass shell, an arbitrary-wavefunction
position-space PDE, the Born rule, or a complete quantum theory.

Build with:

```text
lake update
lake build
lake comparator
```
