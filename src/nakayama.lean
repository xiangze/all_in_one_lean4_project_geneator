/-
  Nakayama’s Lemma in Lean 4
  Requires: mathlib4 ≥ 0.1.0 (module `RingTheory.Nakayama`)
-/
import Mathlib.RingTheory.Nakayama  -- brings in all helper lemmas

open Ideal Submodule

variable {R M : Type*}
  [CommRing R]            -- base commutative ring
  [AddCommGroup M] [Module R M] -- module structure

/-!
### 1. Submodule form

If `N` is finitely generated, `I` lies in the Jacobson radical,
and `I • N = N`, then `N = ⊥`.
This is exactly
`Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` from mathlib.
-/
lemma nakayama_submodule
    {I : Ideal R} {N : Submodule R M}
    (hN : N.FG)                       -- `N` is finitely generated
    (hIN : N ≤ I • N)                 -- condition `I • N = N`
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) :
    N = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I N hN hIN hI

/-!
### 2. Classical module form

For a **finite** module `M` (Lean type-class `Module.Finite`),
if `I` is inside the Jacobson radical and
`I • M = M`, then `M = 0`.

We view `M` as the top submodule `⊤` and reuse the lemma above.
-/
lemma nakayama_module
    {I : Ideal R}
    [Module.Finite R M]                               -- `M` is f.g.
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R))
    (hIM : (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M)) :
    (⊤ : Submodule R M) = (⊥ : Submodule R M) := by
  -- `⊤` is finitely generated because `M` is finite:
  have h_fg : (⊤ : Submodule R M).FG := Module.Finite.fg_top
  -- Apply Nakayama for submodules:
  simpa using
    (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I (⊤ : Submodule R M)
      h_fg hIM hI)
