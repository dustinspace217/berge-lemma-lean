# Berge's Lemma, formalized in Lean 4

A complete, machine-checked proof of **Berge's lemma** (1957) against
[mathlib](https://github.com/leanprover-community/mathlib4): a matching in a
simple graph is maximum if and only if it admits no augmenting path.

```
theorem SimpleGraph.Subgraph.IsMatching.isMaximumMatching_iff_forall_not_isAugmenting
    [Finite V] (hM : M.IsMatching) :
    M.IsMaximumMatching ↔ ∀ ⦃u v : V⦄ (p : G.Walk u v), ¬ p.IsAugmenting M
```

- Zero `sorry`.
- Axiom footprint of the theorem: `[propext, Classical.choice, Quot.sound]`,
  Lean's standard three, confirmed via `#print axioms`.
- Berge's theorem is tracked in mathlib's 1000-theorems list
  ([`docs/1000.yaml`](https://github.com/leanprover-community/mathlib4/blob/master/docs/1000.yaml),
  entry Q552367) with no formalization, and no Lean proof appeared in a
  search of mathlib master and its PR queue on 2026-08-16. An Isabelle/HOL
  formalization exists (Abdulaziz, arXiv:2412.20878), so this appears to be
  the first in Lean, not the first ever.
- Along the way the file proves
  `IsMatching.ncard_verts_eq_two_mul_ncard_edgeSet` (a matching covers
  exactly twice as many vertices as it has edges), which mathlib currently
  lacks.

## Provenance

Written by Claude (Fable 5, Anthropic), 2026-08-16. The hard direction's
proof strategy came from a consultation with GPT-5.6 (OpenAI); the Lean
code was written independently of that exchange. The mathematics is
kernel-checked; the code has not yet been reviewed by a Lean expert.

If you are a mathlib contributor and find this useful: take it. The code is
Apache 2.0, same as mathlib. Upstreaming would need reconciliation with
in-flight matching work (at the time of writing, mathlib PRs #32555,
#33032, #41217, #36274, #36406 touch maximum matchings, König's theorem,
and related counting lemmas).

## Verify it yourself (about 15 minutes, mostly downloads)

```
git clone --depth 1 https://github.com/leanprover-community/mathlib4.git
cd mathlib4
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
cp /path/to/this/repo/Berge.lean Mathlib/Combinatorics/SimpleGraph/Berge.lean
~/.elan/bin/lake exe cache get
~/.elan/bin/lake env lean Mathlib/Combinatorics/SimpleGraph/Berge.lean
```

A clean exit (no output, return code 0) is the kernel accepting every proof
in the file. To audit the axioms:

```
echo 'import Mathlib.Combinatorics.SimpleGraph.Berge
#print axioms SimpleGraph.Subgraph.IsMatching.isMaximumMatching_iff_forall_not_isAugmenting' > check.lean
~/.elan/bin/lake build Mathlib.Combinatorics.SimpleGraph.Berge
~/.elan/bin/lake env lean check.lean
```

Expected output: `depends on axioms: [propext, Classical.choice, Quot.sound]`.
If `sorryAx` appears in that list, some proof is incomplete; it does not.

Checked against mathlib master as of 2026-08-16 with Lean 4.34.0-rc1.
Upstream drift may eventually require small fixes.

## Definitions used

- `Subgraph.IsMaximumMatching M`: `M` is a matching and no matching of the
  same graph has more edges (`Set.ncard` on edge sets, under `[Finite V]`).
- `Walk.IsAugmenting p M`: `p` is a simple path between two distinct
  vertices, neither covered by `M`, whose edge set is alternating with
  respect to `M` (mathlib's `SimpleGraph.IsAlternating` on spanning
  coercions). For interior path vertices this forces the classical strict
  alternation; unsaturated endpoints force the first and last edges off `M`.

Both directions are proved constructively: an augmenting path toggles to a
strictly larger matching, and a strictly larger matching yields an
augmenting path by a connected-component argument on the union of the two
matchings.
