/-
Copyright (c) 2026 the authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude (Fable 5, Anthropic). Hard-direction strategy from a
consultation with GPT-5.6 (OpenAI); the Lean proof is independent of that
exchange.

Not yet submitted to mathlib (Berge's theorem is Q552367 in docs/1000.yaml,
currently without a declaration). Reconcile naming and definitions with
in-flight maximum-matching PRs (e.g. #32555) before any upstream attempt.
-/
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Berge's lemma

A matching `M` in a simple graph `G` is maximum (has the largest possible
number of edges) if and only if there is no `M`-augmenting path: a path
between two distinct `M`-unsaturated vertices whose edges alternate between
edges outside `M` and edges of `M`.

## Design notes

* Matchings are `SimpleGraph.Subgraph`s satisfying `Subgraph.IsMatching`,
  matching the existing mathlib idiom (`Matching.lean`, `Tutte.lean`).
* Alternation reuses `SimpleGraph.IsAlternating` on spanning coercions —
  the same device `Matching.lean` uses for perfect-matching symmDiff work.
  For a path `p` with BOTH endpoints outside `M.verts`, unsaturation of the
  endpoints forces the first and last edges of `p` off `M` (an `M`-edge at
  an endpoint would put that endpoint in `M.verts`); alternation then fixes
  the interior pattern, so the classical "starts and ends with non-M edges"
  is implied rather than restated.
* Maximality is by edge count via `Set.ncard`, under `[Finite V]`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {M : Subgraph G}

open scoped symmDiff

/-- A matching `M` is maximum if no matching of `G` has more edges. -/
def Subgraph.IsMaximumMatching [Finite V] (M : Subgraph G) : Prop :=
  M.IsMatching ∧ ∀ M' : Subgraph G, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard

/-- An `M`-augmenting path: a path between two distinct vertices neither of
which lies in `M.verts` (for a matching `M`, exactly the `M`-saturated
vertices), whose edge set alternates with respect to `M`.
Unsaturated endpoints + alternation make the path start and end with
non-`M` edges and have odd length, in the classical formulation. -/
def Walk.IsAugmenting {u v : V} (p : G.Walk u v) (M : Subgraph G) : Prop :=
  p.IsPath ∧ u ≠ v ∧ u ∉ M.verts ∧ v ∉ M.verts ∧
    p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe

/-! ### Counting infrastructure -/

namespace Subgraph

/-- Distinct edges of a matching share no vertex. -/
lemma IsMatching.notMem_of_mem_of_ne (hM : M.IsMatching) {e f : Sym2 V}
    (he : e ∈ M.edgeSet) (hf : f ∈ M.edgeSet) (hne : e ≠ f) {x : V}
    (hxe : x ∈ e) : x ∉ f := by
  induction e with | _ a b =>
  induction f with | _ c d =>
  rw [Subgraph.mem_edgeSet] at he hf
  rw [Sym2.mem_iff] at hxe
  intro hxf
  rw [Sym2.mem_iff] at hxf
  apply hne
  rcases hxe with rfl | rfl <;> rcases hxf with rfl | rfl
  · rw [hM.eq_of_adj_left he hf]
  · rw [hM.eq_of_adj_left he hf.symm, Sym2.eq_swap]
  · rw [hM.eq_of_adj_left he.symm hf, Sym2.eq_swap]
  · rw [hM.eq_of_adj_left he.symm hf.symm]

/-- A matching covers exactly twice as many vertices as it has edges. -/
lemma IsMatching.ncard_verts_eq_two_mul_ncard_edgeSet [Finite V]
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  rw [hM.verts_eq_biUnion_edgeSet,
    Set.Finite.ncard_biUnion M.edgeSet.toFinite (fun _ _ => Set.toFinite _)
      (fun e he f hf hef => Set.disjoint_left.mpr
        fun x hx => hM.notMem_of_mem_of_ne he hf hef hx)]
  have h2 : ∀ e ∈ M.edgeSet, (e : Set V).ncard = 2 := by
    intro e he
    induction e with | _ a b =>
    rw [Subgraph.mem_edgeSet] at he
    have hab : a ≠ b := (M.adj_sub he).ne
    have hset : (s(a, b) : Set V) = ({a, b} : Set V) := by
      ext x
      simp
    rw [hset, Set.ncard_pair hab]
  rw [finsum_mem_congr rfl h2,
    finsum_mem_congr rfl (fun i (_ : i ∈ M.edgeSet) => one_add_one_eq_two.symm),
    finsum_mem_add_distrib M.edgeSet.toFinite, finsum_one, two_mul]

end Subgraph

/-! ### The toggle: an augmenting path yields a strictly larger matching -/

/-- The symmetric difference of a matching with an augmenting path, as a
subgraph of `G`: vertices are the covered ones. -/
private def augSymmDiff (M : Subgraph G) {u v : V} (p : G.Walk u v) : Subgraph G where
  verts := {w | ((M.spanningCoe ∆ p.toSubgraph.spanningCoe).neighborSet w).Nonempty}
  Adj := (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj
  adj_sub := by
    intro w x h
    rcases (by simpa [symmDiff_def] using h : _ ∨ _) with ⟨h', _⟩ | ⟨h', _⟩
    · exact M.adj_sub h'
    · exact p.toSubgraph.adj_sub h'
  edge_vert := fun h => ⟨_, h⟩
  symm := (M.spanningCoe ∆ p.toSubgraph.spanningCoe).symm

/-- Adjacency in the toggled graph: an edge survives iff it is a matching
edge off the path or a path edge off the matching. -/
private lemma augSymmDiff_adj {u v w x : V} {p : G.Walk u v} :
    (augSymmDiff M p).Adj w x ↔
      (M.Adj w x ∧ s(w, x) ∉ p.edges) ∨ (s(w, x) ∈ p.edges ∧ ¬M.Adj w x) := by
  show (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj w x ↔ _
  simp [symmDiff_def, Walk.adj_toSubgraph_iff_mem_edges]

/-- Off the path, the toggled graph agrees with the matching. -/
private lemma augSymmDiff_adj_of_notMem_support {u v w x : V} {p : G.Walk u v}
    (hw : w ∉ p.support) : (augSymmDiff M p).Adj w x ↔ M.Adj w x := by
  rw [augSymmDiff_adj]
  have hnp : s(w, x) ∉ p.edges := fun he =>
    hw (Walk.fst_mem_support_of_mem_edges p he)
  tauto

/-- At the path's start, the toggled graph's unique neighbor is `p.snd`. -/
private lemma augSymmDiff_adj_startpoint {u v x : V} {p : G.Walk u v}
    (hp : p.IsAugmenting M) :
    (augSymmDiff M p).Adj u x ↔ x = p.snd := by
  obtain ⟨hpath, hne, hu, hv, halt⟩ := hp
  have hnnil : ¬p.Nil := fun hnil => hne (Walk.Nil.eq hnil)
  have hMu : ∀ y, ¬M.Adj u y := fun y hy => hu (M.edge_vert hy)
  rw [augSymmDiff_adj]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd h (hMu x)
    · have hadj : p.toSubgraph.Adj u x := Walk.adj_toSubgraph_iff_mem_edges.mpr h
      have hmem : x ∈ p.toSubgraph.neighborSet u := hadj
      rw [hpath.neighborSet_toSubgraph_startpoint hnnil] at hmem
      exact hmem
  · rintro rfl
    exact Or.inr ⟨Walk.adj_toSubgraph_iff_mem_edges.mp (p.toSubgraph_adj_snd hnnil),
      hMu p.snd⟩

/-- Reversal preserves being augmenting. -/
private lemma Walk.IsAugmenting.reverse {u v : V} {p : G.Walk u v}
    (hp : p.IsAugmenting M) : p.reverse.IsAugmenting M := by
  obtain ⟨hpath, hne, hu, hv, halt⟩ := hp
  exact ⟨hpath.reverse, hne.symm, hv, hu, by rwa [Walk.toSubgraph_reverse]⟩

/-- The toggled graph is unchanged by path reversal. -/
private lemma augSymmDiff_reverse_adj {u v w x : V} {p : G.Walk u v} :
    (augSymmDiff M p.reverse).Adj w x ↔ (augSymmDiff M p).Adj w x := by
  show (M.spanningCoe ∆ p.reverse.toSubgraph.spanningCoe).Adj w x ↔
    (M.spanningCoe ∆ p.toSubgraph.spanningCoe).Adj w x
  rw [Walk.toSubgraph_reverse]

/-- At the path's end, the toggled graph's unique neighbor is the
penultimate vertex. -/
private lemma augSymmDiff_adj_endpoint {u v x : V} {p : G.Walk u v}
    (hp : p.IsAugmenting M) :
    (augSymmDiff M p).Adj v x ↔ x = p.penultimate := by
  rw [← augSymmDiff_reverse_adj, augSymmDiff_adj_startpoint hp.reverse,
    Walk.snd_reverse]

/-- At an internal path vertex, the vertex is matched and has a unique
toggled neighbor. -/
private lemma augSymmDiff_internal {u v w : V} {p : G.Walk u v}
    (hM : M.IsMatching) (hp : p.IsAugmenting M) (hw : w ∈ p.support)
    (hwu : w ≠ u) (hwv : w ≠ v) :
    w ∈ M.verts ∧ ∃! x, (augSymmDiff M p).Adj w x := by
  obtain ⟨hpath, hne, hu, hv, halt⟩ := hp
  obtain ⟨i, hgv, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hw
  subst hgv
  have hi0 : i ≠ 0 := fun h => hwu (by simp [h])
  have hilt : i < p.length := by
    rcases lt_or_eq_of_le hile with h | h
    · exact h
    · exact absurd (by simp [h]) hwv
  -- the two path neighbors
  have hnb := hpath.neighborSet_toSubgraph_internal hi0 hilt
  have hadjPrev : p.toSubgraph.Adj (p.getVert i) (p.getVert (i - 1)) := by
    have := (show i - 1 + 1 = i by lia) ▸
      p.toSubgraph_adj_getVert (show i - 1 < p.length by lia)
    exact this.symm
  have hadjNext : p.toSubgraph.Adj (p.getVert i) (p.getVert (i + 1)) :=
    p.toSubgraph_adj_getVert hilt
  have hnePN : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have := hpath.getVert_injOn (by rw [Set.mem_ofPred_eq]; lia)
      (by rw [Set.mem_ofPred_eq]; lia) h
    lia
  -- alternation: exactly one of the two path edges is a matching edge
  have hiff : M.Adj (p.getVert i) (p.getVert (i - 1)) ↔
      ¬M.Adj (p.getVert i) (p.getVert (i + 1)) := by
    have := halt hnePN (by simpa using hadjPrev) (by simpa using hadjNext)
    simpa using this
  -- the core argument, symmetric in the two neighbors
  have core : ∀ y z : V, y ≠ z →
      p.toSubgraph.Adj (p.getVert i) y → p.toSubgraph.Adj (p.getVert i) z →
      p.toSubgraph.neighborSet (p.getVert i) = {y, z} →
      M.Adj (p.getVert i) y → ¬M.Adj (p.getVert i) z →
      p.getVert i ∈ M.verts ∧ ∃! x, (augSymmDiff M p).Adj (p.getVert i) x := by
    intro y z hyz hpy hpz hnbs hMy hMz
    refine ⟨M.edge_vert hMy, z, ?_, ?_⟩
    · exact augSymmDiff_adj.mpr (Or.inr
        ⟨Walk.adj_toSubgraph_iff_mem_edges.mp hpz, hMz⟩)
    · intro x hx
      rcases augSymmDiff_adj.mp hx with ⟨hMx, hnpx⟩ | ⟨hpx, hMx⟩
      · exact absurd (Walk.adj_toSubgraph_iff_mem_edges.mp
          ((hM.eq_of_adj_left hMx hMy) ▸ hpy)) hnpx
      · have hxmem : x ∈ p.toSubgraph.neighborSet (p.getVert i) :=
          Walk.adj_toSubgraph_iff_mem_edges.mpr hpx
        rw [hnbs] at hxmem
        rcases hxmem with rfl | rfl
        · exact absurd hMy hMx
        · rfl
  by_cases hMa : M.Adj (p.getVert i) (p.getVert (i - 1))
  · exact core _ _ hnePN hadjPrev hadjNext hnb hMa (hiff.mp hMa)
  · have hMb : M.Adj (p.getVert i) (p.getVert (i + 1)) := by
      by_contra hc
      exact hMa (hiff.mpr hc)
    have hnb' : p.toSubgraph.neighborSet (p.getVert i) =
        {p.getVert (i + 1), p.getVert (i - 1)} := by
      rw [hnb, Set.pair_comm]
    exact core _ _ hnePN.symm hadjNext hadjPrev hnb' hMb hMa

/-- Toggling a matching along an augmenting path produces a matching. -/
lemma Walk.IsAugmenting.isMatching_augSymmDiff {u v : V}
    {p : G.Walk u v} (hM : M.IsMatching) (hp : p.IsAugmenting M) :
    (augSymmDiff M p).IsMatching := by
  classical
  intro w hw
  obtain ⟨x0, hx0⟩ := hw
  by_cases hws : w ∈ p.support
  · by_cases hwu : w = u
    · subst hwu
      exact ⟨p.snd, (augSymmDiff_adj_startpoint hp).mpr rfl,
        fun y hy => (augSymmDiff_adj_startpoint hp).mp hy⟩
    · by_cases hwv : w = v
      · subst hwv
        exact ⟨p.penultimate, (augSymmDiff_adj_endpoint hp).mpr rfl,
          fun y hy => (augSymmDiff_adj_endpoint hp).mp hy⟩
      · exact (augSymmDiff_internal hM hp hws hwu hwv).2
  · have hx0' : M.Adj w x0 := (augSymmDiff_adj_of_notMem_support hws).mp hx0
    obtain ⟨y, hy, hyu⟩ := hM (M.edge_vert hx0')
    exact ⟨y, (augSymmDiff_adj_of_notMem_support hws).mpr hy,
      fun z hz => hyu z ((augSymmDiff_adj_of_notMem_support hws).mp hz)⟩

/-- The toggled matching covers the old vertices plus both endpoints. -/
lemma Walk.IsAugmenting.verts_augSymmDiff {u v : V}
    {p : G.Walk u v} (hM : M.IsMatching) (hp : p.IsAugmenting M) :
    (augSymmDiff M p).verts = M.verts ∪ {u, v} := by
  classical
  ext w
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x0, hx0⟩
    by_cases hws : w ∈ p.support
    · by_cases hwu : w = u
      · exact Or.inr (Or.inl hwu)
      · by_cases hwv : w = v
        · exact Or.inr (Or.inr hwv)
        · exact Or.inl (augSymmDiff_internal hM hp hws hwu hwv).1
    · exact Or.inl (M.edge_vert ((augSymmDiff_adj_of_notMem_support hws).mp hx0))
  · rintro (hwM | rfl | rfl)
    · by_cases hws : w ∈ p.support
      · have hwu : w ≠ u := fun h => hp.2.2.1 (h ▸ hwM)
        have hwv : w ≠ v := fun h => hp.2.2.2.1 (h ▸ hwM)
        obtain ⟨-, x, hx, -⟩ := augSymmDiff_internal hM hp hws hwu hwv
        exact ⟨x, hx⟩
      · obtain ⟨x, hx, -⟩ := hM hwM
        exact ⟨x, (augSymmDiff_adj_of_notMem_support hws).mpr hx⟩
    · exact ⟨p.snd, (augSymmDiff_adj_startpoint hp).mpr rfl⟩
    · exact ⟨p.penultimate, (augSymmDiff_adj_endpoint hp).mpr rfl⟩

/-! ### The hard direction: a larger matching forces an augmenting path

Proof route (implemented below): work in the union `H = M ⊔ M'`, which is
alternating with respect to `M` (`isAlternating_sup` — each matching
contributes at most one edge per vertex). Restricting either matching to a
connected component of `H` is still a matching, so each component contains
an even number of `M`-vertices and of `M'`-vertices; since `M'` covers more
vertices overall, pigeonhole gives a component with at least two more
`M'`-vertices than `M`-vertices, hence two distinct `M`-unsaturated
vertices. Any path between them inside `H` inherits alternation by
monotonicity, and mapping it into `G` yields an augmenting path. -/

/-- The union of two matchings is alternating with respect to the first:
at any vertex, each matching contributes at most one incident edge, so two
distinct union-edges at a vertex are one edge of each — exactly one lies in
`M`. (Hard-direction strategy credit: see the file header.) -/
private lemma isAlternating_sup {M' : Subgraph G}
    (hM : M.IsMatching) (hM' : M'.IsMatching) :
    (M.spanningCoe ⊔ M'.spanningCoe).IsAlternating M.spanningCoe := by
  intro x y z hyz hxy hxz
  simp only [sup_adj, Subgraph.spanningCoe_adj] at hxy hxz ⊢
  constructor
  · intro hMy hMz
    exact hyz (hM.eq_of_adj_left hMy hMz)
  · intro hMz
    rcases hxy with hMy | hM'y
    · exact hMy
    · rcases hxz with hMz' | hM'z
      · exact absurd hMz' hMz
      · exact absurd (hM'.eq_of_adj_left hM'y hM'z) hyz

/-- A matching restricted to a connected component of any graph containing
it is still a matching: partners cannot cross component boundaries. -/
private lemma Subgraph.IsMatching.induce_component_of_le {H : SimpleGraph V}
    (hM : M.IsMatching) (hle : M.spanningCoe ≤ H) (c : H.ConnectedComponent) :
    (M.induce (M.verts ∩ c.supp)).IsMatching := by
  intro v hv
  obtain ⟨hv, hvc⟩ := hv
  obtain ⟨w, hvw, hw⟩ := hM hv
  have hHvw : H.Adj v w := hle (by simpa using hvw)
  have hwc : w ∈ c.supp := c.mem_supp_of_adj_mem_supp hvc hHvw
  refine ⟨w, ⟨⟨hv, hvc⟩, ⟨M.edge_vert hvw.symm, hwc⟩, hvw⟩, ?_⟩
  rintro y ⟨-, -, hy⟩
  exact hw y hy

/-- The vertex count of a matching inside any component of a containing
graph is even. -/
private lemma even_ncard_verts_inter_supp [Finite V] {H : SimpleGraph V}
    (hM : M.IsMatching) (hle : M.spanningCoe ≤ H) (c : H.ConnectedComponent) :
    Even (M.verts ∩ c.supp).ncard := by
  have h := (hM.induce_component_of_le hle c).ncard_verts_eq_two_mul_ncard_edgeSet
  rw [Subgraph.induce_verts] at h
  exact ⟨_, by rw [h]; ring⟩

/-- Pigeonhole over connected components of the union: a strictly larger
matching covers strictly more vertices inside some component. -/
private lemma exists_component_ncard_lt [Finite V] {M' : Subgraph G}
    (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hlt : M.edgeSet.ncard < M'.edgeSet.ncard) :
    ∃ c : (M.spanningCoe ⊔ M'.spanningCoe).ConnectedComponent,
      (M.verts ∩ c.supp).ncard < (M'.verts ∩ c.supp).ncard := by
  set H := M.spanningCoe ⊔ M'.spanningCoe with hH
  by_contra hc
  push Not at hc
  have hsum : ∀ N : Subgraph G, N.verts.ncard =
      ∑ᶠ c : H.ConnectedComponent, (N.verts ∩ c.supp).ncard := by
    intro N
    have hcover : N.verts = ⋃ c : H.ConnectedComponent, (N.verts ∩ c.supp) := by
      rw [← Set.inter_iUnion, iUnion_connectedComponentSupp, Set.inter_univ]
    calc N.verts.ncard
        = (⋃ c : H.ConnectedComponent, (N.verts ∩ c.supp)).ncard := by rw [← hcover]
      _ = ∑ᶠ c : H.ConnectedComponent, (N.verts ∩ c.supp).ncard :=
        Set.ncard_iUnion_of_finite (fun _ => Set.toFinite _)
          (fun c c' hcc' => ((H.pairwise_disjoint_supp_connectedComponent hcc').mono
            Set.inter_subset_right Set.inter_subset_right))
  have hle : M'.verts.ncard ≤ M.verts.ncard := by
    rw [hsum M, hsum M']
    exact finsum_le_finsum' (Set.toFinite _) (Set.toFinite _) fun c => hc c
  rw [hM.ncard_verts_eq_two_mul_ncard_edgeSet,
    hM'.ncard_verts_eq_two_mul_ncard_edgeSet] at hle
  lia

/-- A strictly larger matching forces an augmenting path (Berge, hard
direction). Inside the union `M ⊔ M'` — which is alternating with respect
to `M` — some component covers at least two more `M'`-vertices than
`M`-vertices (pigeonhole + evenness), hence contains two distinct
`M`-unsaturated vertices; any path between them in the union is an
augmenting path. -/
private lemma exists_isAugmenting_of_ncard_lt [Finite V] {M' : Subgraph G}
    (hM : M.IsMatching) (hM' : M'.IsMatching)
    (hlt : M.edgeSet.ncard < M'.edgeSet.ncard) :
    ∃ (a b : V) (p : G.Walk a b), p.IsAugmenting M := by
  classical
  have hHG : M.spanningCoe ⊔ M'.spanningCoe ≤ G :=
    sup_le M.spanningCoe_le M'.spanningCoe_le
  obtain ⟨c, hclt⟩ := exists_component_ncard_lt hM hM' hlt
  set s := M.verts ∩ c.supp with hs
  set t := M'.verts ∩ c.supp with ht
  have hsEven : Even s.ncard := even_ncard_verts_inter_supp hM le_sup_left c
  have htEven : Even t.ncard := even_ncard_verts_inter_supp hM' le_sup_right c
  have hgap : s.ncard + 2 ≤ t.ncard := by
    obtain ⟨a, ha⟩ := hsEven
    obtain ⟨b, hb⟩ := htEven
    lia
  have hdecomp : (t ∩ s).ncard + (t \ s).ncard = t.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard t s
  have hint : (t ∩ s).ncard ≤ s.ncard :=
    Set.ncard_le_ncard Set.inter_subset_right s.toFinite
  have htwo : 1 < (t \ s).ncard := by lia
  obtain ⟨u, hu, v, hv, huv⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp htwo
  have huC : u ∈ c.supp := hu.1.2
  have hvC : v ∈ c.supp := hv.1.2
  have huM : u ∉ M.verts := fun hum => hu.2 ⟨hum, huC⟩
  have hvM : v ∉ M.verts := fun hvm => hv.2 ⟨hvm, hvC⟩
  have hreach : (M.spanningCoe ⊔ M'.spanningCoe).Reachable u v :=
    ConnectedComponent.exact
      ((ConnectedComponent.mem_supp_iff _ _).mp huC |>.trans
        ((ConnectedComponent.mem_supp_iff _ _).mp hvC).symm)
  obtain ⟨w⟩ := hreach
  set q : (M.spanningCoe ⊔ M'.spanningCoe).Walk u v := w.toPath.1 with hqdef
  have hq : q.IsPath := w.toPath.2
  set p : G.Walk u v := q.mapLe hHG with hpdef
  have hqalt : q.toSubgraph.spanningCoe.IsAlternating M.spanningCoe :=
    (isAlternating_sup hM hM').mono q.toSubgraph.spanningCoe_le
  have hpalt : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe := by
    intro x y z hyz hxy hxz
    apply hqalt hyz
    · simpa [p, Walk.adj_toSubgraph_mapLe] using hxy
    · simpa [p, Walk.adj_toSubgraph_mapLe] using hxz
  exact ⟨u, v, p, hq.mapLe hHG, huv, huM, hvM, hpalt⟩

/-- **Berge's lemma** (1957): a matching is maximum iff it admits no
augmenting path. -/
theorem Subgraph.IsMatching.isMaximumMatching_iff_forall_not_isAugmenting
    [Finite V] (hM : M.IsMatching) :
    M.IsMaximumMatching ↔ ∀ ⦃u v : V⦄ (p : G.Walk u v), ¬ p.IsAugmenting M := by
  constructor
  · -- maximum → no augmenting path: an augmenting path toggles to a
    -- strictly larger matching (symmDiff with the path's edges).
    rintro ⟨-, hmax⟩ a b p hp
    have hN := hp.isMatching_augSymmDiff hM
    have hverts := hp.verts_augSymmDiff hM
    have hnu : a ∉ M.verts := hp.2.2.1
    have hnv : b ∉ M.verts := hp.2.2.2.1
    have hab : a ≠ b := hp.2.1
    have hdisj : Disjoint M.verts ({a, b} : Set V) := by
      rw [Set.disjoint_right]
      rintro x (rfl | rfl) hx
      · exact hnu hx
      · exact hnv hx
    have hcard : (M.verts ∪ ({a, b} : Set V)).ncard = M.verts.ncard + 2 := by
      rw [Set.ncard_union_eq hdisj M.verts.toFinite (Set.toFinite _),
        Set.ncard_pair hab]
    have h1 := hN.ncard_verts_eq_two_mul_ncard_edgeSet
    have h2 := hM.ncard_verts_eq_two_mul_ncard_edgeSet
    rw [hverts, hcard, h2] at h1
    have := hmax _ hN
    lia
  · -- no augmenting path → maximum: contrapositive; a larger matching M'
    -- gives a component of the union M ⊔ M' containing two M-unsaturated
    -- vertices, and any path between them in the union is M-augmenting.
    intro hnope
    refine ⟨hM, fun M' hM' => ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, p, hp⟩ := exists_isAugmenting_of_ncard_lt hM hM' hlt
    exact hnope p hp

end SimpleGraph
