"""Pure-stdlib zero-float exact-Q primal-dual 2ECSS engine.
Implements Danciu & Ibrahimpur (arXiv:2611.32924, Nov 25, 2026)
"Better-than-3 Approximation for 2ECSS Using the Primal-Dual Method"
using exact fractions.Fraction arithmetic (zero floating-point operations).

Author: Lluis Eriksson
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Set, Tuple


def is_connected(n: int, edges: Sequence[Tuple[int, int]]) -> bool:
    if n <= 1:
        return True
    adj: List[List[int]] = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    seen = {0}
    stack = [0]
    while stack:
        cur = stack.pop()
        for nxt in adj[cur]:
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return len(seen) == n


def is_2_edge_connected(n: int, edges: Sequence[Tuple[int, int]]) -> bool:
    """Exact 2-edge-connectivity check: graph is connected and remains connected after removing any single edge."""
    if n <= 1:
        return True
    if not is_connected(n, edges):
        return False
    m = len(edges)
    for skip in range(m):
        sub = [edges[i] for i in range(m) if i != skip]
        if not is_connected(n, sub):
            return False
    return True


def is_forest_and_decompose(
    n: int,
    forest_edges: Sequence[Tuple[int, int]],
) -> Tuple[bool, List[int], List[int], List[List[int]]]:
    """Check if (V, forest_edges) is a forest and return (ok, leaves L, isolated I, nontrivial components C)."""
    parent = list(range(n))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    deg = [0] * n
    for u, v in forest_edges:
        if u == v or not (0 <= u < n and 0 <= v < n):
            return False, [], [], []
        ru, rv = find(u), find(v)
        if ru == rv:
            return False, [], [], []  # cycle -> not a forest!
        parent[ru] = rv
        deg[u] += 1
        deg[v] += 1

    comps_map: Dict[int, List[int]] = {}
    for v in range(n):
        comps_map.setdefault(find(v), []).append(v)

    leaves = [v for v in range(n) if deg[v] == 1]
    isolated = [v for v in range(n) if deg[v] == 0]
    nontrivial = [sorted(vs) for vs in comps_map.values() if len(vs) >= 2]
    nontrivial.sort()
    return True, leaves, isolated, nontrivial


def approx_ratio_exact(beta: Fraction) -> Tuple[Fraction, Fraction, Fraction]:
    """Return (branch1 = 2 + 2*beta, branch2 = 2 + 1/(1 + beta), alpha = max(branch1, branch2))."""
    b1 = Fraction(2, 1) + 2 * beta
    b2 = Fraction(2, 1) + Fraction(1, 1) / (Fraction(1, 1) + beta)
    return b1, b2, (b1 if b1 >= b2 else b2)


def run_primal_dual_2ecss_exact(
    n: int,
    edges: Sequence[Tuple[int, int, Fraction]],
    beta: Fraction,
) -> Dict:
    """Execute Danciu & Ibrahimpur's single-phase non-uniform-rate primal-dual 2ECSS algorithm exactly over Q.
    Input: n vertices (0..n-1), multigraph edges [(u, v, cost)], rational beta in [0, 1/2].
    Returns exact primal solution F, exact dual (y, z), weak-duality values, and full per-iteration trace.
    """
    m_edges = len(edges)
    # Contracted supernodes: list of frozensets of original vertices
    nodes: List[Set[int]] = [{v} for v in range(n)]
    # Forest edges between current supernode indices (pairs of supernode ids)
    h_edges: List[Tuple[int, int]] = []
    purchased: List[int] = []
    purchased_set: Set[int] = set()
    # Dual variables y[S_tuple] -> Fraction > 0
    y_duals: Dict[Tuple[int, ...], Fraction] = {}
    # Cumulative dual load on each edge e
    loads: List[Fraction] = [Fraction(0, 1)] * m_edges
    # z_e variables (excess dual load on purchased/tight edges)
    z_duals: List[Fraction] = [Fraction(0, 1)] * m_edges

    def vertex_to_node(v: int) -> int:
        for idx, s in enumerate(nodes):
            if v in s:
                return idx
        raise RuntimeError("Vertex lost")

    def node_components() -> Tuple[List[int], List[int], List[List[int]], Dict[int, int]]:
        k = len(nodes)
        adj: List[List[int]] = [[] for _ in range(k)]
        for a, b in h_edges:
            adj[a].append(b)
            adj[b].append(a)
        deg = [len(adj[i]) for i in range(k)]
        leaves = [i for i in range(k) if deg[i] == 1]
        isolated = [i for i in range(k) if deg[i] == 0]
        seen = [False] * k
        comps: List[List[int]] = []
        node_to_comp: Dict[int, int] = {}
        for i in range(k):
            if not seen[i]:
                comp = []
                stack = [i]
                seen[i] = True
                while stack:
                    cur = stack.pop()
                    comp.append(cur)
                    for nxt in adj[cur]:
                        if not seen[nxt]:
                            seen[nxt] = True
                            stack.append(nxt)
                cid = len(comps)
                for u in comp:
                    node_to_comp[u] = cid
                comps.append(sorted(comp))
        return leaves, isolated, comps, node_to_comp

    iter_snapshots: List[Dict] = []

    while len(nodes) > 1:
        leaves, isolated, comps, node_to_comp = node_components()
        disconnected = len(comps) >= 2
        nontrivial_cids = {cid for cid, c in enumerate(comps) if len(c) >= 2}
        active_nodes = set(leaves) | set(isolated)

        # Compute dual growth rate w_e for every relevant edge (unpurchased & joining distinct supernodes)
        best_delta = None
        best_edge = None
        edge_rates: Dict[int, Fraction] = {}
        for eid, (u, v, cost) in enumerate(edges):
            if eid in purchased_set:
                continue
            nu, nv = vertex_to_node(u), vertex_to_node(v)
            if nu == nv:
                continue
            rate = Fraction(0, 1)
            if nu in active_nodes:
                rate += Fraction(1, 1)
            if nv in active_nodes:
                rate += Fraction(1, 1)
            if disconnected:
                cu, cv = node_to_comp[nu], node_to_comp[nv]
                if cu != cv:
                    if cu in nontrivial_cids:
                        rate += beta
                    if cv in nontrivial_cids:
                        rate += beta
            if rate > 0:
                edge_rates[eid] = rate
                rem_cost = cost - (loads[eid] - z_duals[eid])
                delta = rem_cost / rate
                if best_delta is None or delta < best_delta:
                    best_delta = delta
                    best_edge = eid

        assert best_delta is not None and best_edge is not None and best_delta >= 0

        # Active cuts grown in this iteration
        active_cuts: List[Tuple[Tuple[int, ...], Fraction]] = []
        for nd in sorted(active_nodes):
            S = tuple(sorted(nodes[nd]))
            active_cuts.append((S, Fraction(1, 1)))
        if disconnected:
            for cid in sorted(nontrivial_cids):
                S = tuple(sorted(v for nd in comps[cid] for v in nodes[nd]))
                if beta > 0:
                    active_cuts.append((S, beta))

        # Apply dual growth Delta_t
        if best_delta > 0:
            for S, r in active_cuts:
                y_duals[S] = y_duals.get(S, Fraction(0, 1)) + r * best_delta
            for eid, (u, v, cost) in enumerate(edges):
                # Increase load by sum of grown cuts crossing e
                inc = Fraction(0, 1)
                for S, r in active_cuts:
                    Sset = set(S)
                    if (u in Sset) != (v in Sset):
                        inc += r * best_delta
                loads[eid] += inc
                if loads[eid] - z_duals[eid] > cost:
                    z_duals[eid] = loads[eid] - cost

        # Snapshot pre-purchase state for Lemma 3.2/3.3/3.4 telescoping trace
        iter_snapshots.append({
            "num_nodes": len(nodes),
            "kappa": len(comps),
            "L": len(leaves),
            "I": len(isolated),
            "C": len(nontrivial_cids),
            "disconnected": disconnected,
            "delta": best_delta,
            "active_cuts": active_cuts,
            "purchased_before": list(purchased),
        })

        # Purchase best_edge and update contracted forest H
        purchased.append(best_edge)
        purchased_set.add(best_edge)
        eu, ev, _ = edges[best_edge]
        nu, nv = vertex_to_node(eu), vertex_to_node(ev)
        cu, cv = node_to_comp[nu], node_to_comp[nv]
        if cu != cv:
            h_edges.append((nu, nv))
        else:
            # Find unique path in H between nu and nv and contract all its nodes into one!
            k = len(nodes)
            adj: List[List[int]] = [[] for _ in range(k)]
            for a, b in h_edges:
                adj[a].append(b)
                adj[b].append(a)
            parent_bfs = {nu: -1}
            queue = [nu]
            while queue:
                cur = queue.pop(0)
                if cur == nv:
                    break
                for nxt in adj[cur]:
                    if nxt not in parent_bfs:
                        parent_bfs[nxt] = cur
                        queue.append(nxt)
            path_nodes = set()
            cur = nv
            while cur != -1:
                path_nodes.add(cur)
                cur = parent_bfs[cur]
            merged_verts = set()
            for nd in path_nodes:
                merged_verts |= nodes[nd]
            # Rebuild nodes & h_edges
            old_to_new: Dict[int, int] = {}
            new_nodes: List[Set[int]] = [merged_verts]
            for nd in path_nodes:
                old_to_new[nd] = 0
            for nd in range(k):
                if nd not in path_nodes:
                    old_to_new[nd] = len(new_nodes)
                    new_nodes.append(nodes[nd])
            new_h_edges = []
            for a, b in h_edges:
                na, nb = old_to_new[a], old_to_new[b]
                if na != nb:
                    new_h_edges.append((na, nb))
            nodes = new_nodes
            h_edges = new_h_edges

    # Step (S5): Reverse-delete redundant edges preserving 2-edge-connectivity
    final_F = list(purchased)
    for eid in reversed(purchased):
        cand = [x for x in final_F if x != eid]
        cand_uv = [(edges[x][0], edges[x][1]) for x in cand]
        if is_2_edge_connected(n, cand_uv):
            final_F = cand

    # Build exact per-iteration payment & dual-earning trace
    final_set = set(final_F)
    trace = []
    for snap in iter_snapshots:
        # Surviving augmentation A_t = edges in final_F not yet purchased before iteration t
        before_set = set(snap["purchased_before"])
        A_t = [eid for eid in final_F if eid not in before_set]
        # Payment rate = sum_{S, r in active_cuts} r * |A_t cap delta(S)|
        pay_rate = Fraction(0, 1)
        for S, r in snap["active_cuts"]:
            Sset = set(S)
            cnt = sum(1 for eid in A_t if (edges[eid][0] in Sset) != (edges[eid][1] in Sset))
            pay_rate += r * cnt
        # Dual earning rate: |L| + 2|I| + 2*beta*|C| (if disconnected) else |L|
        if snap["disconnected"]:
            earn_rate = Fraction(snap["L"] + 2 * snap["I"], 1) + 2 * beta * snap["C"]
        else:
            earn_rate = Fraction(snap["L"], 1)
        dt = snap["delta"]
        trace.append({
            "num_nodes": snap["num_nodes"],
            "kappa": snap["kappa"],
            "L": snap["L"],
            "I": snap["I"],
            "C": snap["C"],
            "delta": dt,
            "pay_step": pay_rate * dt,
            "earn_step": earn_rate * dt,
        })

    primal_cost = sum((edges[eid][2] for eid in final_F), Fraction(0, 1))
    dual_obj = 2 * sum(y_duals.values(), Fraction(0, 1)) - sum(z_duals, Fraction(0, 1))
    return {
        "final_F": sorted(final_F),
        "primal_cost": primal_cost,
        "y_duals": {S: val for S, val in sorted(y_duals.items()) if val > 0},
        "z_duals": z_duals,
        "dual_obj": dual_obj,
        "iterations": len(iter_snapshots),
        "trace": trace,
    }


def fmt_rat(q: Fraction) -> str:
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"
