import numpy as np
import math
from collections import defaultdict
import onion
"""
Shows that H(n, k) and G(n, k) have some number of Eulerian cycles.
"""

"""
Removes Degree 1 vertices by merging edges.
"""
def simplify_graph_edges(edges: list[tuple[any, any]]) -> list[tuple[any, any]]:
    adj = defaultdict(list)
    in_degree, out_degree = defaultdict(int), defaultdict(int)
    all_nodes = set()
    
    for u, v in edges:
        adj[u].append(v); out_degree[u] += 1; in_degree[v] += 1
        all_nodes.add(u); all_nodes.add(v)

    removable = {n for n in all_nodes if in_degree[n] == 1 and out_degree[n] == 1}
    simplified_edges = []

    for u, v in edges:
        if u in removable: continue
        curr = v
        visited = {u}
        while curr in removable:
            if curr in visited: 
                curr = None
                break
            visited.add(curr)
            curr = adj[curr][0] if adj[curr] else None
        if curr is not None:
            simplified_edges.append((u, curr))
    return simplified_edges

def count_eulerian_cycles(edges):
    if not edges: return 0
    nodes = sorted(list(set([n for e in edges for n in e])))
    node_map = {node: i for i, node in enumerate(nodes)}
    n = len(nodes)
    
    # 1. Build Laplacian Matrix
    L = np.zeros((n, n))
    A = np.zeros((n, n))
    out_degrees = defaultdict(int)
    for u, v in edges:
        L[node_map[u], node_map[u]] += 1
        L[node_map[u], node_map[v]] -= 1
        A[node_map[u], node_map[v]] += 1
        out_degrees[u] += 1

    
    if n == 3 ** 2:
        print(f"Adjancency matrix of G(3, 3):")
    else:
        print(f"Adjancency matrix of H(3, 3):")

    print(A)

    if n == 3 ** 2:
        print("Laplacian(G(3, 3)):")
    else:
        print("Laplacian(H(3, 3))")
    print(L)

    # 2. Compute Arborescences using Eigenvalues
    if n > 1:
        eigvals = np.linalg.eigvals(L)
        non_zero_evals = [round(ev.real) for ev in eigvals if abs(ev) > 1e-10]
        
        print("Non-zero eigenvalues:")
        print(non_zero_evals)
        print(f"Number of eigenvalues is {n}")

        t_w = (1/n) * np.prod(non_zero_evals)
        num_arborescences = round(abs(t_w))
    else:
        num_arborescences = 1


    # Degree Product part of BEST Theorem
    deg_fact_prod = 1
    for node in nodes:
        if out_degrees[node] > 0:
            deg_fact_prod *= math.factorial(out_degrees[node] - 1)
            
    return num_arborescences * deg_fact_prod

G = onion.g(3, 3)
H = simplify_graph_edges(G)

print(f"Number of Eulerian cycles in G(3, 3): {count_eulerian_cycles(G)}")
print(f"Number of Eulerian cycles in H(3, 3): {count_eulerian_cycles(H)}")
