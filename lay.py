import networkx as nx
import matplotlib.pyplot as plt
import numpy as np
import math as m
import sympy as sp
import onion

"""
    Computes number of Hamiltonian paths in Lay(n, k).

    Author: Benjamin Keefer
    Version: December 20th, 2025
"""

# Computes the number of hamiltonian paths in a layer of an onion de Bruijn sequence
# If print_paths is True it will print those paths, otherwise it won't
def num_of_paths_greedy(start, end, print_paths) -> int:
    global num
    idx = 0
    all_paths = []
    
    visited = {}
    for edge in list(ldb.keys()):
        visited[edge] = False

    def dfs(current_path, current_vertex, print_paths):
        global num
        if current_vertex == end and len(current_path) == len(visited):
            if(print_paths):
                all_paths.append(current_path[:])
            num = num + 1
            return
        elif current_vertex == end:
            return
        visited[current_vertex] = True
        for neighbor in ldb[current_vertex]:
            if not visited[neighbor]:
                current_path.append(neighbor)
                dfs(current_path, neighbor, print_paths)
                current_path.pop()
        visited[current_vertex] = False
    
    dfs([start], start, print_paths)
    if(print_paths):
        for path in all_paths:
            print(path)
            if(idx % 2 == 1):
                print("=" * len(path) * 6)
            idx += 1
    return num

# Displays de Bruijn graph
def show_graph(s):
    global G
    G = nx.DiGraph()
    G.add_edges_from(s)
    try:
        nx.draw_planar(G, with_labels=True)
    except:
        nx.draw_spring(G, with_labels=True)
    plt.show()
    return

"""
Finds all hamiltonian cycles that exist in the layer of the de Bruijn graph
using brute force O(v!) algorithm.
"""
def find_hamiltonian_cycles() -> int:
    global sequence, ldb, n, k, num
    sequence = onion.lay(n, k)
    ldb = onion.lay_adj(n, k)
    start = str(k - 1)
    end = ""
    for i in range(n - 1):
        start += "0"
        end += "0"
    end += str(k - 1)

    num = 0
    paths = num_of_paths_greedy(start, end, False)
    print(f"Number of hamiltonian cycles in a ({n}, {k}) de Bruijn graph: " + str(paths))
    return paths

"""
Takes a Laplacian matrix, prints the factored characteristic polynomial,
and calculates its roots.
"""
def analyze_laplacian(laplacian_matrix):
    M = sp.Matrix(laplacian_matrix)
    lam = sp.symbols('λ')
    char_poly = M.charpoly(lam)
    print("--- Characteristic Polynomial ---\n")
    print(sp.factor(char_poly.as_expr()))
    roots = M.eigenvals()
    
    print("\n--- Roots (Eigenvalues) ---")
    for root in sorted(roots.keys(), key=lambda v: float(v.evalf())):
        multiplicity = roots[root]
        print(f"Value: {root} (Multiplicity: {multiplicity})")

# Computes number of hamiltonian paths in Lay(n, k) in polynomial time
def number_of_hamiltonian_paths():
    print("-" * 30)
    global sequence, G, n
    vertices = set()
    for key, value in ldb.items():
        vertices.add(key)
        for v in value:
            vertices.add(v)
    vertices = list(vertices)

    print("Vertices:")
    print(vertices)
    l_v = len(vertices)
    l = (l_v * (4 + n))

    adj = [[0 for _ in range(l_v)] for _ in range(l_v)]
    deg = [[0 for _ in range(l_v)] for _ in range(l_v)]
    degrees = {}
    for v in vertices:
        degrees[v] = 0

    # Populates adjacency matric and degree dictionary
    for edge in sequence:
        adj[vertices.index(edge[0])][vertices.index(edge[1])] = 1
        degrees[edge[1]] = degrees[edge[1]] + 1

    i = 0
    for v in vertices:
        deg[i][i] = degrees[v]
        i += 1

    # Constructs Laplacian matrix
    laplacian = [[(deg[i][j] - adj[i][j]) for j in range(l_v)] for i in range(l_v)]

    print("Laplacian matrix:")

    for row in laplacian:
            print(row)

    print("Analyzing the Laplacian matrix:")
    analyze_laplacian(laplacian)

    sub_arrays = produce_sub_matrices(laplacian)

    # Computes and prints number of arborescences for each vertex in the Line(Lay(n, k))
    # This is the left side of the BEST theorem equation
    dets = []
    print(f"Number of arborescences in Root(Lay({n}, {k})): {round(np.linalg.det(np.array(sub_arrays[0])))}")
    eigenvals = np.linalg.eigvals(np.array(laplacian))
    total = 1
    num_of_vals = 0
    for e in eigenvals:
        if e > 0.0001:
            total *= e
            # print(e)
        num_of_vals += 1

    dets.append(np.linalg.det(np.array(sub_arrays[0])))
        
    # Computes the right side of the BEST theorem equation
    degree_product = 1
    for v in vertices:
        degree_product *= m.factorial(degrees[v] - 1)

    if not (dets[0] % 1 > 0.999 or dets[0] % 1 < 0.001):
        print(dets[0])
        print(dets[0] % 1)
        raise Exception("Determinant computation has floating point value so number of paths computation can't be relied on!")
    else:
        dets[0] = round(dets[0])

    num_of_paths = dets[0] * degree_product

    try:
        assert(num_of_paths == (((m.factorial(k))**((k**(n-1))-((k-1)**(n-1))))) / (k**(n-1)))
    except:
        print(f"Expected: {int(((m.factorial(k))**((k**(n-1))-((k-1)**(n-1))))) / (k**(n-1))}")

    print(f"Number of Eulerian cycles: {num_of_paths}")

    if num_of_paths > 0 and int(m.log10(num_of_paths)+1) > 6:
        print(f"or\napproximately {num_of_paths / (10 ** int(m.log10(num_of_paths))):.1f}e+{int(m.log10(num_of_paths))}")
    return
    
# Generates all sub arrays where the ith row and ith column are removed
def produce_sub_matrices(arr) -> list:
    sub = []
    for i in range(len(arr)):
        sub_arr = []
        for j in range(0, i):
            x = []
            for s in range(0, i):
                x.append(arr[j][s])
            for s in range(i + 1, len(arr)):
                x.append(arr[j][s])
            sub_arr.append(x)
        for j in range(i + 1, len(arr)):
            x = []
            for s in range(0, i):
                x.append(arr[j][s])
            for s in range(i + 1, len(arr)):
                x.append(arr[j][s])
            sub_arr.append(x)
        sub.append(sub_arr)
    return sub

"""
Displays and prints the number of Hamiltonian cycles in Lay(n, k)
by computing the number of Eulerian cycles in its root graph G(n, k).
"""
def compute_paths(n, k):
    global sequence, ldb
    sequence = onion.g(n, k)
    ldb = onion.g_adj(n, k)
    number_of_hamiltonian_paths()
    # Uncomment to confirm number of hamiltonian cycles using brute force
    # find_hamiltonian_cycles()

# Displays layers of De Bruijn graphs and information about them.
def main():
    global n, k
    for n in range(2, 5):
        for k in range(2, 4):
            compute_paths(n, k)
            show_graph(onion.lay(n, k))
    return

if __name__ == "__main__":
    main()
