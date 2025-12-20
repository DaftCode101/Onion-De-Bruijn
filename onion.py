"""
Code for getting layers of Onion De Bruijn graphs as well
as their root graphs.

Author: Benjamin Keefer
Verstion: December 20th, 2025
"""

# De Bruijn generation code from amirrubin87 on github
def val(s):
    n = len(s)
    return sum([s[- i] * (k ** (i - 1)) for i in range(1, n + 1)])
def val_star(s):
    n = len(s)
    return max([val(s[i:] + s[:i]) for i in range(n)])
def rotate_zeros(s):
    return s if s[0]!=0 else rotate_zeros(s[1:]+s[:1])
def a_dagger(s):
    return s[-1] != 0 and val_star(s)==val(rotate_zeros(s))
def shift(s):
    x = s[:-1]
    sigma = s[-1]
    if sigma < (k - 1) and a_dagger(x + [sigma + 1]):
        return [sigma + 1] + x
    elif a_dagger(x + [sigma]):
        return [0] + x
    else:
        return [sigma] + x
def de_bruijn(k_val: int, n_val: int):
    global k
    global n
    k = k_val
    n = n_val
    s = [0 for _ in range(n)]
    for i in range(k ** n):
        sequence.append(s)
        s = shift(s)

# Extends the alphabet beyond 0-9
def char(x : int):
    if x < 10:
        return str(x)
    elif x < 36:
        return str(chr(x + 87))
    elif x < 62:
        return str(chr(x + 29))
    return str(chr(x + 113))

# Generates edge pairs from the de Bruijn sequence
def load_edges():
    global edges
    global sequence
    edges = []
    for word in sequence:
        for other_word in sequence:
            add = True
            for i in range(len(other_word) - 1):
                if(word[i] != other_word[i+1]):
                    add = False
            if(add):
                edges.append(("".join(char(num) for num in word), "".join(char(num) for num in other_word)))
    sequence = edges

# Updates sequence to only contain a single layer of the "onion"
def layer(x : int):
    global sequence
    sub_seq = []
    for word in sequence:
        in_word = False
        for num in word:
            if(num == x):
                in_word = True
        if(in_word):
            sub_seq.append(word)
    sequence = sub_seq

# Removes edges that start or end with 0^(n) because they're not needed for lay computation
def remove_zero_edges() -> list:
    global sequence
    removed = []
    zero = ""
    for i in range(n):
        zero += str(0)

    for word in edges:
        if not (word[0] == zero or word[1] == zero):
            removed.append(word)

    sequence = removed
    return removed

# Converts list of graph edges into a dictionary of adjacency lists
def adjacency_lists():
    global sequence, ldb
    ldb.clear()
    for edge in sequence:
        if edge[0] not in ldb:
            ldb[edge[0]] = [edge[1]]
        else:
            ldb[edge[0]].append(edge[1])

# Removes duplicate edges from a graph
def unique(graph, swap) -> list:
    new_sequence = []
    s = set()

    for seq in graph:
        if not s.__contains__(seq):
            s.add(seq)
            new_sequence.append(seq)

    if swap:
        global sequence
        sequence = new_sequence

    return new_sequence

"""
Constructs the Root Graph of LDB(n, k) where LDB(n, k) = ldb is
a dictionary that maps each vertex in LDB(n, k) to a list of all
vertices that it has an edge going out to.

Returns G(n, k) as a set of edges.
"""
def key() -> set:
    key = set()
    labeled_vertices = dict()
    pk = 0 # arbitrary use of primary key to label vertices

    for neighborhood in ldb.items():
        vertex = neighborhood[0]

        # Labels current vertex if it has not been labeled yet  
        if not labeled_vertices.__contains__(vertex):
            labeled_vertices[vertex] = str(pk)
            pk += 1
        
        # Labels the adjacent vertices if they have not been labeled yet
        pk_used = False
        for adjacent_vertex in neighborhood[1]:
            if not labeled_vertices.__contains__(adjacent_vertex):
                labeled_vertices[adjacent_vertex] = pk
                pk_used = True

        """
        Adds an edge between the current vertex and the 
        vertex of the last-labeled adjacent vertex.
        """
        key.add((str(labeled_vertices[vertex]),\
                 str(labeled_vertices[adjacent_vertex])))

        # Increments labeling key
        if pk_used:
            pk += 1

    # Returns Key(LDB(n, k)) represented as a set of edges.
    return key

def reset_state():
    global edges, ldb, vertices, sequence
    global startTime, endTime, num
    edges = []
    sequence = []
    ldb = {}
    vertices = []
    startTime = 0
    endTime = 0
    num = 0

# Return list of edges in Lay(n, k)
def lay(n, k) -> list:
    reset_state()
    de_bruijn(k, n)
    layer(k-1)
    load_edges()
    remove_zero_edges()
    unique(sequence, True)
    return sequence

# Return adjacency representation of Lay(n, k)
def lay_adj(n, k) -> dict:
    global ldb
    lay(n, k)
    adjacency_lists()
    return ldb

# Return list of edges in G(n, k), the root graph of Lay(n, k)
def g(n, k) -> list:
    lay_adj(n, k)
    return list(key())

# Return adjacency representation of G(n, k)
def g_adj(n, k) -> dict:
    global sequence, ldb
    g(n, k)
    sequence = key()
    adjacency_lists()
    return ldb
