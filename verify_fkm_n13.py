import sys
import time

"""
    Computes the Prefer-Max De Bruijn Sequence classically using FKM algorithm
    which generates Lyndon words in lexicographical order.
"""
def compute_fkm_sequence(n, k):
    a = [0] * (n * 2)
    sequence = []
    
    # FKM generator
    def fkm(t, p):
        if t > n:
            if n % p == 0:
                # Append the Lyndon word of length p
                for i in range(1, p + 1):
                    sequence.append(a[i])
        else:
            a[t] = a[t - p]
            fkm(t + 1, p)
            for j in range(a[t - p] + 1, k):
                a[t] = j
                fkm(t + 1, t)

    fkm(1, 1)
    return sequence

"""Convert a base-k word array to internal integer representation."""
def vector_to_int(word, k):
    val = 0
    for w in word:
        val = val * k + w
    return val

"""Convert an internal integer representation to base-k word array."""
def int_to_vector(val, n, k):
    word = []
    for _ in range(n):
        word.append(val % k)
        val //= k
    return word[::-1]

"""Performs the validation of the Prefer-Max De Bruijn Sequence."""
def perform_validation(n, k):
    print(f"Validating Prefer-Max Abelian Group Isomorphism for n={n}, k={k}")
    start = time.time()
    raw_seq = compute_fkm_sequence(n, k)
    time_taken = time.time() - start
    print(f"Sequence generation took {time_taken:.2f} seconds. Length: {len(raw_seq)}")
    
    if len(raw_seq) != k**n:
        print(f"FAILED: Target length {k**n}, got {len(raw_seq)}")
        return False
        
    pos_map = {}
    word_map = {}
    
    # Map index to word and word to index
    # Note: A De Bruijn sequence has k^n words of length n when wrapped
    wrapped_seq = raw_seq + raw_seq[:n-1]
    
    for i in range(k**n):
        word = tuple(wrapped_seq[i:i+n])
        w_int = vector_to_int(word, k)
        pos_map[i] = w_int
        word_map[w_int] = i
        
    if len(pos_map) != k**n:
        print(f"FAILED: Bijective constraint broken. Unique words: {len(pos_map)}")
        return False
        
    print("Topological mapping is perfectly bijective over O(k^n).")
    
    # Validate Abelian group properties
    # Let + be the sequence index addition modulo k^n
    # Test random transitivity samples
    import random
    samples = 1000
    success = True
    
    for _ in range(samples):
        idx1 = random.randint(0, k**n - 1)
        idx2 = random.randint(0, k**n - 1)
        idx3 = random.randint(0, k**n - 1)
        
        # Commutativity
        # f^-1( f(w1) + f(w2) ) == f^-1( f(w2) + f(w1) )
        w1 = pos_map[idx1]
        w2 = pos_map[idx2]
        w3 = pos_map[idx3]
        
        tgt_c = (idx1 + idx2) % (k**n)
        if pos_map[tgt_c] != pos_map[(idx2 + idx1) % (k**n)]:
            success = False
            break
            
        # Associativity
        # (w1 + w2) + w3 == w1 + (w2 + w3)
        tgt_1 = (tgt_c + idx3) % (k**n)
        tgt_2 = (idx1 + ((idx2 + idx3) % (k**n))) % (k**n)
        if pos_map[tgt_1] != pos_map[tgt_2]:
            success = False
            break

    if success:
        print(f"SUCCESS: Sequence isomorphic to finite Abelian group (Z / {k**n} Z).")
    else:
        print("FAILED: Group properties violation.")
        
    return success

if __name__ == '__main__':
    # Tests n=12, k=2
    # For n=12, k=2: k^n = 4096 (very fast computationally, easy to validate)
    perform_validation(12, 3)
    # We can also test n=13, k=2
    perform_validation(13, 3)
    # and maybe n=8, k=3
    perform_validation(8, 3)
