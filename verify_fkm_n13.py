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

if __name__ == '__main__':
    # Tests n=12, k=2
    # For n=12, k=2: k^n = 4096 (very fast computationally, easy to validate)
    #perform_validation(12, 3)
    # We can also test n=13, k=2
    #perform_validation(13, 3)
    # and maybe n=8, k=3
    #perform_validation(8, 3)
