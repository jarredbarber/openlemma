def solve(n, k):
    print(f"Checking n={n}, k={k}")
    # Calculate binomial
    binom = 1
    for i in range(k):
        binom = binom * (n - i) // (i + 1)
        
    print(f"  C({n},{k}) = {binom}")
    
    # Check prime factors <= k
    divisors = []
    for p in range(2, k + 1):
        if binom % p == 0:
            divisors.append(p)
            
    print(f"  Divisible by primes <= {k}: {divisors}")
    
    # Trace Kummer for each p <= k
    # We want to know WHY.
    # p | C(n,k) <==> carry in base p for k + (n-k)
    
    for p in range(2, k + 1):
        # Check if p is prime
        is_p = True
        for i in range(2, p):
            if p % i == 0: is_p = False
        if not is_p: continue
        
        # Base p representation
        def to_base(num, base):
            if num == 0: return [0]
            digits = []
            while num:
                digits.append(num % base)
                num //= base
            return digits
            
        digits_k = to_base(k, p)
        digits_nk = to_base(n - k, p)
        digits_n = to_base(n, p)
        
        # Check carry
        # Align lengths
        l = max(len(digits_k), len(digits_nk))
        dk = digits_k + [0] * (l - len(digits_k))
        dnk = digits_nk + [0] * (l - len(digits_nk))
        
        carries = []
        c = 0
        for i in range(l):
            s = dk[i] + dnk[i] + c
            if s >= p:
                carries.append(i)
                c = 1
            else:
                c = 0
        
        if carries:
            print(f"    p={p}: Carries at positions {carries}")
            print(f"      k   (base {p}): {digits_k}")
            print(f"      n-k (base {p}): {digits_nk}")
            print(f"      n   (base {p}): {digits_n}")
        else:
            print(f"    p={p}: No carry")

print("--- Example 1: k=5, n=30 ---")
solve(30, 5)

print("\n--- Interval check for k=5, M=6 ---")
for i in range(5):
    solve(30 + i, 5)

print("\n--- Example 2: k=5, n=50 ---")
solve(50, 5)

print("\n--- Interval check for k=5, M=10 ---")
for i in range(5):
    solve(50 + i, 5)
