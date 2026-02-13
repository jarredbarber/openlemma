import math

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5)+1, 2):
        if n % i == 0: return False
    return True

def get_prime_factors(m):
    factors = set()
    d = 2
    temp = m
    while d * d <= temp:
        if temp % d == 0:
            factors.add(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return factors

def solve():
    # Check k in range
    for k in range(29, 45):
        print(f"Checking k={k}")
        # Generate k-smooth M
        # Limit M to reasonable size
        M_limit = 500
        
        primes = [p for p in range(2, k + 1) if is_prime(p)]
        
        smooth_nums = []
        def generate(idx, current):
            if current > M_limit: return
            if current > k: # M > k
                smooth_nums.append(current)
            for i in range(idx, len(primes)):
                p = primes[i]
                nxt = current * p
                if nxt > M_limit: break
                generate(i, nxt)
        
        generate(0, 1)
        smooth_nums.sort()
        
        for M in smooth_nums:
            # Check interval [kM, kM + k)
            start = k * M
            end = start + k
            
            for n in range(start, end):
                # Calculate C(n, k)
                # Compute directly
                binom = 1
                for i in range(k):
                    binom = binom * (n - i) // (i + 1)
                
                # Check Strong Hypothesis: gcd(binom, M) > 1
                common = gcd(binom, M)
                if common == 1:
                    print(f"Counterexample to Strong Hypothesis: k={k}, M={M}, n={n}")
                    print(f"  binom={binom}, factors of M={get_prime_factors(M)}")
                    
                    # Check Weak Hypothesis: exists p <= k dividing binom
                    # (This must be true if not exception)
                    has_small_prime = False
                    for p in range(2, k + 1):
                        if binom % p == 0:
                            has_small_prime = True
                            break
                    if not has_small_prime:
                        print(f"  FATAL: Exception found! minFac > k")
                    else:
                        print(f"  (But divisible by other p <= k)")
                    
                    return # Stop after first counterexample to read

solve()
