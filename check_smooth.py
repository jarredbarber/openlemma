import math

def min_fac_choose(n, k):
    # Check primes <= n/k
    M = n // k
    limit = max(k, M)
    
    # Check primes <= limit
    # We want to find smallest prime factor of C(n,k).
    # If it is <= limit, return it.
    # Otherwise return something larger.
    
    # Actually, just compute minFac directly.
    # But C(n,k) is huge.
    # We only care if minFac <= limit.
    
    # Strategy: check divisibility by p for p <= limit.
    # p | C(n,k) <==> count_p(n!) > count_p(k!) + count_p((n-k)!)
    # or using Kummer: carry in base p addition k + (n-k)
    
    for p in range(2, limit + 1):
        if not is_prime(p): continue
        if kummer_check(n, k, p):
            return p
            
    return limit + 1 # Fail

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5)+1, 2):
        if n % i == 0: return False
    return True

def kummer_check(n, k, p):
    # Returns True if p | C(n,k)
    # Using Kummer's theorem: p | C(n,k) iff carry in k + (n-k) in base p
    # Equivalent to count_p(n) > count_p(k) + count_p(n-k)
    # Let's use the carry method: add k and n-k in base p
    a = k
    b = n - k
    carry = 0
    while a > 0 or b > 0 or carry > 0:
        sum_val = (a % p) + (b % p) + carry
        if sum_val >= p:
            return True
        carry = sum_val // p
        a //= p
        b //= p
    return False

def check_smooth_case(k_min, k_max, M_limit):
    for k in range(k_min, k_max + 1):
        # Generate k-smooth numbers M > k
        # We can use a recursive generator
        smooth_nums = []
        primes = [p for p in range(2, k + 1) if is_prime(p)]
        
        def generate(idx, current_val):
            if current_val > M_limit:
                return
            if current_val > k:
                smooth_nums.append(current_val)
            
            for i in range(idx, len(primes)):
                p = primes[i]
                next_val = current_val * p
                if next_val > M_limit:
                    break # Primes are sorted, so larger primes will also exceed
                generate(i, next_val)
                
        # The recursive generation might be slow if M_limit is large.
        # But M needs to be checked only for Type B (smooth).
        # We only care about M where all prime factors are <= k.
        generate(0, 1)
        smooth_nums.sort()
        
        print(f"Checking k={k}, {len(smooth_nums)} smooth numbers <= {M_limit}")
        
        for M in smooth_nums:
            # Check interval [k*M, k*M + k)
            start = k * M
            end = start + k
            for n in range(start, end):
                mf = min_fac_choose(n, k)
                if mf > M:
                    print(f"COUNTEREXAMPLE FOUND: k={k}, n={n}, M={M}, minFac={mf}")
                    return

check_smooth_case(29, 35, 1000000)
print("Done checking.")
