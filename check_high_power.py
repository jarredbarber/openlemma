import math

def get_primes(n):
    primes = []
    is_prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if is_prime[p]:
            primes.append(p)
            for i in range(p * p, n + 1, p):
                is_prime[i] = False
    return primes

def get_lcm_valuation(k, p):
    # Returns v_p(lcm(1..k)) = floor(log_p k)
    return int(math.floor(math.log(k, p)))

def get_valuation(n, p):
    v = 0
    while n > 0 and n % p == 0:
        v += 1
        n //= p
    return v

def solve_constraints(k):
    print(f"Checking k={k}")
    primes = get_primes(k)
    
    # We need M > k such that for all p <= k:
    # v_p(k*M) <= floor(log_p k)
    # v_p(M) + v_p(k) <= floor(log_p k)
    # v_p(M) <= floor(log_p k) - v_p(k)
    
    # Construct possible M values
    # M = product p^e_p
    # where 0 <= e_p <= max_e_p
    
    max_exponents = {}
    for p in primes:
        vp_k = get_valuation(k, p)
        max_vp_M = get_lcm_valuation(k, p) - vp_k
        max_exponents[p] = max_vp_M
        
    # If any max_vp_M < 0, then NO solutions (impossible since vp_k <= log_p k)
    
    # Generate all M
    # This could be large?
    # log M <= sum (log_p k - v_p(k)) log p = log(lcm) - log k
    # M <= lcm(1..k) / k
    # For k=29, lcm is huge. 
    # But wait!
    # For p > k/2, max_vp_M = 1 - 1 = 0 (if p|k) or 1 - 0 = 1 (if p not|k)
    # But wait, if p not|k, p > k/2 => 2p > k => floor(log_p k) = 1.
    # So max_vp_M is 0 or 1 for large primes.
    
    # We are looking for EXCEPTIONS.
    # An exception (n, k) in Type B must have M satisfying this.
    # AND M must survive the CRT sieve.
    
    # Let's generate M values via backtracking, but apply CRT sieve ON THE FLY.
    # We don't need to generate M if it already fails CRT.
    
    # Actually, M determines the interval [kM, kM+k).
    # We need to find if there is ANY n in this interval satisfying digit domination.
    
    # Algorithm:
    # 1. Iterate p from small to large.
    # 2. Maintain a set of valid residues for M modulo (product p_i^something).
    #    Actually, M is fixed mod p^e.
    #    For a fixed p, we iterate possible e_p in [0, max_exponents[p]].
    #    For each choice, M has a valuation v_p(M) = e_p.
    #    This determines the "trailing zeros" of kM in base p.
    #    Does this allow k \preceq_p (kM+j) for some j?
    #    We check if there exists j in [0, k-1] such that k \preceq_p (k * p^e_p * residue + j)?
    #    Wait, M is just p^e_p * (something coprime).
    #    kM = k * p^e_p * M'.
    #    In base p, kM has e_p + v_p(k) zeros?
    #    No, v_p(kM) = e_p + v_p(k).
    #    Let V = v_p(kM).
    #    If V > log_p k, impossible. (High Power Lemma).
    #    We are only considering V <= log_p k.
    #    So kM has V zeros.
    #    k has V' = v_p(k) zeros? No, k might not end in zeros.
    #    But kM is a multiple of k.
    
    #    Let's just generate M and check.
    #    Since M can be large, we prioritize small primes?
    #    Actually, for k=29, M can be ~ e^29 / 29. Too big.
    #    But we have the Large Prime constraint too!
    #    For p in (k, M], n mod p >= k.
    #    This requires M to be such that we can satisfy this.
    #    
    #    Let's check the number of valid M for small k first.
    
    count = 0
    
    def generate(idx, current_M):
        nonlocal count
        if idx == len(primes):
            if current_M > k:
                # Check this M
                check_M(k, current_M)
                count += 1
            return

        p = primes[idx]
        limit = max_exponents[p]
        
        # Optimization: if current_M is already huge, stop?
        # No, we need to be exhaustive for the "Low Power" case.
        # But for k=29, this is impossible to enumerate.
        
        # Is there a constraint on M from the FACT that it is Type B?
        # Yes, M is k-smooth. (By construction).
        
        # We need another filter.
        # The High Power lemma kills almost everything.
        # The survivors are divisors of LCM/k.
        
        # Let's count how many survivors for k=10.
        
        p_pow = 1
        for e in range(limit + 1):
            generate(idx + 1, current_M * p_pow)
            p_pow *= p

    if k > 15:
        print(f"Skipping exhaustive generation for k={k} (too large)")
        # Just compute the number of divisors
        total_divs = 1
        for p in primes:
            total_divs *= (max_exponents[p] + 1)
        print(f"Total candidates M (divisors of LCM/k): {total_divs}")
        return

    generate(0, 1)

def check_M(k, M):
    # Check if there is n in [kM, kM+k) satisfying all constraints
    # 1. k <=p n for all p <= k
    # 2. n mod q >= k for all q in (k, M]
    #    (If M is smooth, q in (k, M] implies q does not divide M)
    
    start = k * M
    end = start + k
    
    # Filter by small primes first
    possible_ns = []
    for n in range(start, end):
        good = True
        for p in range(2, k + 1):
            if not is_prime(p): continue
            if not kummer_divides(n, k, p): # k <=p n means NOT divisible
                # If kummer_divides is True (p | C(n,k)), then NOT exception.
                # We want EXCEPTION. So we want p NOT dividing.
                # So we want kummer_check(n, k, p) to be False.
                pass
            else:
                good = False; break
        if good:
            possible_ns.append(n)
            
    if not possible_ns:
        return # No candidates
        
    # Filter by large primes
    # q in (k, M]
    # M is k-smooth, so no q divides M.
    # Check q in range
    
    # Generating primes in (k, M] might be slow if M is large.
    # But here M is bounded by LCM/k.
    
    for n in possible_ns:
        # Check large primes
        is_exception = True
        # Check primes from k+1 to M
        # Optimization: check p|C(n,k) directly?
        # p | C(n,k) <==> n mod p < k
        # We need n mod p >= k for all p in (k, n/k]
        # Here n/k approx M.
        
        # We can iterate p.
        for p in range(k + 1, n // k + 1):
             if is_prime(p):
                 if n % p < k: # p divides C(n,k)
                     is_exception = False
                     break
        
        if is_exception:
            print(f"EXCEPTION FOUND: k={k}, M={M}, n={n}")

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5)+1, 2):
        if n % i == 0: return False
    return True

def kummer_divides(n, k, p):
    # Returns True if p | C(n,k) (i.e. carry exists)
    a = k
    b = n - k
    carry = 0
    while a > 0 or b > 0 or carry > 0:
        val = (a % p) + (b % p) + carry
        if val >= p: return True
        carry = val // p
        a //= p; b //= p
    return False

# Check for small k
for k in range(2, 13):
    solve_constraints(k)
