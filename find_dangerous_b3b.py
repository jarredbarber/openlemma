import math

def get_base_digits(n, base):
    if n == 0: return [0]
    digits = []
    while n:
        digits.append(n % base)
        n //= base
    return digits

def dominates(val_q, val_k, p):
    dq = get_base_digits(val_q, p)
    dk = get_base_digits(val_k, p)
    for i in range(len(dk)):
        d_q_i = dq[i] if i < len(dq) else 0
        if d_q_i < dk[i]:
            return False
    return True

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5)+1, 2):
        if n % i == 0: return False
    return True

def is_k_smooth(m, k):
    d = 2
    temp = m
    while d * d <= temp:
        if temp % d == 0:
            if d > k: return False
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        if temp > k: return False
    return True

def solve():
    # Check k in range [7, 40]
    for k in range(7, 41):
        # Find divisors
        divs = []
        for i in range(1, int(k**0.5) + 1):
            if k % i == 0:
                divs.append(i)
                if i*i != k:
                    divs.append(k // i)
        divs.sort()
        proper_divs = [d for d in divs if d < k]
        
        found_any = False
        for s in proper_divs:
            # Search for prime q
            limit = 50000 
            
            for q in range(k + 1, limit):
                if not is_prime(q): continue
                
                n = s * q
                M = n // k
                
                # Filter: M must be k-smooth
                if not is_k_smooth(M, k):
                    continue
                
                # Check domination s*k' <= s*q
                val_k = k
                val_sq = n
                
                # Check all p <= k
                good = True
                temp = 2
                while temp <= k:
                    is_p = True
                    for i in range(2, int(temp**0.5)+1):
                        if temp % i == 0: is_p = False; break
                    if is_p:
                        if not dominates(val_sq, val_k, temp):
                            good = False
                            break
                    temp += 1
                
                if good:
                    # Check Large Primes
                    # Does any p in (k, M] divide C(n,k)?
                    # i.e. n % p < k
                    # Note: We already know M is smooth, so no p in (k, M] divides M.
                    # So p divides C(n,k) iff n % p < k.
                    
                    primes_large = []
                    # Get primes in (k, M]
                    # Actually we need p <= n/k. M approx n/k.
                    # Exception if minFac > n/k.
                    # If we find p in (k, n/k] with n % p < k, then minFac <= p <= n/k. Not exception.
                    
                    # Just report the candidate
                    print(f"DANGEROUS B3b: k={k}, s={s}, q={q}, n={n}, M={M}")
                    found_any = True
                    # Check if killed by Large Primes
                    killed = False
                    for p in range(k + 1, M + 2): # Check up to M+1 just in case
                        if is_prime(p):
                            if n % p < k:
                                #print(f"  (Killed by p={p})")
                                killed = True
                                break
                    if not killed:
                        print(f"  FATAL: Genuine Exception found!")
                    else:
                        print(f"  (Killed by Large Primes)")
                        
        if not found_any:
            pass #print(f"k={k}: No smooth Kummer-valid n found")

solve()
