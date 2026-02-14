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

def solve():
    # Check k in range [7, 20]
    for k in range(7, 21):
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
            # q must be > k (roughly)
            # Limit search
            limit = 100000
            
            # Optimization: q must satisfy constraints
            # We can iterate, but let's just brute force for small k
            
            for q in range(k + 1, limit):
                if not is_prime(q): continue
                
                # Check domination s*k' <= s*q
                val_k = k
                val_sq = s * q
                
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
                    print(f"Exception found: k={k}, s={s}, q={q}")
                    found_any = True
                    break
        
        if not found_any:
            print(f"k={k}: No exceptions found (s < k)")

solve()
