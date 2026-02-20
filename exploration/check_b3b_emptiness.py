import math

def get_base_digits(n, base):
    if n == 0: return [0]
    digits = []
    while n:
        digits.append(n % base)
        n //= base
    return digits

def dominates(a_val, b_val, p):
    # Check if digits of a_val <= digits of b_val in base p
    # Digits must assume infinite zeros for higher positions
    da = get_base_digits(a_val, p)
    db = get_base_digits(b_val, p)
    
    for i in range(len(da)):
        val_a = da[i]
        val_b = db[i] if i < len(db) else 0
        if val_a > val_b:
            return False
    return True

def solve():
    # Check k in range
    for k in range(29, 45):
        # Find divisors
        divs = []
        for i in range(1, int(k**0.5) + 1):
            if k % i == 0:
                divs.append(i)
                if i*i != k:
                    divs.append(k // i)
        divs.sort()
        
        # Check each divisor s
        # B3: s < k. So exclude s=k.
        proper_divs = [d for d in divs if d < k]
        
        for s in proper_divs:
            # Check if there is a prime p <= k blocking this s
            # Blocking means NO x in [1, p^L-1] coprime to p satisfies s*k' <= s*x
            
            # We need to consider all p <= k
            # If for some p, valid set is empty, then (s,k) is SAFE.
            
            is_safe = False
            
            k_prime = k // s
            
            # Iterate primes p <= k
            # Optimization: check small primes first (2, 3, 5)
            # as they impose strongest constraints?
            
            primes = []
            temp = 2
            while temp <= k:
                is_p = True
                for i in range(2, int(temp**0.5)+1):
                    if temp % i == 0: is_p = False; break
                if is_p: primes.append(temp)
                temp += 1
                
            blocking_prime = None
            
            for p in primes:
                # Length of s*k' in base p
                val_target = s * k_prime # This is k
                
                # We need x such that s*k' <= s*x (digitwise)
                # We only care about digits up to len(k)
                # But multiplication by s might carry.
                
                # Let's just bruteforce residues x mod p^L
                # What L?
                # The condition s*k' <= s*x must hold for all digits of s*k'.
                # Let L be number of digits of k in base p.
                
                L = len(get_base_digits(k, p))
                modulus = p ** L
                
                # Check if there exists x in [0, modulus-1]
                # such that x % p != 0 (coprime)
                # AND s*k' <= s*x (locally)
                
                # Note: "Locally" means digits of (s*x mod p^something) match?
                # No, s*q is the full number.
                # The lower L digits of s*q are determined by q mod p^L ?
                # Not exactly, carries from higher digits of q might flow in?
                # But q is huge.
                # q = A * p^L + x.
                # s*q = s*A*p^L + s*x.
                # s*x might overflow p^L.
                # The digits at 0..L-1 are determined by s*x mod p^L?
                # No. s*x can be larger than p^L.
                # The digits of s*q at 0..L-1 are exactly digits of s*x at 0..L-1 
                # PLUS potentially carries from s*A*p^L?
                # s*A*p^L has zeros at 0..L-1?
                # Yes, unless s has denominator p? No s is integer.
                # So digits 0..L-1 of s*q depend ONLY on s*x.
                # Wait. s*x might have length > L.
                # If s*x has digits beyond L-1, they sum with s*A*p^L.
                # But they don't affect digits 0..L-1.
                # So domination at 0..L-1 depends ONLY on x.
                
                # So we check x in [0, modulus-1].
                # Calculate s*x.
                # Check if digits(k)[i] <= digits(s*x)[i] for i in 0..L-1.
                
                valid_exists = False
                for x in range(modulus):
                    if x % p == 0: continue
                    
                    prod = s * x
                    d_prod = get_base_digits(prod, p)
                    d_k = get_base_digits(k, p)
                    
                    # Pad
                    while len(d_prod) < L: d_prod.append(0)
                    while len(d_k) < L: d_k.append(0)
                    
                    local_dom = True
                    for i in range(L):
                        if d_k[i] > d_prod[i]:
                            local_dom = False; break
                    if local_dom:
                        valid_exists = True
                        break
                
                if not valid_exists:
                    blocking_prime = p
                    is_safe = True
                    break
            
            if not is_safe:
                print(f"DANGER: k={k}, s={s} has solutions for all p <= k")
            #else:
                #print(f"Safe: k={k}, s={s} blocked by p={blocking_prime}")

solve()
