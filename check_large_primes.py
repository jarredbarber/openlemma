import math

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, int(n**0.5)+1, 2):
        if n % i == 0: return False
    return True

def get_primes_in_range(start, end):
    return [p for p in range(start + 1, end + 1) if is_prime(p)]

def check_large_primes_sufficiency(k_start, k_end):
    for k in range(k_start, k_end + 1):
        print(f"Checking k={k}")
        primes_large = get_primes_in_range(k, 2 * k)
        
        # Generate k-smooth M
        M_limit = 10000
        primes_small = [p for p in range(2, k + 1) if is_prime(p)]
        
        smooth_nums = []
        def generate(idx, current):
            if current > M_limit: return
            if current >= 2 * k: # M >= 2k (Case B1)
                smooth_nums.append(current)
            for i in range(idx, len(primes_small)):
                p = primes_small[i]
                nxt = current * p
                if nxt > M_limit: break
                generate(i, nxt)
        
        generate(0, 1)
        smooth_nums.sort()
        
        survivor_count = 0
        
        for M in smooth_nums:
            # Check interval [kM, kM + k)
            start = k * M
            end = start + k
            
            # For each n in interval, is it killed by large primes?
            # Killed if EXISTS p in (k, 2k] such that n mod p < k.
            # Survives if FOR ALL p in (k, 2k], n mod p >= k.
            
            # If ANY n in interval survives, we report it.
            # This n requires Kummer to kill it.
            
            interval_survivors = []
            for n in range(start, end):
                survives = True
                for p in primes_large:
                    if n % p < k: # Killed by p (p divides C(n,k))
                        survives = False
                        break
                if survives:
                    interval_survivors.append(n)
            
            if interval_survivors:
                #print(f"  M={M}: Survivors {interval_survivors}")
                survivor_count += 1
                
        print(f"  k={k}: {survivor_count} intervals with Large Prime survivors (out of {len(smooth_nums)})")
        if survivor_count == 0:
            print(f"  SUCCESS! Large Primes kill ALL Type B exceptions for k={k} (up to M={M_limit})")

check_large_primes_sufficiency(29, 40)
