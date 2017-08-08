
isTimes : (x, i : Nat) -> Bool
isTimes Z _ = True
isTimes x i = case compare x i of
                   LT => False                 
                   EQ => True
                   GT => isTimes (minus x i) i

isPrime : Nat -> Bool
isPrime Z = False
isPrime (S Z) = False
isPrime (S (S Z)) = True
isPrime x = not $ any (isTimes x) [2..(minus x (S Z))]


prime_times_one : (p : Nat) -> isPrime p = True -> isTimes p (S Z) = True
prime_times_one n prf = rewrite prime_times_one n prf in Refl

prime_times_itself : (p : Nat) -> isPrime p = True -> isTimes p p = True
prime_times_itself p prf = rewrite prime_times_itself p prf in Refl


prime_is_prime : (p, n : Nat) -> isPrime p = True -> compare n (S Z) = GT -> compare p n = GT -> isTimes p n = False
prime_is_prime p n prf prf1 prf2 = rewrite prime_is_prime p n prf prf1 prf2 in Refl
