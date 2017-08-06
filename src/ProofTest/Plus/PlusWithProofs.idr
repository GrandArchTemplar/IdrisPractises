pls : Nat -> Nat -> Nat
pls Z y = y
pls (S x) y = S $ pls x y



pls_left_neu_elem : (n : Nat) -> n = pls Z n
pls_left_neu_elem n = Refl


pls_right_neu_elem : (n : Nat) -> n = pls n Z
pls_right_neu_elem Z = Refl
pls_right_neu_elem (S k) = let rec = pls_right_neu_elem k in 
                               rewrite rec in Refl

pls_left_right_neus_eq : (n : Nat) -> pls n Z = pls Z n
pls_left_right_neus_eq Z = Refl
pls_left_right_neus_eq (S k) = let rec = pls_left_right_neus_eq k in 
                                   rewrite rec in Refl

pls_uniq_neu : (n, k : Nat) -> pls n k = n -> k = Z
pls_uniq_neu Z k prf = prf
pls_uniq_neu (S j) k prf = let rec = pls_uniq_neu (S j) k prf in 
                               rewrite rec in Refl
