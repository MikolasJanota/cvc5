(set-logic UF)
(declare-sort S 0)
(declare-fun m (S S) S)
(declare-fun e () S)
(declare-fun i (S) S)

(assert (forall ((x S)(y S)(z S)) (= (m x (m y z)) (m (m x y) z))))
(assert (forall ((x S)(y S)) (= (m x e) x))) 
(assert (forall ((x S)(y S)) (= (m e x) x))) 
(assert (forall ((x S)) (= (m x (i x)) e)))
(assert (forall ((x S)) (= (m (i x) x) e)))

(declare-fun a () S)
(declare-fun b () S)

(assert (= (m a b) a))
(assert (not (= b e)))

(check-sat)
(exit)
