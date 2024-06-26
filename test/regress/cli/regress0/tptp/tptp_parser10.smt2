(set-logic ALL)
(set-info :status unsat)
(declare-sort $$unsorted 0)
(declare-fun tptp.e ($$unsorted) $$unsorted)
(assert (forall ((A $$unsorted) (B $$unsorted)) (=> (not (= A B)) (not (= (tptp.e A) (tptp.e B))))))
(declare-fun $$rtu (Real) $$unsorted)
(declare-fun $$utr ($$unsorted) Real)
(assert (= (/ 8 5) ($$utr ($$rtu (/ 8 5)))))
(assert (let ((_let_1 (to_real 1))) (= _let_1 ($$utr ($$rtu _let_1)))))
(assert (not (not (= (tptp.e ($$rtu (/ 8 5))) (tptp.e ($$rtu (to_real 1)))))))
(set-info :filename tptp_parser10)
(check-sat-assuming ( true ))
