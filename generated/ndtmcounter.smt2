(define-fun R ((start Int) (counter Int) (state Int)) Bool (and (and (>= start 0) (>= counter 0) (>= state 0)) (or (or (or (and (or (and (= (mod (- start 1) 2) 0) (= (mod counter 2) 0) (= state 0)) (and (= start 0) (= (mod counter 2) 0) (= state 0))) (not (and (and (= start 1) (= counter 0) (= state 0)) (and (= start 0) (= counter 0) (= state 0))))) (and (or (and (= (mod (- start 1) 2) 0) (= counter 0) (= state 2)) (and (= start 0) (= counter 0) (= state 2))) (not (and (and (= start 1) (= counter 0) (= state 0)) (and (= start 0) (= counter 0) (= state 0)))))) (and (or (and (= (mod (- start 1) 2) 0) (= (mod (- counter 2) 2) 0) (= state 0)) (and (= start 0) (= (mod (- counter 2) 2) 0) (= state 0))) (not (and (and (= start 1) (= counter 0) (= state 0)) (and (= start 0) (= counter 0) (= state 0)))))) (or (or (and (= (mod (- start 2) 2) 0) (= (mod counter 2) 0) (= state 0) (= (mod start 2) (mod 0 2)) (= (mod counter 2) (mod 0 2)) (= (mod state 2) (mod 0 2))) (and (= (mod (- start 2) 2) 0) (= counter 0) (= state 2) (= (mod start 2) (mod 0 2)) (= (mod counter 2) (mod 0 2)) (= (mod state 2) (mod 0 2)))) (and (= (mod (- start 2) 2) 0) (= (mod (- counter 2) 2) 0) (= state 0) (= (mod start 2) (mod 0 2)) (= (mod counter 2) (mod 0 2)) (= (mod state 2) (mod 0 2)))))))

(assert
  (ramsey Int
    (start)
    (counter)
    (exists ((state Int)) (R start counter state))
  )
)
(check-sat)
